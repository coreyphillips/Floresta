// SPDX-License-Identifier: MIT OR Apache-2.0
//! Confirmed history for explicitly registered public scripts and outpoints.
//! The cursor and its block's matches are committed in the same database batch.
//! No Electrum client can register a watch or read this index.

mod confirmed;

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::io::{self, BufRead, Read, Write};
use std::path::Path;
use std::str::FromStr;
use std::sync::{Arc, Mutex};
use std::time::Duration;

use bitcoin::blockdata::constants::genesis_block;
use bitcoin::consensus::encode::{serialize, serialize_hex};
use bitcoin::{Block, BlockHash, Network, OutPoint, ScriptBuf, Transaction, Txid, Wtxid};
use floresta_chain::pruned_utreexo::BlockchainInterface;
use floresta_watch_only::merkle::MerkleProof;
use floresta_wire::node_interface::NodeInterface;
use miniscript::descriptor::Wildcard;
use miniscript::{Descriptor, DescriptorPublicKey, ForEachKey};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use tokio::sync::RwLock;

const LIMIT: usize = 65536;
type Result<T> = std::result::Result<T, &'static str>;
type Cursor = (u32, BlockHash);

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct PublicRange {
    descriptor: String,
    range: [u32; 2],
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Command {
    id: u32,
    action: String,
    owner: String,
    #[serde(default)]
    scripts: Vec<String>,
    #[serde(default)]
    descriptors: Vec<PublicRange>,
    #[serde(default)]
    outpoints: Vec<OutPoint>,
    #[serde(default)]
    txid: Option<Txid>,
    #[serde(default)]
    offset: Option<u32>,
    #[serde(default)]
    query: Option<confirmed::Query>,
}

#[derive(Clone, Default, Serialize, Deserialize)]
struct Watches {
    scripts: BTreeSet<ScriptBuf>,
    #[serde(default)]
    through: BTreeMap<String, u32>,
    outpoints: BTreeSet<OutPoint>,
}

impl Watches {
    fn extend_descriptor(&mut self, item: PublicRange, network: Network) -> Result<bool> {
        let [start, end] = item.range;
        if start > end || end >= (1 << 31) || end - start >= 256 || item.descriptor.len() > 512 {
            return Err("Invalid public descriptor range.");
        }
        let desc = Descriptor::<DescriptorPublicKey>::from_str(&item.descriptor)
            .map_err(|_| "Invalid public descriptor.")?;
        if !desc.has_wildcard()
            || !desc.for_each_key(|key| {
                matches!(key, DescriptorPublicKey::XPub(x)
            if x.wildcard == Wildcard::Unhardened && x.xkey.network == network.into()
            && x.derivation_path.into_iter().all(|child| !child.is_hardened()))
            })
        {
            return Err("Invalid public descriptor network or branch.");
        }
        let canonical = desc.to_string();
        let next = self.through.get(&canonical).map_or(0, |n| n + 1);
        if start > next {
            return Err("Public descriptor range has a gap.");
        }
        if next > end {
            return Ok(false);
        }
        let secp = bitcoin::secp256k1::Secp256k1::verification_only();
        for index in next..=end {
            let definite = desc
                .at_derivation_index(index)
                .map_err(|_| "Invalid derivation index.")?;
            let script = definite
                .derived_descriptor(&secp)
                .map_err(|_| "Public derivation failed.")?
                .script_pubkey();
            self.scripts.insert(script);
        }
        self.through.insert(canonical, end);
        Ok(true)
    }
}

struct Owner {
    watches: Watches,
    tree: sled::Tree,
    cursor: Option<Cursor>,
    parent_cursor: Option<Cursor>,
    unavailable: bool,
    matched: u64,
}

struct Registry {
    db: sled::Db,
    owners: BTreeMap<String, Owner>,
}

fn storage<T>(_: T) -> &'static str {
    "Managed watch storage is unavailable."
}

fn owner_id(s: &str) -> bool {
    s.len() == 64
        && s.bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}

impl Registry {
    fn open(path: &Path) -> Result<Self> {
        let db = sled::open(path).map_err(storage)?;
        let mut owners = BTreeMap::new();
        for entry in db.iter() {
            let (key, _) = entry.map_err(storage)?;
            let id = std::str::from_utf8(&key).map_err(storage)?;
            if !owner_id(id) {
                return Err("Invalid managed watch owner.");
            }
            let tree = db.open_tree(id).map_err(storage)?;
            let watches = tree
                .get(b"watches")
                .map_err(storage)?
                .ok_or("Missing watch registration.")?;
            let watches = serde_json::from_slice(&watches).map_err(storage)?;
            let cursor = tree
                .get(b"cursor")
                .map_err(storage)?
                .map(|v| serde_json::from_slice(&v))
                .transpose()
                .map_err(storage)?;
            let matched = tree
                .get(b"matches")
                .map_err(storage)?
                .map(|v| serde_json::from_slice(&v))
                .transpose()
                .map_err(storage)?
                .unwrap_or(0);
            let parent_cursor = tree
                .get(b"parent-cursor")
                .map_err(storage)?
                .map(|v| serde_json::from_slice(&v))
                .transpose()
                .map_err(storage)?;
            let version = tree.get(b"proof-format").map_err(storage)?;
            let mut owner = Owner {
                watches,
                tree,
                cursor,
                parent_cursor,
                matched,
                unavailable: false,
            };
            match version.as_deref() {
                Some(b"2") => (),
                Some(b"1") | None => owner.reset_to(owner.watches.clone())?,
                _ => return Err("Unsupported managed proof index format."),
            }
            owners.insert(id.to_string(), owner);
        }
        Ok(Self { db, owners })
    }

    fn command(
        &mut self,
        request: Command,
        network: Network,
        chain: &impl BlockchainInterface,
    ) -> Result<Value> {
        if !owner_id(&request.owner) {
            return Err("Invalid watch owner.");
        }
        if let Some(query) = request.query {
            if request.action != "confirmed"
                || request.txid.is_some()
                || request.offset.is_some()
                || !request.scripts.is_empty()
                || !request.descriptors.is_empty()
                || !request.outpoints.is_empty()
            {
                return Err("Invalid confirmed script request.");
            }
            let Some(owner) = self.owners.get_mut(&request.owner) else {
                return Ok(json!({"phase":"unavailable"}));
            };
            owner.reconcile(chain)?;
            return confirmed::page(owner, chain, query);
        }
        if request.action == "transaction" {
            if !request.scripts.is_empty()
                || !request.outpoints.is_empty()
                || !request.descriptors.is_empty()
            {
                return Err("Invalid transaction request.");
            }
            let txid = request.txid.ok_or("Missing transaction id.")?;
            let offset = request.offset.ok_or("Missing transaction offset.")?;
            let Some(owner) = self.owners.get_mut(&request.owner) else {
                return Ok(json!({"phase":"unavailable"}));
            };
            owner.reconcile(chain)?;
            return owner.transaction(chain, txid, offset);
        }
        if request.txid.is_some() || request.offset.is_some() {
            return Err("Unexpected transaction fields.");
        }
        match request.action.as_str() {
            "register" => {
                if request.scripts.is_empty()
                    && request.outpoints.is_empty()
                    && request.descriptors.is_empty()
                {
                    return Err("Empty watch registration.");
                }
                let mut scripts = Vec::new();
                for text in request.scripts {
                    if text.is_empty() || text.len() > 20000 {
                        return Err("Invalid public script.");
                    }
                    scripts.push(ScriptBuf::from_hex(&text).map_err(|_| "Invalid public script.")?);
                }
                let tree = self.db.open_tree(&request.owner).map_err(storage)?;
                let owner = self
                    .owners
                    .entry(request.owner.clone())
                    .or_insert_with(|| Owner {
                        watches: Watches::default(),
                        tree,
                        cursor: None,
                        parent_cursor: None,
                        matched: 0,
                        unavailable: false,
                    });
                let mut watches = owner.watches.clone();
                let mut extended = false;
                for descriptor in request.descriptors {
                    extended |= watches.extend_descriptor(descriptor, network)?;
                }
                if extended
                    || scripts.iter().any(|s| !watches.scripts.contains(s))
                    || request
                        .outpoints
                        .iter()
                        .any(|o| !watches.outpoints.contains(o))
                {
                    watches.scripts.extend(scripts);
                    watches.outpoints.extend(request.outpoints);
                    owner.reset_to(watches)?;
                }
                self.db
                    .insert(request.owner.as_bytes(), &[])
                    .map_err(storage)?;
                self.db.flush().map_err(storage)?;
            }
            "coverage"
                if request.scripts.is_empty()
                    && request.outpoints.is_empty()
                    && request.descriptors.is_empty() => {}
            _ => return Err("Invalid watch command."),
        }
        let owner = self
            .owners
            .get_mut(&request.owner)
            .ok_or("Unknown watch owner.")?;
        owner.reconcile(chain)?;
        let caught_up = owner.cursor.is_some()
            && chain.get_best_block().ok() == owner.cursor
            && chain.get_validation_index().ok() == owner.cursor.map(|c| c.0)
            && !chain.is_in_ibd();
        let parents_pending = owner.has_missing_parents()?;
        let exhausted =
            parents_pending && owner.parent_cursor.is_some() && owner.parent_cursor == owner.cursor;
        let phase = if owner.unavailable || exhausted {
            "unavailable"
        } else if caught_up && !parents_pending {
            "caught-up"
        } else if owner.cursor.is_none() {
            "registered"
        } else {
            "scanning"
        };
        Ok(
            json!({ "phase":phase, "height":owner.cursor.map(|c| c.0), "hash":owner.cursor.map(|c| c.1),
            "matchedTransactions":owner.matched, "requiredScripts":owner.watches.scripts.len(), "requiredOutpoints":owner.watches.outpoints.len() }),
        )
    }
}

impl Owner {
    fn reset_to(&mut self, watches: Watches) -> Result<()> {
        // Removing the cursor together with all derived records makes a restart
        // after an expansion or a reorg start from genesis. Preserve the union
        // of old and new requirements throughout, even if a write is retried.
        let mut batch = sled::Batch::default();
        for key in self.tree.iter().keys() {
            batch.remove(key.map_err(storage)?);
        }
        batch.insert(b"proof-format", &b"2"[..]);
        for script in &watches.scripts {
            batch.insert(
                format!("script/{}", floresta_common::get_spk_hash(script)).as_bytes(),
                &[],
            );
        }
        batch.insert(b"watches", serde_json::to_vec(&watches).map_err(storage)?);
        self.tree.apply_batch(batch).map_err(storage)?;
        self.tree.flush().map_err(storage)?;
        self.watches = watches;
        self.cursor = None;
        self.parent_cursor = None;
        self.matched = 0;
        self.unavailable = false;
        Ok(())
    }

    fn reconcile(&mut self, chain: &impl BlockchainInterface) -> Result<()> {
        if let Some((height, hash)) = self.cursor {
            let tip = chain.get_height().map_err(|_| "Chain tip unavailable.")?;
            if height > tip
                || chain
                    .get_block_hash(height)
                    .map_err(|_| "Chain anchor unavailable.")?
                    != hash
            {
                self.reset_to(self.watches.clone())?;
            }
        }
        Ok(())
    }

    fn apply(&mut self, height: u32, block: &Block) -> Result<()> {
        let mut batch = sled::Batch::default();
        confirmed::apply(self, &mut batch, height, block)?;
        let mut found = HashSet::new();
        let mut matched = self.matched;
        let mut parents = HashSet::new();
        let mut stored = HashSet::new();
        for (position, tx) in block.txdata.iter().enumerate() {
            let txid = tx.compute_txid();
            let mut relevant = false;
            for input in &tx.input {
                let prev = input.previous_output;
                if self.watches.outpoints.contains(&prev)
                    || found.contains(&prev)
                    || self
                        .tree
                        .contains_key(format!("out/{prev}"))
                        .map_err(storage)?
                {
                    relevant = true;
                }
            }
            for (index, output) in tx.output.iter().enumerate() {
                let outpoint = OutPoint::new(txid, index as u32);
                if self.watches.scripts.contains(&output.script_pubkey)
                    || self.watches.outpoints.contains(&outpoint)
                {
                    relevant = true;
                    found.insert(outpoint);
                    batch.insert(format!("out/{outpoint}").as_bytes(), &[]);
                }
            }
            if relevant {
                matched += 1;
                if !tx.is_coinbase() {
                    parents.extend(tx.input.iter().map(|input| input.previous_output.txid));
                }
                save_proof(&mut batch, block, height, position, tx)?;
                stored.insert(txid);
            }
        }
        // The parent's position may precede the match in this same block.
        // Capture such a parent without another network request. Never follow
        // the inputs of a transaction stored solely as somebody else's parent.
        if !parents.is_empty() {
            for (position, tx) in block.txdata.iter().enumerate() {
                let txid = tx.compute_txid();
                if parents.contains(&txid) && !stored.contains(&txid) {
                    save_proof(&mut batch, block, height, position, tx)?;
                    stored.insert(txid);
                }
            }
        }
        let mut reset_parent_cursor = false;
        for txid in parents {
            let missing = format!("need/{txid}");
            if !stored.contains(&txid)
                && !self
                    .tree
                    .contains_key(format!("proof/{txid}"))
                    .map_err(storage)?
                && !self.tree.contains_key(&missing).map_err(storage)?
            {
                batch.insert(missing.as_bytes(), &[]);
                reset_parent_cursor = true;
            }
        }
        if reset_parent_cursor {
            batch.remove(b"parent-cursor");
        }
        let cursor = (height, block.block_hash());
        batch.insert(b"matches", serde_json::to_vec(&matched).map_err(storage)?);
        batch.insert(b"cursor", serde_json::to_vec(&cursor).map_err(storage)?);
        self.tree.apply_batch(batch).map_err(storage)?;
        self.cursor = Some(cursor);
        if reset_parent_cursor {
            self.parent_cursor = None;
        }
        self.matched = matched;
        self.unavailable = false;
        Ok(())
    }

    fn has_missing_parents(&self) -> Result<bool> {
        Ok(self
            .tree
            .scan_prefix(b"need/")
            .next()
            .transpose()
            .map_err(storage)?
            .is_some())
    }

    fn next_height(&self, target: u32) -> Result<Option<u32>> {
        let next = self.cursor.map_or(0, |c| c.0.saturating_add(1));
        if next <= target {
            return Ok(Some(next));
        }
        let replay = self.parent_cursor.map_or(0, |c| c.0.saturating_add(1));
        Ok((replay <= target && self.has_missing_parents()?).then_some(replay))
    }

    fn replay(&mut self, height: u32, block: &Block) -> Result<()> {
        let mut batch = sled::Batch::default();
        for (position, tx) in block.txdata.iter().enumerate() {
            if self
                .tree
                .contains_key(format!("need/{}", tx.compute_txid()))
                .map_err(storage)?
            {
                save_proof(&mut batch, block, height, position, tx)?;
            }
        }
        let cursor = (height, block.block_hash());
        batch.insert(
            b"parent-cursor",
            serde_json::to_vec(&cursor).map_err(storage)?,
        );
        self.tree.apply_batch(batch).map_err(storage)?;
        self.parent_cursor = Some(cursor);
        self.unavailable = false;
        Ok(())
    }

    fn transaction(
        &self,
        chain: &impl BlockchainInterface,
        txid: Txid,
        offset: u32,
    ) -> Result<Value> {
        let unavailable = || json!({"phase":"unavailable"});
        let tip = chain.get_best_block().map_err(storage)?;
        if self.cursor != Some(tip)
            || chain.get_validation_index().ok() != Some(tip.0)
            || chain.is_in_ibd()
        {
            return Ok(unavailable());
        }
        let Some(bytes) = self.tree.get(format!("proof/{txid}")).map_err(storage)? else {
            return Ok(unavailable());
        };
        let meta: ProofRecord = serde_json::from_slice(&bytes).map_err(storage)?;
        if meta.height > tip.0 || chain.get_block_hash(meta.height).ok() != Some(meta.block) {
            return Ok(unavailable());
        }
        let header = chain.get_block_header(&meta.block).map_err(storage)?;
        if header.block_hash() != meta.block
            || meta.proof.target != txid
            || !meta
                .proof
                .verify(header.merkle_root.to_raw_hash())
                .map_err(storage)?
        {
            return Err("Invalid indexed transaction proof.");
        }
        if offset >= meta.size || offset % REPLY_BYTES != 0 {
            return Err("Invalid transaction offset.");
        }
        let page = self
            .tree
            .get(format!("raw/{txid}/{}", offset / PAGE_BYTES))
            .map_err(storage)?
            .ok_or("Missing indexed transaction page.")?;
        let start = (offset % PAGE_BYTES) as usize;
        let n = REPLY_BYTES.min(meta.size - offset) as usize;
        let chunk = page
            .get(start..start + n)
            .ok_or("Invalid indexed transaction page.")?;
        if chain.get_best_block().ok() != Some(tip)
            || chain.get_validation_index().ok() != Some(tip.0)
        {
            return Ok(unavailable());
        }
        use bitcoin::hex::DisplayHex;
        Ok(
            json!({ "phase":"confirmed", "txid":txid, "height":meta.height, "blockHash":meta.block,
            "tipHeight":tip.0, "tipHash":tip.1, "header":serialize_hex(&header), "position":meta.proof.pos,
            "merkle":meta.proof.hashes, "wtxid":meta.wtxid, "size":meta.size, "offset":offset, "chunk":chunk.to_lower_hex_string() }),
        )
    }
}

const REPLY_BYTES: u32 = 512;
const PAGE_BYTES: u32 = 16384;

#[derive(Serialize, Deserialize)]
struct ProofRecord {
    height: u32,
    block: BlockHash,
    size: u32,
    wtxid: Wtxid,
    proof: MerkleProof,
}

fn save_proof(
    batch: &mut sled::Batch,
    block: &Block,
    height: u32,
    position: usize,
    tx: &Transaction,
) -> Result<()> {
    let txid = tx.compute_txid();
    let raw = serialize(tx);
    let record = ProofRecord {
        height,
        block: block.block_hash(),
        size: raw.len() as u32,
        wtxid: tx.compute_wtxid(),
        proof: MerkleProof::from_block(block, position as u64),
    };
    batch.insert(
        format!("proof/{txid}").as_bytes(),
        serde_json::to_vec(&record).map_err(storage)?,
    );
    for (i, chunk) in raw.chunks(PAGE_BYTES as usize).enumerate() {
        batch.insert(format!("raw/{txid}/{i}").as_bytes(), chunk);
    }
    batch.remove(format!("need/{txid}").as_bytes());
    Ok(())
}

fn verified_block(block: &Block, hash: BlockHash) -> bool {
    // Reject duplicate txids, including the duplicated-tail Merkle ambiguity.
    block.block_hash() == hash
        && block.check_merkle_root()
        && block.check_witness_commitment()
        && block
            .txdata
            .iter()
            .map(|tx| tx.compute_txid())
            .collect::<HashSet<_>>()
            .len()
            == block.txdata.len()
}

async fn scan(
    registry: &Mutex<Registry>,
    network: Network,
    chain: &impl BlockchainInterface,
    peer: &NodeInterface,
) -> Result<bool> {
    let target = chain
        .get_validation_index()
        .map_err(|_| "Chain unavailable.")?;
    let next = {
        let mut registry = registry.lock().map_err(storage)?;
        let mut next = None;
        for owner in registry.owners.values_mut() {
            owner.reconcile(chain)?;
            if let Some(height) = owner.next_height(target)? {
                next = Some(next.map_or(height, |n: u32| n.min(height)));
            }
        }
        next
    };
    let Some(height) = next else {
        return Ok(false);
    };
    let hash = chain
        .get_block_hash(height)
        .map_err(|_| "Historical header unavailable.")?;
    let block = if height == 0 {
        Some(genesis_block(network))
    } else {
        tokio::time::timeout(Duration::from_secs(20), peer.get_block(hash))
            .await
            .ok()
            .and_then(|r| r.ok())
            .flatten()
    };
    let block = block.filter(|b| verified_block(b, hash));
    let mut registry = registry.lock().map_err(storage)?;
    if chain.get_block_hash(height).ok() != Some(hash)
        || chain.get_validation_index().map_or(true, |h| h < height)
    {
        return Ok(false);
    }
    for owner in registry.owners.values_mut() {
        owner.reconcile(chain)?;
        if owner.next_height(target)? != Some(height) {
            continue;
        }
        if let Some(block) = &block {
            let primary = owner.cursor.map_or(0, |c| c.0.saturating_add(1)) == height;
            let previous = if primary {
                owner.cursor
            } else {
                owner.parent_cursor
            };
            if previous.is_some_and(|(_, previous)| previous != block.header.prev_blockhash) {
                continue;
            }
            if primary {
                owner.apply(height, block)?;
            } else {
                owner.replay(height, block)?;
            }
        } else {
            owner.unavailable = true;
        }
    }
    Ok(block.is_some())
}

pub(crate) fn start<C: BlockchainInterface + Send + Sync + 'static>(
    data_dir: &str,
    network: Network,
    chain: Arc<C>,
    peer: NodeInterface,
    stop: Arc<RwLock<bool>>,
) -> io::Result<()> {
    let registry = Arc::new(Mutex::new(
        Registry::open(&Path::new(data_dir).join("chicory-watches-v1"))
            .map_err(io::Error::other)?,
    ));
    let control = registry.clone();
    let reader_chain = chain.clone();
    let owner_lifetime = stop.clone();
    std::thread::spawn(move || {
        let mut input = io::stdin().lock();
        loop {
            let mut line = Vec::new();
            if input
                .by_ref()
                .take(LIMIT as u64)
                .read_until(b'\n', &mut line)
                .is_err()
                || line.last() != Some(&b'\n')
            {
                break;
            }
            let Ok(command) = serde_json::from_slice::<Command>(&line) else {
                break;
            };
            let id = command.id;
            let reply = match control
                .lock()
                .map_err(storage)
                .and_then(|mut r| r.command(command, network, &*reader_chain))
            {
                Ok(result) => json!({ "protocol":"chicory.watch/1", "id":id, "result":result }),
                Err(error) => json!({ "protocol":"chicory.watch/1", "id":id, "error":error }),
            };
            if writeln!(io::stdout().lock(), "{reply}").is_err() {
                break;
            }
        }
        *owner_lifetime.blocking_write() = true;
    });
    tokio::spawn(async move {
        while !*stop.read().await {
            match scan(&registry, network, &*chain, &peer).await {
                Ok(true) => tokio::task::yield_now().await,
                Ok(false) => tokio::time::sleep(Duration::from_secs(2)).await,
                Err(_) => {
                    *stop.write().await = true;
                }
            }
        }
    });
    Ok(())
}
