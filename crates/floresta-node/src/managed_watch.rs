// SPDX-License-Identifier: MIT OR Apache-2.0
//! Confirmed history for explicitly registered public scripts and outpoints.
//! The cursor and its block's matches are committed in the same database batch.
//! No Electrum client can register a watch or read this index.

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::io::{self, BufRead, Read, Write};
use std::path::Path;
use std::str::FromStr;
use std::sync::{Arc, Mutex};
use std::time::Duration;

use bitcoin::blockdata::constants::genesis_block;
use bitcoin::consensus::encode::serialize_hex;
use bitcoin::{Block, BlockHash, Network, OutPoint, ScriptBuf};
use floresta_chain::pruned_utreexo::BlockchainInterface;
use floresta_watch_only::merkle::MerkleProof;
use floresta_wire::node_interface::NodeInterface;
use miniscript::descriptor::Wildcard;
use miniscript::{Descriptor, DescriptorPublicKey, ForEachKey};
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
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
            owners.insert(
                id.to_string(),
                Owner {
                    watches,
                    tree,
                    cursor,
                    matched,
                    unavailable: false,
                },
            );
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
        let phase = if owner.unavailable {
            "unavailable"
        } else if caught_up {
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
        batch.insert(b"watches", serde_json::to_vec(&watches).map_err(storage)?);
        self.tree.apply_batch(batch).map_err(storage)?;
        self.tree.flush().map_err(storage)?;
        self.watches = watches;
        self.cursor = None;
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
        let mut found = HashSet::new();
        let mut matched = self.matched;
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
                let record = json!({ "height":height, "block":block.block_hash(), "hex":serialize_hex(tx),
                    "proof":MerkleProof::from_block(block, position as u64) });
                batch.insert(
                    format!("tx/{height:08x}/{position:08x}").as_bytes(),
                    serde_json::to_vec(&record).map_err(storage)?,
                );
            }
        }
        let cursor = (height, block.block_hash());
        batch.insert(b"matches", serde_json::to_vec(&matched).map_err(storage)?);
        batch.insert(b"cursor", serde_json::to_vec(&cursor).map_err(storage)?);
        self.tree.apply_batch(batch).map_err(storage)?;
        self.cursor = Some(cursor);
        self.matched = matched;
        self.unavailable = false;
        Ok(())
    }
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
            let height = owner.cursor.map_or(0, |c| c.0.saturating_add(1));
            if height <= target {
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
        if owner.cursor.map_or(0, |c| c.0.saturating_add(1)) != height {
            continue;
        }
        if let Some(block) = &block {
            if owner
                .cursor
                .is_some_and(|(_, previous)| previous != block.header.prev_blockhash)
            {
                continue;
            }
            owner.apply(height, block)?;
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
