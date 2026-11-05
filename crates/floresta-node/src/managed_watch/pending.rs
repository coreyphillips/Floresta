// SPDX-License-Identifier: MIT OR Apache-2.0
//! Peer-observed transactions for the managed index. All inputs must be
//! proven against the local tip or spend an already checked pool output.
use std::collections::{BTreeMap, HashMap, HashSet};
use std::time::{Duration, Instant};

use bitcoin::hashes::Hash;
use bitcoin::{BlockHash, Network, OutPoint, Transaction, TxOut, Txid};
use floresta_chain::proof_util::reconstruct_leaf_data;
use floresta_chain::pruned_utreexo::consensus::Consensus;
use floresta_chain::{BlockchainInterface, ChainParams, CompactLeafData, UtxoData};
use floresta_common::get_spk_hash;
use rustreexo::node_hash::BitcoinNodeHash;
use rustreexo::proof::Proof;
use rustreexo::stump::Stump;
use serde::Deserialize;
use serde_json::{json, Value};

use super::{owner_id, storage, Cursor, Owner, Result};

const MAX_COUNT: usize = 4096;
const MAX_BYTES: usize = 16 * 1024 * 1024;
const MAX_INPUTS: usize = 256;
const MAX_ANCESTORS: usize = 25;
const MAX_REPLACEMENTS: usize = 100;
const MAX_AGE: Duration = Duration::from_secs(60 * 60 * 2);

#[derive(Deserialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub(super) struct Query {
    script_hash: String,
    after: Option<Txid>,
}

struct Entry {
    tx: Transaction,
    inputs: Vec<TxOut>,
    fee: u64,
    cost: usize,
    seen: Instant,
}

#[derive(Default)]
pub(super) struct Pool {
    anchor: Option<Cursor>,
    entries: BTreeMap<Txid, Entry>,
    spent: HashMap<OutPoint, Txid>,
    bytes: usize,
    revision: u64,
}

// A retained tip hash alone is insufficient during a chain switch.
fn active(chain: &impl BlockchainInterface, tip: Cursor) -> bool {
    !chain.is_in_ibd()
        && chain.get_validation_index().ok() == Some(tip.0)
        && chain.get_best_block().ok() == Some(tip)
}

fn mtp(chain: &impl BlockchainInterface, height: u32) -> Result<u32> {
    let mut hash = chain.get_block_hash(height).map_err(storage)?;
    let mut times = Vec::with_capacity(11);
    for _ in 0..height.saturating_add(1).min(11) {
        let header = chain.get_block_header(&hash).map_err(storage)?;
        times.push(header.time);
        hash = header.prev_blockhash;
    }
    times.sort_unstable();
    Ok(times[times.len() / 2])
}

// Count targets and siblings before using the block validation primitive.
fn check_proof(stump: &Stump, hashes: &[BitcoinNodeHash], proof: &Proof) -> Result<()> {
    if hashes.len() != proof.targets.len() || hashes.len() > MAX_INPUTS {
        return Err("Invalid proof dimensions.");
    }
    let required = floresta_wire::proven_tx::proof_positions(&proof.targets, stump.leaves)
        .ok_or("Invalid proof positions.")?;
    if proof.hashes.len() != required.len() {
        return Err("Mismatched proof siblings.");
    }
    // Use the same root-matching path as block validation, on an immutable
    // snapshot. The temporary removal result is never committed.
    stump
        .modify(&[], hashes, proof)
        .map_err(|_| "Invalid transaction inclusion proof.")?;
    Ok(())
}

fn final_at(tx: &Transaction, coins: &[UtxoData], height: u32, time: u32) -> bool {
    let lock = tx.lock_time.to_consensus_u32();
    let reached = lock == 0 || lock < if lock < 500_000_000 { height } else { time };
    if !reached && tx.input.iter().any(|i| i.sequence.0 != u32::MAX) {
        return false;
    }
    if tx.version.0 < 2 {
        return true;
    }
    tx.input.iter().zip(coins).all(|(input, coin)| {
        let sequence = input.sequence.0;
        if sequence & (1 << 31) != 0 {
            return true;
        }
        let delay = sequence & 0xffff;
        let (at, earliest) = if sequence & (1 << 22) != 0 {
            (time, coin.creation_time.checked_add(delay << 9))
        } else {
            (height, coin.creation_height.checked_add(delay))
        };
        earliest.is_some_and(|earliest| earliest <= at)
    })
}

impl Pool {
    fn clear(&mut self, anchor: Option<Cursor>) {
        self.entries.clear();
        self.spent.clear();
        self.bytes = 0;
        self.anchor = anchor;
        self.revision += 1;
    }

    pub(super) fn reconcile(&mut self, chain: &impl BlockchainInterface) {
        let anchor = chain
            .get_best_block()
            .ok()
            .filter(|tip| active(chain, *tip));
        if anchor != self.anchor || self.entries.values().any(|e| e.seen.elapsed() > MAX_AGE) {
            // Proofs depend on the tip. An old observation is never reused as
            // evidence after the chain advances or a fork replaces its anchor.
            self.clear(anchor);
        }
    }

    pub(super) fn admit(
        &mut self,
        chain: &impl BlockchainInterface,
        network: Network,
        tip: Cursor,
        tx: &Transaction,
        proof: &Proof,
        leaves: &[Option<CompactLeafData>],
    ) -> Result<()> {
        self.reconcile(chain);
        if self.anchor != Some(tip)
            || tx.input.len() != leaves.len()
            || tx.input.len() > MAX_INPUTS
            || tx.weight().to_wu() > 400_000
            || tx.input.is_empty()
        {
            return Err("Ineligible pending transaction.");
        }
        let txid = tx.compute_txid();
        if self.entries.contains_key(&txid) {
            return Ok(());
        }
        let mut distinct = HashSet::new();
        if tx
            .input
            .iter()
            .any(|i| i.previous_output.is_null() || !distinct.insert(i.previous_output))
        {
            return Err("Invalid or repeated previous output.");
        }
        let next = tip.0.checked_add(1).ok_or("Invalid tip height.")?;
        let time = mtp(chain, tip.0)?;
        let stump = chain.acc();
        let mut hashes = Vec::new();
        let mut coins = Vec::with_capacity(leaves.len());
        let mut script_inputs = HashMap::new();
        let mut ancestors = HashSet::new();
        let mut work = Vec::new();
        for (input, leaf) in tx.input.iter().zip(leaves) {
            let prev = input.previous_output;
            let coin = if let Some(leaf) = leaf {
                let h = leaf.header_code >> 1;
                if h == 0 || h > tip.0 {
                    return Err("Invalid confirmed input height.");
                }
                let hash = chain.get_block_hash(h).map_err(storage)?;
                let data = reconstruct_leaf_data(leaf, input, hash)
                    .map_err(|_| "Cannot reconstruct input.")?;
                let hash = data._get_leaf_hashes();
                if Consensus::contains_unspendable_utxo(&[hash]) {
                    return Err("Input spends an overwritten coinbase.");
                }
                hashes.push(BitcoinNodeHash::Some(hash.to_byte_array()));
                UtxoData {
                    txout: data.utxo,
                    creation_height: h,
                    creation_time: mtp(chain, h - 1)?,
                    is_coinbase: leaf.header_code & 1 == 1,
                }
            } else {
                let entry = self
                    .entries
                    .get(&prev.txid)
                    .ok_or("Missing pending parent.")?;
                let output = entry
                    .tx
                    .output
                    .get(prev.vout as usize)
                    .ok_or("Invalid pending prevout.")?;
                work.push(prev.txid);
                UtxoData {
                    txout: output.clone(),
                    creation_height: next,
                    creation_time: time,
                    is_coinbase: false,
                }
            };
            script_inputs.insert(prev, coin.clone());
            coins.push(coin);
        }
        while let Some(id) = work.pop() {
            if !ancestors.insert(id) {
                continue;
            }
            if ancestors.len() > MAX_ANCESTORS {
                return Err("Pending ancestry exceeds limit.");
            }
            if let Some(e) = self.entries.get(&id) {
                work.extend(
                    e.tx.input
                        .iter()
                        .map(|i| i.previous_output.txid)
                        .filter(|id| self.entries.contains_key(id)),
                );
            }
        }
        check_proof(&stump, &hashes, proof)?;
        if !final_at(&tx, &coins, next, time) {
            return Err("Pending transaction is timelocked.");
        }
        // Apply all currently deployed relay script checks, including on short
        // regtest chains. No historical block exception applies to the mempool.
        let flags =
            ChainParams::from(network).get_validation_flags(u32::MAX, BlockHash::all_zeros());
        let (credit, debit) =
            Consensus::verify_transaction(&tx, &mut script_inputs, next, true, flags)
                .map_err(|_| "Pending input scripts or transaction values are invalid.")?;
        let fee = credit.to_sat() - debit.to_sat();
        let inputs: Vec<_> = coins.into_iter().map(|coin| coin.txout).collect();
        self.insert(tx, inputs, fee, &ancestors, || active(chain, tip))
    }

    fn insert(
        &mut self,
        tx: &Transaction,
        inputs: Vec<TxOut>,
        fee: u64,
        ancestors: &HashSet<Txid>,
        still_active: impl FnOnce() -> bool,
    ) -> Result<()> {
        let txid = tx.compute_txid();
        let cost = tx.total_size()
            + inputs
                .iter()
                .map(|coin| coin.script_pubkey.len() + 64)
                .sum::<usize>();
        let direct: HashSet<_> = tx
            .input
            .iter()
            .filter_map(|i| self.spent.get(&i.previous_output).copied())
            .collect();
        let mut evict = direct.clone();
        let mut queue: Vec<_> = direct.iter().copied().collect();
        while let Some(id) = queue.pop() {
            if ancestors.contains(&id) || evict.len() > MAX_REPLACEMENTS {
                return Err("Invalid replacement ancestry.");
            }
            let old = &self.entries[&id];
            for vout in 0..old.tx.output.len() {
                if let Some(child) = self.spent.get(&OutPoint::new(id, vout as u32)) {
                    if evict.insert(*child) {
                        queue.push(*child);
                    }
                }
            }
        }
        if !evict.is_empty() {
            let paid: u64 = evict.iter().map(|id| self.entries[id].fee).sum();
            let min_fee = paid.saturating_add(tx.vsize() as u64);
            if fee < min_fee
                || direct.iter().any(|id| {
                    let old = &self.entries[id];
                    u128::from(fee) * old.tx.vsize() as u128
                        <= u128::from(old.fee) * tx.vsize() as u128
                })
            {
                return Err("Insufficient replacement fee.");
            }
            // Do not admit a replacement that introduces a new unconfirmed input.
            let prior: HashSet<_> = direct
                .iter()
                .flat_map(|id| self.entries[id].tx.input.iter().map(|i| i.previous_output))
                .collect();
            if tx.input.iter().any(|i| {
                self.entries.contains_key(&i.previous_output.txid)
                    && !prior.contains(&i.previous_output)
            }) {
                return Err("Replacement adds a pending input.");
            }
        }
        let recovered: usize = evict.iter().map(|id| self.entries[id].cost).sum();
        if self.bytes - recovered + cost > MAX_BYTES
            || self.entries.len() - evict.len() >= MAX_COUNT
        {
            return Err("Pending view is full.");
        }
        if !still_active() {
            return Err("Transaction proof tip changed.");
        }
        for id in evict {
            if let Some(old) = self.entries.remove(&id) {
                for input in old.tx.input {
                    self.spent.remove(&input.previous_output);
                }
            }
        }
        for input in &tx.input {
            self.spent.insert(input.previous_output, txid);
        }
        self.bytes = self.bytes - recovered + cost;
        self.entries.insert(
            txid,
            Entry {
                tx: tx.clone(),
                inputs,
                fee,
                cost,
                seen: Instant::now(),
            },
        );
        self.revision += 1;
        Ok(())
    }

    pub(super) fn page(
        &mut self,
        owner: &Owner,
        chain: &impl BlockchainInterface,
        query: Query,
    ) -> Result<Value> {
        self.reconcile(chain);
        let Some(tip) = self.anchor else {
            return Ok(json!({"phase":"unavailable"}));
        };
        if !owner_id(&query.script_hash)
            || owner.cursor != Some(tip)
            || owner.unavailable
            || owner.has_missing_parents()?
            || !owner
                .tree
                .contains_key(format!("script/{}", query.script_hash))
                .map_err(storage)?
        {
            return Ok(json!({"phase":"unavailable"}));
        }
        let mut rows = Vec::new();
        let mut next = None;
        let mut last = None;
        let mut size = 0;
        for (id, e) in &self.entries {
            if query.after.is_some_and(|after| *id <= after) {
                continue;
            }
            let matches =
                |out: &TxOut| get_spk_hash(&out.script_pubkey).to_string() == query.script_hash;
            let spent: Vec<_> = e.tx.input.iter().zip(&e.inputs).filter(|(_,o)| matches(o)).map(|(i,o)|
                json!({"txid": i.previous_output.txid, "vout": i.previous_output.vout, "value": o.value.to_sat()})).collect();
            let created: Vec<_> =
                e.tx.output
                    .iter()
                    .enumerate()
                    .filter(|(_, o)| matches(o))
                    .map(|(vout, o)| json!({"vout":vout,"value":o.value.to_sat()}))
                    .collect();
            if spent.is_empty() && created.is_empty() {
                continue;
            }
            let height = if e
                .tx
                .input
                .iter()
                .any(|i| self.entries.contains_key(&i.previous_output.txid))
            {
                -1
            } else {
                0
            };
            let row =
                json!({"txid":id,"height":height,"fee":e.fee,"spent":spent,"created":created});
            let bytes = row.to_string().len();
            if bytes > 48_000 {
                return Ok(json!({"phase":"unavailable"}));
            }
            if rows.len() == 12 || size + bytes > 48_000 {
                next = last;
                break;
            }
            size += bytes;
            rows.push(row);
            last = Some(id);
        }
        if !active(chain, tip) {
            return Ok(json!({"phase":"unavailable"}));
        }
        Ok(
            json!({"phase":"observed","coverageComplete":false,"tipHeight":tip.0,"tipHash":tip.1,
            "revision":self.revision,"rows":rows,"next":next}),
        )
    }
}

// Observe the private inbox on a dedicated worker. Remote script checks must
// not block chain sync. Orphans wait only for an admitted parent, in a bounded
// transient queue. Nothing from this queue reaches a wallet.
pub(super) fn start<C: BlockchainInterface + Send + Sync + 'static>(
    pool: std::sync::Arc<std::sync::Mutex<Pool>>,
    peer: floresta_wire::node_interface::NodeInterface,
    network: Network,
    chain: std::sync::Arc<C>,
    stop: std::sync::Arc<tokio::sync::RwLock<bool>>,
) -> std::io::Result<()> {
    std::thread::Builder::new()
        .name("managed-pending".into())
        .spawn(move || {
            use floresta_wire::proven_tx::Candidate;
            let mut deferred: Vec<(Instant, Candidate, usize)> = Vec::new();
            while !*stop.blocking_read() {
                let mut incoming = peer.drain_proven_transactions();
                let now = Instant::now();
                deferred.retain(|(since, candidate, _)| {
                    now.duration_since(*since) < Duration::from_secs(30)
                        && active(&*chain, (candidate.height, candidate.tip))
                });
                let mut retained: usize = deferred.iter().map(|(_, _, bytes)| bytes).sum();
                while !incoming.is_empty() && !*stop.blocking_read() {
                    let mut advanced = false;
                    for c in incoming.drain(..) {
                        if *stop.blocking_read() {
                            return;
                        }
                        let outcome = match pool.lock() {
                            Ok(mut pool) => pool.admit(
                                &*chain,
                                network,
                                (c.height, c.tip),
                                &c.tx,
                                &c.proof,
                                &c.leaves,
                            ),
                            Err(_) => return,
                        };
                        if outcome == Err("Missing pending parent.") {
                            // Include leaf payloads as well as transaction and sibling bytes.
                            let bytes = c.tx.total_size()
                                + c.proof.hashes.len() * 32
                                + c.leaves
                                    .iter()
                                    .flatten()
                                    .map(|l| match &l.spk_ty {
                                        floresta_chain::ScriptPubKeyKind::Other(bytes) => {
                                            bytes.len() + 64
                                        }
                                        _ => 64,
                                    })
                                    .sum::<usize>();
                            if deferred.len() < 64 && retained + bytes <= 4 * 1024 * 1024 {
                                retained += bytes;
                                deferred.push((now, c, bytes));
                            }
                        } else if outcome.is_ok() {
                            advanced = true;
                        }
                    }
                    if advanced {
                        incoming.extend(deferred.drain(..).map(|(_, c, _)| c));
                        retained = 0;
                    }
                }
                std::thread::sleep(Duration::from_millis(100));
            }
        })?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn proof_shape_and_mixed_confirmed_inputs() {
        let leaves: Vec<_> = (1..=4).map(|n| BitcoinNodeHash::from([n; 32])).collect();
        let stump = Stump::new()
            .modify(&leaves, &[], &Proof::default())
            .unwrap()
            .0;
        let proof = Proof::new(vec![0, 2], vec![leaves[1], leaves[3]]);
        assert!(check_proof(&stump, &[leaves[0], leaves[2]], &proof).is_ok());
        assert!(check_proof(&stump, &[leaves[1], leaves[2]], &proof).is_err());
        for targets in [vec![0, 0], vec![0, 4], vec![0, u64::MAX], vec![0, 1 << 63]] {
            assert!(check_proof(
                &stump,
                &[leaves[0], leaves[2]],
                &Proof::new(targets, vec![leaves[1]])
            )
            .is_err());
        }
        assert!(check_proof(&stump, &[leaves[0]], &Proof::default()).is_err());
        assert!(check_proof(
            &stump,
            &[leaves[0], leaves[2]],
            &Proof::new(vec![0, 2], vec![])
        )
        .is_err());
        assert!(check_proof(&stump, &[], &Proof::default()).is_ok());
    }

    #[test]
    fn replacement_is_atomic_and_evicts_descendants() {
        use bitcoin::{Amount, ScriptBuf, Sequence, TxIn, Witness};
        let spend = |prev, value| Transaction {
            version: bitcoin::transaction::Version::TWO,
            lock_time: bitcoin::absolute::LockTime::ZERO,
            input: vec![TxIn {
                previous_output: prev,
                sequence: Sequence::ENABLE_RBF_NO_LOCKTIME,
                script_sig: ScriptBuf::new(),
                witness: Witness::new(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(value),
                script_pubkey: ScriptBuf::new(),
            }],
        };
        let funding = OutPoint::new(Txid::from_byte_array([3; 32]), 0);
        let first = spend(funding, 99_000);
        let first_id = first.compute_txid();
        let child = spend(OutPoint::new(first_id, 0), 98_500);
        let child_id = child.compute_txid();
        let ancestors = HashSet::new();
        let mut pool = Pool::default();
        assert!(pool
            .insert(&first, vec![], 1_000, &ancestors, || true)
            .is_ok());
        assert!(pool
            .insert(&child, vec![], 500, &HashSet::from([first_id]), || true)
            .is_ok());
        let revision = pool.revision;
        let weak = spend(funding, 98_900);
        assert!(pool
            .insert(&weak, vec![], 1_100, &ancestors, || true)
            .is_err());
        let strong = spend(funding, 97_000);
        assert!(pool
            .insert(&strong, vec![], 3_000, &ancestors, || false)
            .is_err());
        assert_eq!(pool.revision, revision);
        assert!(pool.entries.contains_key(&first_id) && pool.entries.contains_key(&child_id));
        assert!(pool
            .insert(&strong, vec![], 3_000, &ancestors, || true)
            .is_ok());
        assert_eq!(pool.spent.len(), 1);
        assert_eq!(pool.entries.len(), 1);
        assert_eq!(pool.spent.get(&funding), Some(&strong.compute_txid()));
        pool.clear(None);
        assert!(pool.spent.is_empty() && pool.entries.is_empty());
    }

    #[test]
    fn next_block_absolute_and_relative_locks() {
        use bitcoin::absolute::LockTime;
        use bitcoin::{Amount, ScriptBuf, Sequence, TxIn, Witness};
        let coin = UtxoData {
            txout: TxOut {
                value: Amount::from_sat(10),
                script_pubkey: ScriptBuf::new(),
            },
            is_coinbase: false,
            creation_height: 100,
            creation_time: 500_000_000,
        };
        let mut tx = Transaction {
            version: bitcoin::transaction::Version::TWO,
            lock_time: LockTime::ZERO,
            input: vec![TxIn {
                previous_output: OutPoint::null(),
                sequence: Sequence(2),
                script_sig: ScriptBuf::new(),
                witness: Witness::new(),
            }],
            output: Vec::new(),
        };
        let coins = [coin];
        assert!(!final_at(&tx, &coins, 101, 500_000_001));
        assert!(final_at(&tx, &coins, 102, 500_000_001));
        tx.input[0].sequence = Sequence((1 << 22) | 2);
        assert!(!final_at(&tx, &coins, 102, 500_001_023));
        assert!(final_at(&tx, &coins, 102, 500_001_024));
        tx.input[0].sequence = Sequence::ENABLE_RBF_NO_LOCKTIME;
        tx.lock_time = LockTime::from_consensus(103);
        assert!(!final_at(&tx, &coins, 103, 500_001_024));
        assert!(final_at(&tx, &coins, 104, 500_001_024));
        tx.lock_time = LockTime::from_consensus(500_001_024);
        assert!(!final_at(&tx, &coins, 105, 500_001_024));
        tx.input[0].sequence = Sequence::MAX;
        assert!(final_at(&tx, &coins, 102, 500_001_024));
    }
}
