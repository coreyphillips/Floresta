// SPDX-License-Identifier: MIT OR Apache-2.0
//! A regtest-only wallet send. Authorize every input against the active owner's
//! confirmed UTXOs, then hand one transaction to its exact connected proof peer.
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::Duration;

use bitcoin::consensus::deserialize;
use bitcoin::hashes::Hash;
use bitcoin::hex::FromHex;
use bitcoin::{BlockHash, Network, OutPoint, Transaction, Txid};
use floresta_chain::pruned_utreexo::consensus::Consensus;
use floresta_chain::{BlockchainInterface, ChainParams, UtxoData};
use floresta_wire::node_interface::NodeInterface;
use serde::Deserialize;
use serde_json::{Value, json};

use super::{Cursor, Owner, PAGE_BYTES, ProofRecord, Registry, Result, pending, storage};

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct Request {
    tip: BlockHash,
    hex: String,
}

fn active(owner: &Owner, chain: &impl BlockchainInterface, tip: Cursor) -> bool {
    owner.cursor == Some(tip)
        && !owner.unavailable
        && chain.get_best_block().ok() == Some(tip)
        && !chain.is_in_ibd()
        && chain.get_validation_index().ok() == Some(tip.0)
}

fn coin(
    owner: &Owner,
    chain: &impl BlockchainInterface,
    prev: OutPoint,
    budget: &mut u32,
) -> Result<UtxoData> {
    if !owner
        .tree
        .contains_key(format!("coin/{prev}"))
        .map_err(storage)?
    {
        return Err("Input is not a confirmed owner UTXO.");
    }
    let bytes = owner
        .tree
        .get(format!("proof/{}", prev.txid))
        .map_err(storage)?
        .ok_or("Missing input metadata.")?;
    let m: ProofRecord = serde_json::from_slice(&bytes).map_err(storage)?;
    *budget = budget
        .checked_sub(m.size)
        .ok_or("Parent data exceeds the regtest qualification bound.")?;
    if m.height == 0
        || m.size == 0
        || chain.get_block_hash(m.height).ok() != Some(m.block)
        || m.proof.target != prev.txid
    {
        return Err("Input is not on the active chain.");
    }
    let header = chain.get_block_header(&m.block).map_err(storage)?;
    if header.block_hash() != m.block
        || !m
            .proof
            .verify(header.merkle_root.to_raw_hash())
            .map_err(storage)?
    {
        return Err("Invalid input proof.");
    }
    let mut raw = Vec::with_capacity(m.size as usize);
    for page in 0..m.size.div_ceil(PAGE_BYTES) {
        let bytes = owner
            .tree
            .get(format!("raw/{}/{page}", prev.txid))
            .map_err(storage)?
            .ok_or("Missing input bytes.")?;
        if bytes.len() != (m.size - page * PAGE_BYTES).min(PAGE_BYTES) as usize {
            return Err("Invalid input page.");
        }
        raw.extend_from_slice(&bytes);
    }
    let tx: Transaction = deserialize(&raw).map_err(storage)?;
    if tx.compute_txid() != prev.txid || tx.compute_wtxid() != m.wtxid {
        return Err("Invalid input identity.");
    }
    let out = tx
        .output
        .get(prev.vout as usize)
        .ok_or("Invalid input index.")?;
    if !owner.watches.scripts.contains(&out.script_pubkey) {
        return Err("Input is outside the owner registration.");
    }
    Ok(UtxoData {
        txout: out.clone(),
        creation_height: m.height,
        creation_time: pending::mtp(chain, m.height - 1)?,
        is_coinbase: tx.is_coinbase(),
    })
}

pub(super) fn submit<C: BlockchainInterface + Send + Sync + 'static>(
    registry: &Arc<Mutex<Registry>>,
    chain: &Arc<C>,
    peer: &NodeInterface,
    network: Network,
    owner_id: String,
    txid: Txid,
    request: Request,
) -> Result<Value> {
    if network != Network::Regtest
        || !peer.fixture_broadcast_available()
        || request.hex.len() > 60000
    {
        return Err("Wallet broadcast is unavailable.");
    }
    let tx: Transaction =
        deserialize(&Vec::from_hex(&request.hex).map_err(storage)?).map_err(storage)?;
    if tx.compute_txid() != txid
        || tx.is_coinbase()
        || tx.input.is_empty()
        || tx.input.len() > 32
        || tx.output.is_empty()
    {
        return Err("Invalid wallet transaction.");
    }
    Consensus::check_transaction_context_free(&tx).map_err(storage)?;
    let tip = chain.get_best_block().map_err(storage)?;
    if request.tip != tip.1 {
        return Err("Wallet tip changed.");
    }
    {
        let registry = registry.lock().map_err(storage)?;
        let owner = registry
            .owners
            .get(&owner_id)
            .ok_or("Unknown wallet owner.")?;
        if !active(owner, &**chain, tip)
            || owner.has_missing_parents()?
            || registry.pool.lock().map_err(storage)?.spends_any(&tx)
        {
            return Err("Wallet inputs are unavailable.");
        }
        let next = tip.0.checked_add(1).ok_or("Invalid height.")?;
        let mut coins = Vec::with_capacity(tx.input.len());
        let mut inputs = HashMap::new();
        let mut budget = 2_000_000;
        for input in &tx.input {
            let prev = input.previous_output;
            let coin = coin(owner, &**chain, prev, &mut budget)?;
            if inputs.insert(prev, coin.clone()).is_some() {
                return Err("Repeated wallet input.");
            }
            coins.push(coin);
        }
        if !pending::final_at(&tx, &coins, next, pending::mtp(&**chain, tip.0)?) {
            return Err("Wallet transaction is timelocked.");
        }
        let flags =
            ChainParams::from(network).get_validation_flags(u32::MAX, BlockHash::all_zeros());
        Consensus::verify_transaction(&tx, &mut inputs, next, true, flags)
            .map_err(|_| "Invalid wallet signatures or values.")?;
    }
    let registry = registry.clone();
    let chain = chain.clone();
    let check_tx = tx.clone();
    let allowed = Arc::new(move || {
        let Ok(registry) = registry.lock() else {
            return false;
        };
        let Some(owner) = registry.owners.get(&owner_id) else {
            return false;
        };
        active(owner, &*chain, tip)
            && owner.has_missing_parents() == Ok(false)
            && check_tx.input.iter().all(|i| {
                owner
                    .tree
                    .contains_key(format!("coin/{}", i.previous_output))
                    .ok()
                    == Some(true)
            })
            && registry.pool.lock().is_ok_and(|p| !p.spends_any(&check_tx))
    });
    let receipt = peer
        .offer_fixture_transaction(tip.1, tx, allowed)
        .ok_or("A wallet offer is unavailable at this tip.")?;
    receipt
        .recv_timeout(Duration::from_secs(8))
        .map_err(|_| "Wallet delivery is uncertain.")?;
    Ok(json!({"phase":"relayed", "txid":txid, "tipHash":tip.1}))
}
