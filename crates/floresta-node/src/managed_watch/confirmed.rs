// SPDX-License-Identifier: MIT OR Apache-2.0
//! Confirmed script rows for a single registered owner. Balances and spend
//! status use the same committed block cursor as the transaction proofs.
use std::collections::{BTreeSet, HashMap};
use std::ops::Bound;

use bitcoin::{Block, OutPoint, Txid};
use floresta_chain::pruned_utreexo::BlockchainInterface;
use floresta_common::get_spk_hash;
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};

use super::{Owner, Result, owner_id, storage};

const PAGE: usize = 12;

#[derive(Deserialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub(super) struct Query {
    script_hash: String,
    kind: Kind,
    after: Option<String>,
}

#[derive(Deserialize, Serialize, Copy, Clone)]
#[serde(rename_all = "lowercase")]
enum Kind {
    History,
    Unspent,
}

impl Kind {
    fn prefix(self) -> &'static str {
        match self {
            Self::History => "hist",
            Self::Unspent => "utxo",
        }
    }
}

#[derive(Clone, Serialize, Deserialize)]
struct Coin {
    hash: String,
    key: String,
}

fn order(height: u32, position: u32, index: u32) -> String {
    format!("{height:08x}{position:08x}{index:08x}")
}

fn load_coin(tree: &sled::Tree, prev: OutPoint) -> Result<Option<Coin>> {
    tree.get(format!("coin/{prev}"))
        .map_err(storage)?
        .map(|v| serde_json::from_slice(&v))
        .transpose()
        .map_err(storage)
}

pub(super) fn apply(
    owner: &Owner,
    batch: &mut sled::Batch,
    height: u32,
    block: &Block,
) -> Result<()> {
    let mut staged = HashMap::new();
    for (position, tx) in block.txdata.iter().enumerate() {
        let position = position as u32;
        let txid: Txid = tx.compute_txid();
        let mut affected = BTreeSet::new();
        for input in &tx.input {
            let prev = input.previous_output;
            let coin = match staged.remove(&prev) {
                Some(coin) => Some(coin),
                None if !prev.is_null() => load_coin(&owner.tree, prev)?,
                None => None,
            };
            if let Some(Coin { key, hash }) = coin {
                batch.remove(key.as_bytes());
                batch.remove(format!("coin/{prev}").as_bytes());
                affected.insert(hash);
            }
        }
        for (vout, output) in tx.output.iter().enumerate() {
            if !owner.watches.scripts.contains(&output.script_pubkey) {
                continue;
            }
            let hash = get_spk_hash(&output.script_pubkey).to_string();
            affected.insert(hash.clone());
            if height == 0
                || output.script_pubkey.is_op_return()
                || output.script_pubkey.len() > 10000
            {
                continue;
            }
            let vout = vout as u32;
            let prev = OutPoint::new(txid, vout);
            let key = format!("utxo/{hash}/{}", order(height, position, vout));
            let coin = Coin { hash, key };
            // Historical BIP30 duplicate coinbases overwrite an existing outpoint.
            if let Some(old) = load_coin(&owner.tree, prev)? {
                batch.remove(old.key.as_bytes());
            }
            let row = json!({ "txid": txid, "height": height, "position": position, "vout": vout, "value": output.value.to_sat() });
            batch.insert(
                coin.key.as_bytes(),
                serde_json::to_vec(&row).map_err(storage)?,
            );
            batch.insert(
                format!("coin/{prev}").as_bytes(),
                serde_json::to_vec(&coin).map_err(storage)?,
            );
            staged.insert(prev, coin);
        }
        let row =
            serde_json::to_vec(&json!({ "txid": txid, "height": height, "position": position }))
                .map_err(storage)?;
        for hash in affected {
            let key = format!("hist/{hash}/{}", order(height, position, 0));
            batch.insert(key.as_bytes(), &row[..]);
        }
    }
    Ok(())
}

pub(super) fn page(owner: &Owner, chain: &impl BlockchainInterface, query: Query) -> Result<Value> {
    let unavailable = || json!({ "phase": "unavailable" });
    let Query {
        script_hash,
        kind,
        after,
    } = query;
    if !owner_id(&script_hash)
        || after.as_ref().is_some_and(|key| {
            key.len() != 24
                || !key
                    .bytes()
                    .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
        })
    {
        return Err("Invalid confirmed script query.");
    }
    let tip = chain.get_best_block().map_err(storage)?;
    let at_tip = || {
        owner.cursor == Some(tip)
            && chain.get_best_block().ok() == Some(tip)
            && chain.get_validation_index().ok() == Some(tip.0)
            && !chain.is_in_ibd()
    };
    if owner.unavailable
        || !at_tip()
        || owner.has_missing_parents()?
        || !owner
            .tree
            .contains_key(format!("script/{script_hash}"))
            .map_err(storage)?
    {
        return Ok(unavailable());
    }
    let prefix = format!("{}/{script_hash}/", kind.prefix());
    let lower = match after {
        Some(key) => Bound::Excluded(format!("{prefix}{key}")),
        None => Bound::Included(prefix.clone()),
    };
    let mut rows = Vec::new();
    let mut last = None;
    let mut next = None;
    for item in owner
        .tree
        .range((lower, Bound::Excluded(format!("{prefix}g"))))
    {
        let (key, bytes) = item.map_err(storage)?;
        if rows.len() == PAGE {
            next = last;
            break;
        }
        let row: Value = serde_json::from_slice(&bytes).map_err(storage)?;
        rows.push(row);
        last = Some(
            std::str::from_utf8(&key[prefix.len()..])
                .map_err(storage)?
                .to_owned(),
        );
    }
    if !at_tip() {
        return Ok(unavailable());
    }
    Ok(
        json!({ "phase": "confirmed-only", "kind": kind, "scriptHash": script_hash,
        "tipHeight": tip.0, "tipHash": tip.1, "rows": rows, "next": next }),
    )
}
