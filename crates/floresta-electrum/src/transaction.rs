// SPDX-License-Identifier: MIT OR Apache-2.0

use bitcoin::block::Header;
use bitcoin::consensus::encode::serialize_hex;
use bitcoin::hex::DisplayHex;
use bitcoin::{Address, Network, Transaction};
use floresta_chain::pruned_utreexo::BlockchainInterface;
use floresta_watch_only::merkle::MerkleProof;
use floresta_watch_only::CachedTransaction;
use serde_json::{json, Value};

use crate::error::Error;

pub(super) fn verbose<C: BlockchainInterface>(
    record: &CachedTransaction,
    chain: &C,
) -> Result<Value, Error> {
    let mut result = decode(&record.tx, chain.get_params().network);
    if record.height > 0 {
        let height = chain
            .get_validation_index()
            .map_err(|e| Error::Blockchain(Box::new(e)))?;
        let (_, header) = active_proof(record, chain)?;
        add_confirmation(&mut result, record.height, &header, height)?;
    }
    Ok(result)
}

pub(super) fn active_proof<'a, C: BlockchainInterface>(
    record: &'a CachedTransaction,
    chain: &C,
) -> Result<(&'a MerkleProof, Header), Error> {
    let hash = chain
        .get_block_hash(record.height)
        .map_err(|e| Error::Blockchain(Box::new(e)))?;
    let header = chain
        .get_block_header(&hash)
        .map_err(|e| Error::Blockchain(Box::new(e)))?;
    Ok((verify_branch(record, &header)?, header))
}

fn verify_branch<'a>(
    record: &'a CachedTransaction,
    header: &Header,
) -> Result<&'a MerkleProof, Error> {
    let proof = record
        .merkle_block
        .as_ref()
        .ok_or(Error::HistoryUnavailable)?;
    // The active header at a cached height can change after a reorg.
    if record.height == 0
        || proof.target != record.tx.compute_txid()
        || !proof
            .verify(*header.merkle_root.as_raw_hash())
            .unwrap_or(false)
    {
        return Err(Error::HistoryUnavailable);
    }
    Ok(proof)
}

fn add_confirmation(
    result: &mut Value,
    height: u32,
    header: &Header,
    tip: u32,
) -> Result<(), Error> {
    if height > tip {
        return Err(Error::HistoryUnavailable);
    }
    result["blockhash"] = json!(header.block_hash());
    result["blocktime"] = json!(header.time);
    result["time"] = json!(header.time);
    result["confirmations"] = json!(tip - height + 1);
    Ok(())
}

fn decode(tx: &Transaction, network: Network) -> Value {
    let vin: Vec<_> = tx.input.iter().map(|input| {
        let mut value = if tx.is_coinbase() {
            json!({ "coinbase": input.script_sig.to_hex_string() })
        } else {
            json!({
                "txid": input.previous_output.txid,
                "vout": input.previous_output.vout,
                "scriptSig": { "asm": input.script_sig.to_asm_string(), "hex": input.script_sig.to_hex_string() }
            })
        };
        value["sequence"] = json!(input.sequence.to_consensus_u32());
        if !input.witness.is_empty() {
            let witness: Vec<_> = input.witness.iter().map(|item| item.to_lower_hex_string()).collect();
            value["txinwitness"] = json!(witness);
        }
        value
    }).collect();
    let vout: Vec<_> = tx.output.iter().enumerate().map(|(n, output)| {
        let mut script = json!({ "asm": output.script_pubkey.to_asm_string(), "hex": output.script_pubkey.to_hex_string() });
        if let Ok(address) = Address::from_script(&output.script_pubkey, network) {
            script["address"] = json!(address.to_string());
        }
        json!({ "n": n, "value": output.value.to_btc(), "scriptPubKey": script })
    }).collect();
    json!({
        "hex": serialize_hex(tx), "txid": tx.compute_txid(), "hash": tx.compute_wtxid(),
        "version": tx.version.0, "size": tx.total_size(), "vsize": tx.vsize(),
        "weight": tx.weight().to_wu(), "locktime": tx.lock_time.to_consensus_u32(),
        "vin": vin, "vout": vout, "confirmations": 0
    })
}

#[cfg(test)]
mod tests {
    use bitcoin::blockdata::constants::genesis_block;
    use bitcoin::hashes::Hash;
    use bitcoin::TxMerkleNode;
    use floresta_watch_only::merkle::MerkleProof;

    use super::*;

    #[test]
    fn verbose_coinbase_uses_btc_amounts_and_only_reports_a_proven_confirmation() {
        let block = genesis_block(Network::Regtest);
        let tx = block.txdata[0].clone();
        let record = CachedTransaction {
            hash: tx.compute_txid(),
            height: 100,
            position: 0,
            merkle_block: Some(MerkleProof::from_block(&block, 0)),
            tx,
        };
        let mut decoded = decode(&record.tx, Network::Regtest);
        assert_eq!(
            decoded["vin"][0]["coinbase"],
            record.tx.input[0].script_sig.to_hex_string()
        );
        assert_eq!(decoded["vout"][0]["value"], 50.0);
        assert_eq!(decoded["vsize"], record.tx.vsize());
        assert_eq!(decoded["confirmations"], 0);
        assert!(decoded.get("blockhash").is_none());

        let mut alternate_header = block.header;
        alternate_header.merkle_root = TxMerkleNode::all_zeros();
        assert!(verify_branch(&record, &alternate_header).is_err());
        assert!(add_confirmation(&mut decoded, record.height, &block.header, 99).is_err());
        assert!(verify_branch(&record, &block.header).is_ok());
        add_confirmation(&mut decoded, record.height, &block.header, 102).unwrap();
        assert_eq!(decoded["confirmations"], 3);
        assert_eq!(decoded["blockhash"], block.header.block_hash().to_string());
    }
}
