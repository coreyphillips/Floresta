// SPDX-License-Identifier: MIT OR Apache-2.0

//! Bounded acquisition of proof-carrying Utreexo transactions. A candidate is untrusted
//! until the consumer verifies every input against the same locally validated chain tip.
use std::collections::{BTreeSet, HashMap, VecDeque};
use std::net::SocketAddr;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use bitcoin::consensus::encode::{deserialize_partial, Decodable, VarInt};
use bitcoin::hashes::Hash;
use bitcoin::p2p::message_blockdata::Inventory;
use bitcoin::{BlockHash, Transaction, Txid};
use floresta_chain::{CompactLeafData, ScriptPubKeyKind};
use rustreexo::{node_hash::BitcoinNodeHash, proof::Proof};

pub(crate) const MAX_BYTES: usize = 400_000;
const MAX_HELD: usize = 8 * 1024 * 1024;
const MAX_INPUTS: usize = 256;
const MAX_PENDING: usize = 64;
const MAX_SEEN: usize = 1024;
const TTL: Duration = Duration::from_secs(30);
const PROOF_HASH: u32 = 6;
const UTREEXO_TX: u32 = 0x0100_0001;
const WITNESS_UTREEXO_TX: u32 = 0x4100_0001;

#[derive(Debug)]
pub struct Candidate {
    pub peer: u32,
    pub height: u32,
    pub tip: BlockHash,
    pub tx: Transaction,
    pub proof: Proof,
    /// One entry per normalized transaction input. None must spend an independently admitted parent.
    pub leaves: Vec<Option<CompactLeafData>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Tip {
    height: u32,
    hash: BlockHash,
    leaves: u64,
}

struct Request {
    peer: u32,
    tip: Tip,
    targets: Vec<u64>,
    hashes: usize,
    needs_hint: bool,
    since: Instant,
}

struct Offer {
    tx: Transaction,
    id: Txid,
    owner_peer: Option<u32>,
    deadline: Instant,
    allowed: Arc<dyn Fn() -> bool + Send + Sync>,
    sent: std::sync::mpsc::SyncSender<()>,
}

#[derive(Default)]
struct State {
    offered: bool,
    outbound: Option<Offer>,
    tip: Option<Tip>,
    pending: HashMap<Txid, Request>,
    seen: HashMap<Txid, Instant>,
    ready: VecDeque<Candidate>,
    bytes: usize,
}

#[derive(Clone)]
pub struct Relay(Arc<Mutex<State>>, SocketAddr);

/// Authority for one connected socket. The kernel-reported destination is immutable
/// for this connection and is compared with the configured endpoint on each operation.
pub struct BoundRelay {
    relay: Relay,
    remote: SocketAddr,
}

impl BoundRelay {
    pub(crate) fn permitted(&self) -> Option<&Relay> {
        (self.remote.ip().is_loopback() && self.remote == self.relay.1).then_some(&self.relay)
    }
}

impl std::fmt::Debug for Relay {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Managed transaction intake")
    }
}

/// Return all sibling positions for a complete proof in the Utreexo wire protocol's
/// fixed 63-row forest. Each leading-one prefix identifies the row, and remaining
/// bits select the aligned leaf interval. Reject overlapping, unpopulated or duplicate
/// targets and more than 256 confirmed inputs before traversing the forest.
pub fn proof_positions(targets: &[u64], leaves: u64) -> Option<Vec<u64>> {
    if targets.len() > MAX_INPUTS || leaves >= 1 << 63 {
        return None;
    }
    let position = |index: u64, row: u32| {
        if row == 0 {
            index
        } else {
            (u64::MAX << (64 - row)) | index
        }
    };
    let mut roots = BTreeSet::new();
    let mut start = 0;
    for row in (0..63).rev() {
        let width = 1u64 << row;
        if leaves & width != 0 {
            roots.insert(position(start >> row, row));
            start += width;
        }
    }
    let mut nodes = BTreeSet::new();
    for &target in targets {
        let row = target.leading_ones();
        if row >= 63 {
            return None;
        }
        let index = target ^ position(0, row);
        if index >= (leaves >> row) || !nodes.insert(target) {
            return None;
        }
    }
    let mut hashes = Vec::new();
    while let Some(node) = nodes.pop_first() {
        if roots.contains(&node) {
            continue;
        }
        if !nodes.remove(&(node ^ 1)) {
            hashes.push(node ^ 1);
        }
        let parent = (node >> 1) | (1u64 << 63);
        if parent == node || !nodes.insert(parent) {
            return None;
        }
    }
    hashes.sort_unstable();
    Some(hashes)
}

fn txid(inv: &Inventory) -> Option<Txid> {
    match inv {
        Inventory::Transaction(id) | Inventory::WitnessTransaction(id) => Some(*id),
        Inventory::Unknown {
            inv_type: UTREEXO_TX | WITNESS_UTREEXO_TX,
            hash,
        } => Some(Txid::from_byte_array(*hash)),
        _ => None,
    }
}

fn unpack(invs: &[Inventory]) -> Option<Vec<u64>> {
    if invs.len() > MAX_INPUTS / 4 {
        return None;
    }
    let mut positions = Vec::new();
    let mut padded = false;
    for item in invs {
        let Inventory::Unknown {
            inv_type: PROOF_HASH,
            hash,
        } = item
        else {
            return None;
        };
        for bytes in hash.chunks_exact(8) {
            let p = u64::from_le_bytes(bytes.try_into().ok()?);
            if p == u64::MAX {
                padded = true;
            } else if padded {
                return None;
            } else {
                positions.push(p);
            }
        }
    }
    Some(positions)
}

fn pack(values: &[u64]) -> Vec<Inventory> {
    values
        .chunks(4)
        .map(|group| {
            let mut hash = [0xff; 32];
            for (slot, position) in hash.chunks_exact_mut(8).zip(group) {
                slot.copy_from_slice(&position.to_le_bytes());
            }
            Inventory::Unknown {
                inv_type: PROOF_HASH,
                hash,
            }
        })
        .collect()
}

fn read<T: Decodable>(bytes: &mut &[u8]) -> Option<T> {
    let (item, used) = deserialize_partial::<T>(bytes).ok()?;
    *bytes = &bytes[used..];
    Some(item)
}

fn take<'a>(bytes: &mut &'a [u8], count: usize) -> Option<&'a [u8]> {
    let chunk = bytes.get(..count)?;
    *bytes = &bytes[count..];
    Some(chunk)
}

fn count(bytes: &mut &[u8], max: usize) -> Option<usize> {
    let n = usize::try_from(read::<VarInt>(bytes)?.0).ok()?;
    (n <= max).then_some(n)
}

fn decode(mut bytes: &[u8]) -> Option<(Transaction, Proof, Vec<Option<CompactLeafData>>)> {
    if bytes.len() > MAX_BYTES {
        return None;
    }
    let n = count(&mut bytes, MAX_INPUTS)?;
    let targets = (0..n)
        .map(|_| Some(read::<VarInt>(&mut bytes)?.0))
        .collect::<Option<Vec<_>>>()?;
    let n = count(&mut bytes, MAX_INPUTS * 63)?;
    let hashes = take(&mut bytes, n.checked_mul(32)?)?
        .chunks_exact(32)
        .map(|chunk| BitcoinNodeHash::new(chunk.try_into().unwrap()))
        .collect();
    let mut tx: Transaction = read(&mut bytes)?;
    if tx.input.is_empty() || tx.input.len() > MAX_INPUTS {
        return None;
    }
    let mut leaves = Vec::with_capacity(tx.input.len());
    for input in &mut tx.input {
        let unconfirmed = input.previous_output.vout & 1 != 0;
        input.previous_output.vout >>= 1;
        leaves.push(if unconfirmed {
            None
        } else {
            let header_code = read(&mut bytes)?;
            let amount = read(&mut bytes)?;
            let spk_ty = match read::<u8>(&mut bytes)? {
                0 => {
                    let n = count(&mut bytes, 10_000)?;
                    ScriptPubKeyKind::Other(take(&mut bytes, n)?.into())
                }
                1 => ScriptPubKeyKind::PubKeyHash,
                2 => ScriptPubKeyKind::WitnessV0PubKeyHash,
                3 => ScriptPubKeyKind::ScriptHash,
                4 => ScriptPubKeyKind::WitnessV0ScriptHash,
                _ => return None,
            };
            Some(CompactLeafData {
                header_code,
                amount,
                spk_ty,
            })
        });
    }
    if !bytes.is_empty() || leaves.iter().flatten().count() != targets.len() {
        return None;
    }
    Some((tx, Proof::new(targets, hashes), leaves))
}

/// Network actions remain separate from candidate admission.
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum Intake {
    Dropped,
    Queued,
    Request(Vec<Inventory>),
}

impl Relay {
    /// Only the explicitly selected, local regtest qualification endpoint may receive
    /// proof-transaction traffic. All ordinary peer and network configurations remain block-only.
    pub fn for_config(
        managed: bool,
        network: bitcoin::Network,
        fixed: Option<&str>,
        proxied: bool,
    ) -> Option<Self> {
        if !managed || network != bitcoin::Network::Regtest || proxied {
            return None;
        }
        let endpoint: SocketAddr = fixed?.parse().ok()?;
        if !endpoint.ip().is_loopback() || endpoint.port() == 0 {
            return None;
        }
        Some(Self(Arc::default(), endpoint))
    }

    pub(crate) fn bind(
        &self,
        network: bitcoin::Network,
        remote: Option<SocketAddr>,
    ) -> Option<BoundRelay> {
        if network != bitcoin::Network::Regtest {
            return None;
        }
        let bound = BoundRelay {
            relay: self.clone(),
            remote: remote?,
        };
        bound.permitted()?;
        Some(bound)
    }

    pub(crate) fn tip(&self, tip: Option<(u32, BlockHash, u64)>) {
        let tip = tip.map(|(height, hash, leaves)| Tip {
            height,
            hash,
            leaves,
        });
        let mut state = self.0.lock().unwrap();
        if state.tip != tip {
            *state = State {
                tip,
                ..Default::default()
            };
        }
    }

    // One authorized outgoing offer per distinct active tip. A lost reply or
    // timeout never retries it. Its bytes never enter a shared peer mempool.
    pub(crate) fn offer(&self, tip: BlockHash, tx: Transaction, allowed: Arc<dyn Fn() -> bool + Send + Sync>)
        -> Option<std::sync::mpsc::Receiver<()>> {
        let mut state = self.0.lock().ok()?;
        if state.tip?.hash != tip || state.offered { return None; }
        let (sent, receipt) = std::sync::mpsc::sync_channel(1);
        state.offered = true;
        state.outbound = Some(Offer { id: tx.compute_txid(), tx, allowed, sent, owner_peer: None,
            deadline: Instant::now() + Duration::from_secs(7) });
        Some(receipt)
    }

    pub(crate) fn announcement(&self, peer: u32) -> Option<Txid> {
        let mut state = self.0.lock().ok()?;
        let offer = state.outbound.as_mut()?;
        if offer.owner_peer.is_some() || Instant::now() > offer.deadline { return None; }
        offer.owner_peer = Some(peer);
        let (id, allowed) = (offer.id, offer.allowed.clone());
        drop(state);
        allowed().then_some(id)
    }

    pub(crate) fn fulfill(&self, peer: u32, id: Txid) -> Option<(Transaction, std::sync::mpsc::SyncSender<()>)> {
        let mut state = self.0.lock().ok()?;
        let offer = state.outbound.as_ref()?;
        if offer.owner_peer != Some(peer) || offer.id != id || Instant::now() > offer.deadline { return None; }
        let offer = state.outbound.take()?;
        drop(state);
        (offer.allowed)().then_some((offer.tx, offer.sent))
    }

    pub(crate) fn active_tip(&self) -> Option<BlockHash> {
        self.0.lock().unwrap().tip.map(|tip| tip.hash)
    }

    pub(crate) fn requests(&self, peer: u32, invs: &[Inventory]) -> Vec<Inventory> {
        let mut state = self.0.lock().unwrap();
        let Some(tip) = state.tip else {
            return vec![];
        };
        let now = Instant::now();
        state
            .pending
            .retain(|_, r| now.duration_since(r.since) < TTL);
        state.seen.retain(|_, t| now.duration_since(*t) < TTL);
        let mut out = Vec::new();
        let mut iter = invs.iter().enumerate().peekable();
        while let Some((i, item)) = iter.next() {
            let Some(id) = txid(item) else {
                continue;
            };
            let mut end = i + 1;
            while iter
                .next_if(|(_, item)| {
                    matches!(
                        item,
                        Inventory::Unknown {
                            inv_type: PROOF_HASH,
                            ..
                        }
                    )
                })
                .is_some()
            {
                end += 1;
            }
            if state.pending.len() >= MAX_PENDING || state.seen.len() >= MAX_SEEN {
                break;
            }
            if state.seen.contains_key(&id) {
                continue;
            }
            let Some(targets) = unpack(&invs[i + 1..end]) else {
                continue;
            };
            let Some(positions) = proof_positions(&targets, tip.leaves) else {
                continue;
            };
            let packed = pack(&positions);
            if out.len() + 1 + packed.len() > 4096 {
                break;
            }
            state.pending.insert(
                id,
                Request {
                    peer,
                    tip,
                    needs_hint: targets.is_empty(),
                    targets,
                    hashes: positions.len(),
                    since: now,
                },
            );
            state.seen.insert(id, now);
            out.push(Inventory::Unknown {
                inv_type: WITNESS_UTREEXO_TX,
                hash: id.to_byte_array(),
            });
            out.extend(packed);
        }
        out
    }

    pub(crate) fn receive(&self, peer: u32, bytes: &[u8]) -> Intake {
        {
            let state = self.0.lock().unwrap();
            if bytes.len() > MAX_BYTES
                || !state
                    .pending
                    .values()
                    .any(|r| r.peer == peer && r.since.elapsed() < TTL)
            {
                return Intake::Dropped;
            }
        }
        let Some((tx, proof, leaves)) = decode(bytes) else {
            return Intake::Dropped;
        };
        let mut state = self.0.lock().unwrap();
        let id = tx.compute_txid();
        let Some(req) = state.pending.get(&id) else {
            return Intake::Dropped;
        };
        if req.peer != peer || Some(req.tip) != state.tip || req.since.elapsed() >= TTL {
            return Intake::Dropped;
        }
        if req.needs_hint && !proof.targets.is_empty() {
            // MEMPOOL replies omit the packed target positions. The first GETDATA can
            // reveal them but cannot establish inclusion. Request the full sibling set
            // for those positions under the same tip and transaction identity.
            if !proof.hashes.is_empty() {
                return Intake::Dropped;
            }
            let Some(positions) = proof_positions(&proof.targets, req.tip.leaves) else {
                return Intake::Dropped;
            };
            if !positions.is_empty() {
                let request = state.pending.get_mut(&id).unwrap();
                request.targets = proof.targets;
                request.hashes = positions.len();
                request.needs_hint = false;
                let mut inv = vec![Inventory::Unknown {
                    inv_type: WITNESS_UTREEXO_TX,
                    hash: id.to_byte_array(),
                }];
                inv.extend(pack(&positions));
                return Intake::Request(inv);
            }
            // A complete proof can contain no sibling hashes when all targets are roots.
        } else if req.targets != proof.targets || req.hashes != proof.hashes.len() {
            return Intake::Dropped;
        }
        let tip = req.tip;
        state.pending.remove(&id);
        if state.bytes + bytes.len() > MAX_HELD || state.ready.len() >= MAX_PENDING {
            return Intake::Dropped;
        }
        state.bytes += bytes.len();
        state.ready.push_back(Candidate {
            peer,
            height: tip.height,
            tip: tip.hash,
            tx,
            proof,
            leaves,
        });
        Intake::Queued
    }

    pub(crate) fn drain(&self) -> Vec<Candidate> {
        let mut state = self.0.lock().unwrap();
        state.bytes = 0;
        state.ready.drain(..).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bitcoin::hex::FromHex;

    #[test]
    fn wallet_offers_are_one_use_and_private_to_the_exact_connected_fixture_peer_and_tip() {
        let relay = test_relay();
        let genesis = bitcoin::blockdata::constants::genesis_block(bitcoin::Network::Regtest);
        let tip = genesis.block_hash();
        let tx = genesis.txdata[0].clone();
        let id = tx.compute_txid();
        relay.tip(Some((101, tip, 101)));
        assert!(relay.bind(bitcoin::Network::Regtest, Some("127.0.0.1:18445".parse().unwrap())).is_none());
        assert!(relay.bind(bitcoin::Network::Bitcoin, Some("127.0.0.1:18444".parse().unwrap())).is_none());
        let receipt = relay.offer(tip, tx.clone(), Arc::new(|| true)).unwrap();
        assert!(relay.fulfill(1, id).is_none());
        assert_eq!(relay.announcement(1), Some(id));
        assert!(relay.announcement(2).is_none());
        assert!(relay.fulfill(2, id).is_none());
        let (delivered, ack) = relay.fulfill(1, id).unwrap();
        assert_eq!(delivered, tx);
        ack.try_send(()).unwrap();
        assert!(receipt.try_recv().is_ok());
        assert!(relay.offer(tip, tx.clone(), Arc::new(|| true)).is_none());
        let other = BlockHash::all_zeros();
        relay.tip(Some((102, other, 102)));
        assert!(relay.offer(tip, tx.clone(), Arc::new(|| true)).is_none());
        let permitted = Arc::new(std::sync::atomic::AtomicBool::new(true));
        let live = permitted.clone();
        let receipt = relay.offer(other, tx, Arc::new(move || live.load(std::sync::atomic::Ordering::Acquire))).unwrap();
        assert_eq!(relay.announcement(1), Some(id));
        permitted.store(false, std::sync::atomic::Ordering::Release);
        assert!(relay.fulfill(1,id).is_none());
        assert!(receipt.try_recv().is_err());
    }

    fn test_relay() -> Relay {
        Relay::for_config(
            true,
            bitcoin::Network::Regtest,
            Some("127.0.0.1:18444"),
            false,
        )
        .unwrap()
    }

    #[test]
    fn qualification_requires_managed_regtest_and_exact_direct_socket() {
        use bitcoin::Network;
        let local = Some("127.0.0.1:18444");
        for network in [
            Network::Bitcoin,
            Network::Testnet,
            Network::Testnet4,
            Network::Signet,
        ] {
            assert!(Relay::for_config(true, network, local, false).is_none());
        }
        assert!(Relay::for_config(false, Network::Regtest, local, false).is_none());
        assert!(Relay::for_config(true, Network::Regtest, local, true).is_none());
        for endpoint in [
            None,
            Some("127.0.0.1:0"),
            Some("localhost:18444"),
            Some("192.0.2.1:18444"),
            Some("[::]:18444"),
        ] {
            assert!(Relay::for_config(true, Network::Regtest, endpoint, false).is_none());
        }
        let relay = test_relay();
        assert!(relay.bind(Network::Regtest, None).is_none());
        for endpoint in [
            "127.0.0.1:18445",
            "127.0.0.2:18444",
            "192.0.2.1:18444",
            "[::1]:18444",
        ] {
            assert!(relay
                .bind(Network::Regtest, Some(endpoint.parse().unwrap()))
                .is_none());
        }
        let actual = Some("127.0.0.1:18444".parse().unwrap());
        assert!(relay.bind(Network::Bitcoin, actual).is_none());
        assert!(relay
            .bind(Network::Regtest, actual)
            .unwrap()
            .permitted()
            .is_some());
    }
    // Captured from the v0.6.0 bridge after a funded regtest transaction spent leaf 0 at 101.
    const PAYLOAD: &str = "01000634b828cedf38ed3e9d8fba739af97affc2d0bd465971bf1085c84c47e8a4df7d4fe3af0c4bf72ffcc2214b01dbe2cd8b5038809f033e8db5dbb730542cb29cc7945f415cfb20472581186b48218ed22a0a0f8823625ae84b4defb81372058769f15395c44fa1a63da6f38d884659f3fdfff0c10c818065914c4fedcb05a2c4ceb3c9cf7f319f67ea72164c0ec7e703a9d5efde62e97e853d58c78cd3308061db18b91b96fae6362914b39449f154d0d05df0a482cf8883ee757fc73bc38d67430100000001bbfa4bc8a83cf9d4f647ae5c65b86b6514b9c63deef411dba1e060c2516f6c2400000000020151fdffffff03e026052a0100000017a914da1745e9b549bd0bfa1a569971c77eba30cd5a4b87e80300000000000017a914da1745e9b549bd0bfa1a569971c77eba30cd5a4b8750c3000000000000220020dbeda1256f5e8b945ea986a7501758010dd85225901a2d531013f4c516824013000000000300000000f2052a0100000003";
    const TXID: &str = "bb89170c9e2f2db83d1f248fff2906beb22ba8055a6b935ed7b5045c08333858";

    #[test]
    fn bridge_response_requires_peer_request_and_exact_active_tip() {
        let wire = Vec::<u8>::from_hex(PAYLOAD).unwrap();
        let relay = test_relay();
        let tip = BlockHash::all_zeros();
        let id = TXID.parse().unwrap();
        let mut announcements = vec![Inventory::Transaction(id)];
        announcements.extend(pack(&[0]));
        assert_eq!(relay.receive(1, &wire), Intake::Dropped);
        relay.tip(Some((101, tip, 101)));
        let requested = relay.requests(1, &announcements);
        assert_eq!(requested.len(), 3);
        assert_eq!(
            unpack(&requested[1..]).unwrap(),
            vec![
                1,
                9223372036854775809,
                13835058055282163713,
                16140901064495857665,
                17293822569102704641,
                17870283321406128129
            ]
        );
        assert!(relay.requests(2, &announcements).is_empty());
        assert_eq!(relay.receive(2, &wire), Intake::Dropped);
        let mut malformed = wire.clone();
        malformed.push(0);
        assert_eq!(relay.receive(1, &malformed), Intake::Dropped);
        assert_eq!(relay.receive(1, &wire), Intake::Queued);
        assert_eq!(relay.receive(1, &wire), Intake::Dropped);
        let result = relay.drain().pop().unwrap();
        assert_eq!(
            (
                result.peer,
                result.height,
                result.tip,
                result.tx.compute_txid()
            ),
            (1, 101, tip, id)
        );
        assert_eq!(result.proof.targets, vec![0]);
        assert_eq!(result.proof.hashes.len(), 6);
        let leaf = result.leaves[0].as_ref().unwrap();
        assert_eq!((leaf.header_code, leaf.amount), (3, 5_000_000_000));
        assert_eq!(leaf.spk_ty, ScriptPubKeyKind::ScriptHash);
        relay.tip(Some((102, tip, 105)));
        assert_eq!(relay.receive(1, &wire), Intake::Dropped);
    }

    #[test]
    fn cold_inventory_requests_target_hints_then_full_inclusion() {
        let wire = Vec::<u8>::from_hex(PAYLOAD).unwrap();
        let relay = test_relay();
        relay.tip(Some((101, BlockHash::all_zeros(), 101)));
        let request = relay.requests(1, &[Inventory::Transaction(TXID.parse().unwrap())]);
        assert_eq!(request.len(), 1);
        let mut hint = vec![1, 0, 0]; // one target at position zero and no sibling hashes
        hint.extend_from_slice(&wire[3 + 6 * 32..]);
        let Intake::Request(second) = relay.receive(1, &hint) else {
            panic!("missing second proof request");
        };
        assert_eq!(second.len(), 3);
        assert_eq!(relay.receive(1, &hint), Intake::Dropped);
        assert!(relay.drain().is_empty());
        assert_eq!(relay.receive(1, &wire), Intake::Queued);
        assert_eq!(relay.drain().len(), 1);
    }

    #[test]
    fn position_bounds_and_unconfirmed_input_encoding() {
        assert_eq!(proof_positions(&[0, 1], 2), Some(vec![]));
        assert_eq!(proof_positions(&[0, 2], 4), Some(vec![1, 3]));
        assert_eq!(proof_positions(&[1 << 63], 2), Some(vec![]));
        assert_eq!(proof_positions(&[0, 1 << 63], 2), None);
        assert_eq!(proof_positions(&[2], 2), None);
        assert_eq!(proof_positions(&[0, 0], 2), None);
        let wire = Vec::<u8>::from_hex(PAYLOAD).unwrap();
        let (mut tx, _, _) = decode(&wire).unwrap();
        // An unconfirmed parent at vout 4 is carried as 9 with no leaf or proof.
        tx.input[0].previous_output.vout = 9;
        let mut bytes = vec![0, 0];
        bytes.extend(bitcoin::consensus::serialize(&tx));
        let (normalized, proof, leaves) = decode(&bytes).unwrap();
        assert_eq!(normalized.input[0].previous_output.vout, 4);
        assert_eq!(proof.targets.len(), 0);
        assert_eq!(leaves, vec![None]);
        let bad_padding = Inventory::Unknown {
            inv_type: PROOF_HASH,
            hash: [0xff; 32],
        };
        assert!(unpack(&[bad_padding, pack(&[0]).remove(0)]).is_none());
        assert!(decode(&wire[..wire.len() - 1]).is_none());
    }
}
