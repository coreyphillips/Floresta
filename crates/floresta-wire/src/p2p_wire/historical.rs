// SPDX-License-Identifier: MIT OR Apache-2.0

//! Managed replay checkpoints are private to the directory locked by the daemon.
//! Legacy .sync_node_state files cannot establish or advance historical verification.
use std::fs::File;
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

use bitcoin::hashes::{sha256, Hash, HashEngine, Hmac, HmacEngine};
use bitcoin::{BlockHash, Network};
use floresta_chain::{AssumeUtreexoValue, ChainParams};
use rand::{rngs::OsRng, RngCore};
use rustreexo::stump::Stump;
use serde::{Deserialize, Serialize};
use tempfile::Builder;

#[derive(Clone, Debug, Serialize)]
pub struct Progress {
    state: &'static str,
    height: u32,
    target: u32,
    #[serde(skip_serializing_if = "Option::is_none")]
    error: Option<String>,
    #[serde(rename = "checkpointEligible")]
    checkpoint_eligible: bool,
    #[serde(rename = "checkpointHold", skip_serializing_if = "Option::is_none")]
    checkpoint_hold: Option<&'static str>,
    #[serde(skip)]
    reserved_at: Option<u32>,
    #[serde(skip)]
    anchor: Option<BlockHash>,
}

impl Default for Progress {
    fn default() -> Self {
        Self {
            state: "pending",
            height: 0,
            target: 0,
            error: None,
            checkpoint_eligible: false,
            checkpoint_hold: None,
            reserved_at: None,
            anchor: None,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct Historical(Arc<Mutex<Progress>>);

impl Historical {
    pub(crate) fn begin(&self, height: u32, anchor: &AssumeUtreexoValue, admission: Admission) {
        *self.0.lock().unwrap() = Progress {
            state: "verifying",
            height,
            target: anchor.height,
            error: None,
            checkpoint_eligible: false,
            reserved_at: (admission == Admission::Reserved).then_some(height),
            checkpoint_hold: match admission {
                Admission::Interrupted => Some("independent-replay-required"),
                Admission::Mismatch => Some("previous-accumulator-mismatch"),
                _ => None,
            },
            anchor: Some(anchor.block_hash),
        };
    }

    pub fn target(&self) -> Option<u32> {
        let progress = self.0.lock().unwrap();
        progress.anchor.map(|_| progress.target)
    }

    pub(crate) fn completed_anchor(&self) -> Option<(u32, BlockHash)> {
        let progress = self.0.lock().unwrap();
        if progress.state == "verified" && progress.height == progress.target {
            return Some((progress.target, progress.anchor?));
        }
        None
    }

    pub(crate) fn failed(&self) -> bool {
        self.0.lock().unwrap().state == "error"
    }

    pub(crate) fn advance(&self, height: u32) {
        let mut progress = self.0.lock().unwrap();
        progress.height = height;
        progress.checkpoint_eligible = progress.state == "verifying"
            && height < progress.target
            && progress.reserved_at.is_some_and(|start| height > start);
    }

    pub(crate) fn verified(&self) {
        let mut progress = self.0.lock().unwrap();
        progress.state = "verified";
        progress.checkpoint_eligible = false;
        progress.checkpoint_hold = None;
    }

    pub(crate) fn fail(&self, message: &str) {
        let mut state = self.0.lock().unwrap();
        state.checkpoint_eligible = false;
        state.state = "error";
        state.error = Some(message.to_owned());
    }

    pub fn snapshot(
        &self,
        tip: u32,
        validated: u32,
        ibd: bool,
        hash: impl FnOnce(u32) -> Option<BlockHash>,
    ) -> Progress {
        let mut result = self.0.lock().unwrap().clone();
        if result.state == "verified" || result.checkpoint_eligible {
            let current = !ibd && tip == validated && result.target <= tip;
            if result.target > tip || hash(result.target) != result.anchor {
                result.checkpoint_eligible = false;
                result.state = "error";
                result.error = Some("Historical anchor left the active chain".to_owned());
            } else if !current {
                result.checkpoint_eligible = false;
                result.state = "verifying";
            }
        }
        result
    }
}

const KEY_FILE: &str = "chicory-backfill-v1.key";
const STATE_FILE: &str = "chicory-backfill-v1.state";
const FENCE_FILE: &str = "chicory-checkpoint-fence-v1";

// Ready exists only after clean interruption, or after independently proven completion.
// A durable reservation makes an unexpected exit conservative across process boundaries.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Fence {
    Ready = 1,
    Reserved = 2,
    Mismatch = 3,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Admission {
    StrictOnly,
    Reserved,
    Interrupted,
    Mismatch,
}
impl Admission {
    pub(crate) fn requires_replay(self) -> bool {
        matches!(self, Self::Interrupted | Self::Mismatch)
    }
}
const MAX_RECORD: usize = 16384;
const MAC_SIZE: usize = 32;

fn invalid(message: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}

fn read_bounded(path: &Path, max: usize) -> io::Result<Vec<u8>> {
    let mut bytes = Vec::new();
    File::open(path)?
        .take(max as u64 + 1)
        .read_to_end(&mut bytes)?;
    if bytes.len() > max {
        return Err(invalid("Oversized historical checkpoint"));
    }
    Ok(bytes)
}

fn save(path: &Path, bytes: &[u8]) -> io::Result<()> {
    let dir = path
        .parent()
        .ok_or_else(|| invalid("Missing checkpoint directory"))?;
    let name = path
        .file_name()
        .ok_or_else(|| invalid("Missing checkpoint filename"))?;
    let mut staging = name.to_os_string();
    staging.push(".tmp");
    // The daemon holds the data directory lock. Only an interrupted previous write may
    // have left this exact staging pathname. Removing a symlink never follows its target.
    match std::fs::remove_file(dir.join(&staging)) {
        Ok(()) => {}
        Err(error) if error.kind() == io::ErrorKind::NotFound => {}
        Err(error) => return Err(error),
    }
    let mut file = Builder::new()
        .prefix(&staging)
        .rand_bytes(0)
        .tempfile_in(dir)?;
    file.write_all(bytes)?;
    file.as_file().sync_all()?;
    file.persist(path)?;
    #[cfg(unix)]
    File::open(dir)?.sync_all()?;
    Ok(())
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Record {
    version: u8,
    target: u32,
    anchor: [u8; 32],
    height: u32,
    hash: [u8; 32],
    complete: bool,
    stump: Vec<u8>,
}

fn encode_stump(stump: &Stump) -> io::Result<Vec<u8>> {
    if stump.roots.len() != stump.leaves.count_ones() as usize {
        return Err(invalid("Invalid accumulator root count"));
    }
    let mut bytes = Vec::new();
    stump
        .serialize(&mut bytes)
        .map_err(|_| invalid("Invalid accumulator"))?;
    Ok(bytes)
}

#[derive(Clone)]
pub(crate) struct Checkpoint {
    path: PathBuf,
    key: [u8; MAC_SIZE],
    pub anchor: AssumeUtreexoValue,
    moving_target: bool,
    mainnet_pin: bool,
    new_key: bool,
}

// NodeContext requires Debug. Keep the integrity key out of logs.
impl std::fmt::Debug for Checkpoint {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt.debug_struct("Checkpoint")
            .field("target", &self.anchor.height)
            .finish()
    }
}

impl Checkpoint {
    pub(crate) fn open(
        dir: &Path,
        network: Network,
        anchor: AssumeUtreexoValue,
    ) -> io::Result<Self> {
        let key_path = dir.join(KEY_FILE);
        let (key, new_key): ([u8; MAC_SIZE], bool) = match read_bounded(&key_path, MAC_SIZE) {
            Ok(bytes) => (
                bytes
                    .try_into()
                    .map_err(|_| invalid("Invalid historical checkpoint key"))?,
                false,
            ),
            Err(error) if error.kind() == io::ErrorKind::NotFound => {
                let mut key = [0; MAC_SIZE];
                OsRng.try_fill_bytes(&mut key).map_err(io::Error::other)?;
                save(&key_path, &key)?;
                (key, true)
            }
            Err(error) => return Err(error),
        };
        // Bind the unchanged record layout to the network, consensus policy and
        // released assumption. Old unbound records trigger a full replay.
        let pin = ChainParams::get_assume_utreexo(network);
        let mainnet_pin = network == Network::Bitcoin
            && floresta_chain::SCRIPT_KERNEL_ENABLED
            && anchor.height == pin.height
            && anchor.block_hash == pin.block_hash
            && anchor.leaves == pin.leaves
            && anchor.roots == pin.roots;
        let mut domain = HmacEngine::<sha256::Hash>::new(&key);
        domain.input(b"chicory.full-script-replay/2");
        domain.input(&network.magic().to_bytes());
        domain.input(&[u8::from(floresta_chain::SCRIPT_KERNEL_ENABLED)]);
        domain.input(&pin.height.to_le_bytes());
        domain.input(pin.block_hash.as_byte_array());
        domain.input(&encode_stump(&Stump {
            roots: pin.roots,
            leaves: pin.leaves,
        })?);
        Ok(Self {
            path: dir.join(STATE_FILE),
            key: Hmac::from_engine(domain).to_byte_array(),
            anchor,
            moving_target: pin.height == 0,
            mainnet_pin,
            new_key,
        })
    }

    fn tag(&self, bytes: &[u8]) -> [u8; MAC_SIZE] {
        let mut engine = HmacEngine::<sha256::Hash>::new(&self.key);
        engine.input(bytes);
        Hmac::from_engine(engine).to_byte_array()
    }

    fn fence_tag(&self, state: u8) -> [u8; MAC_SIZE] {
        let mut domain = HmacEngine::<sha256::Hash>::new(&self.key);
        domain.input(b"chicory.assumed-checkpoint/1");
        domain.input(&[state]);
        Hmac::from_engine(domain).to_byte_array()
    }

    fn read_fence(&self, fresh_chain: bool) -> Option<Fence> {
        let bytes = match read_bounded(&self.path.with_file_name(FENCE_FILE), MAC_SIZE + 1) {
            Ok(bytes) => bytes,
            Err(e) if e.kind() == io::ErrorKind::NotFound && fresh_chain && self.new_key => {
                return Some(Fence::Ready)
            }
            Err(_) => return None,
        };
        let (&value, tag) = bytes.split_first()?;
        if tag != self.fence_tag(value) {
            return None;
        }
        match value {
            1 => Some(Fence::Ready),
            2 => Some(Fence::Reserved),
            3 => Some(Fence::Mismatch),
            _ => None,
        }
    }

    pub(crate) fn fence(&self, state: Fence) -> io::Result<()> {
        if !self.mainnet_pin {
            return Ok(());
        }
        let mut bytes = vec![state as u8];
        bytes.extend(self.fence_tag(state as u8));
        save(&self.path.with_file_name(FENCE_FILE), &bytes)
    }

    pub(crate) fn reserve(
        &self,
        fresh_chain: bool,
        progress_intact: bool,
        complete: bool,
    ) -> io::Result<Admission> {
        if !self.mainnet_pin {
            return Ok(Admission::StrictOnly);
        }
        let previous = self.read_fence(fresh_chain);
        if previous == Some(Fence::Mismatch) {
            return Ok(Admission::Mismatch);
        }
        let allowed = previous == Some(Fence::Ready) && progress_intact;
        if allowed && complete {
            return Ok(Admission::StrictOnly);
        }
        // Write and sync before granting *any* provisional authority or examining
        // another candidate that might disprove the pin. An interrupted update is held.
        self.fence(Fence::Reserved)?;
        Ok(if allowed {
            Admission::Reserved
        } else {
            Admission::Interrupted
        })
    }

    /// The complete replay must name the selected header before a different
    /// accumulator can establish a contradiction. Peer or storage errors cannot.
    pub(crate) fn check_replayed_anchor(
        &self,
        height: u32,
        hash: BlockHash,
        active: Option<BlockHash>,
        stump: &Stump,
    ) -> io::Result<()> {
        if height != self.anchor.height || hash != self.anchor.block_hash || active != Some(hash) {
            return Err(invalid(
                "Active header differs from the historical replay target",
            ));
        }
        if !self.matches(stump) {
            self.fence(Fence::Mismatch)?;
            return Err(invalid(
                "Independently replayed accumulator differs from the active historical anchor",
            ));
        }
        Ok(())
    }

    pub(crate) fn matches(&self, stump: &Stump) -> bool {
        self.anchor.leaves == stump.leaves && self.anchor.roots == stump.roots
    }

    pub(crate) fn store(
        &self,
        height: u32,
        hash: BlockHash,
        stump: &Stump,
        complete: bool,
    ) -> io::Result<()> {
        if height > self.anchor.height
            || (height == self.anchor.height
                && (hash != self.anchor.block_hash || !self.matches(stump)))
            || (complete && height != self.anchor.height)
        {
            return Err(invalid(
                "Historical checkpoint differs from the selected anchor",
            ));
        }
        let record = Record {
            version: 1,
            target: self.anchor.height,
            anchor: self.anchor.block_hash.to_byte_array(),
            height,
            hash: hash.to_byte_array(),
            complete,
            stump: encode_stump(stump)?,
        };
        let bytes = serde_json::to_vec(&record)?;
        let mut signed = self.tag(&bytes).to_vec();
        signed.extend(bytes);
        save(&self.path, &signed)
    }

    pub(crate) fn recover(
        &self,
        hash_at: impl FnOnce(u32) -> Option<BlockHash>,
    ) -> io::Result<(u32, Stump, bool)> {
        let bytes = match read_bounded(&self.path, MAX_RECORD) {
            Ok(bytes) => bytes,
            Err(error) if error.kind() == io::ErrorKind::NotFound => {
                return Ok((0, Stump::default(), false))
            }
            Err(error) => return Err(error),
        };
        if bytes.len() <= MAC_SIZE || self.tag(&bytes[MAC_SIZE..]) != bytes[..MAC_SIZE] {
            return Err(invalid("Invalid historical checkpoint integrity tag"));
        }
        let record: Record = serde_json::from_slice(&bytes[MAC_SIZE..])?;
        let same_target = record.target == self.anchor.height
            && record.anchor == self.anchor.block_hash.to_byte_array();
        // A completed older target authenticates only its own prefix. Incomplete
        // or detached targets cannot be moved, and a released pin is immutable.
        let prefix = self.moving_target && record.complete && record.target < self.anchor.height;
        if record.version != 1
            || !(same_target || prefix)
            || record.height > record.target
            || hash_at(record.height) != Some(BlockHash::from_byte_array(record.hash))
            || (record.complete && record.height != record.target)
            || (record.height == record.target && record.hash != record.anchor)
        {
            return Err(invalid(
                "Historical checkpoint does not match the selected chain",
            ));
        }
        // Check declared root count before handing any bytes to the accumulator decoder.
        let header = record
            .stump
            .get(..16)
            .ok_or_else(|| invalid("Missing accumulator header"))?;
        let leaves = u64::from_le_bytes(header[..8].try_into().unwrap());
        let roots = u64::from_le_bytes(header[8..].try_into().unwrap());
        if roots != u64::from(leaves.count_ones()) || record.stump.len() > 16 + 64 * 33 {
            return Err(invalid("Invalid historical accumulator dimensions"));
        }
        let stump = Stump::deserialize(record.stump.as_slice())
            .map_err(|_| invalid("Invalid accumulator"))?;
        if encode_stump(&stump)? != record.stump
            || (same_target && record.height == record.target && !self.matches(&stump))
        {
            return Err(invalid("Historical accumulator mismatch"));
        }
        Ok((record.height, stump, same_target && record.complete))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustreexo::node_hash::BitcoinNodeHash;

    fn anchor() -> AssumeUtreexoValue {
        let mut anchor = ChainParams::get_assume_utreexo(Network::Regtest);
        anchor.height = 2;
        anchor.leaves = 1;
        anchor.roots = vec![BitcoinNodeHash::new([2; 32])];
        anchor
    }

    #[test]
    fn checkpoints_authenticate_progress_and_compare_final_roots_and_count() {
        let dir = tempfile::tempdir().unwrap();
        std::fs::write(dir.path().join(".sync_node_state"), []).unwrap();
        let anchor = anchor();
        let checkpoint = Checkpoint::open(dir.path(), Network::Regtest, anchor.clone()).unwrap();
        assert_eq!(
            checkpoint.recover(|_| None).unwrap(),
            (0, Stump::default(), false)
        );
        let hash = BlockHash::all_zeros();
        checkpoint.store(1, hash, &Stump::default(), false).unwrap();
        let reopened = Checkpoint::open(dir.path(), Network::Regtest, anchor.clone()).unwrap();
        assert_eq!(
            reopened.recover(|_| Some(hash)).unwrap(),
            (1, Stump::default(), false)
        );
        assert!(reopened.recover(|_| Some(anchor.block_hash)).is_err());
        assert!(reopened.store(1, hash, &Stump::default(), true).is_err());
        assert!(reopened
            .store(2, anchor.block_hash, &Stump::default(), true)
            .is_err());
        let mut stump = Stump {
            leaves: 1,
            roots: vec![BitcoinNodeHash::new([1; 32])],
        };
        assert!(reopened.store(2, anchor.block_hash, &stump, true).is_err());
        stump.roots.clone_from(&anchor.roots);
        reopened.store(2, anchor.block_hash, &stump, true).unwrap();
        assert_eq!(
            reopened.recover(|_| Some(anchor.block_hash)).unwrap(),
            (2, stump, true)
        );
        let bytes = std::fs::read(&reopened.path).unwrap();
        let mut corrupt = bytes.clone();
        corrupt[0] ^= 1;
        for torn in [
            vec![],
            bytes[..4].to_vec(),
            corrupt,
            vec![0; MAX_RECORD + 1],
        ] {
            std::fs::write(&reopened.path, torn).unwrap();
            assert!(reopened.recover(|_| Some(anchor.block_hash)).is_err());
        }
    }

    #[test]
    fn checkpoint_prefix_replays_only_the_suffix_and_preserves_pinned_policy() {
        let dir = tempfile::tempdir().unwrap();
        let old = anchor();
        let old_stump = Stump {
            leaves: old.leaves,
            roots: old.roots.clone(),
        };
        let mut later = old.clone();
        later.height += 2;
        later.block_hash = BlockHash::from_byte_array([7; 32]);
        later.roots = vec![BitcoinNodeHash::new([3; 32])];

        for network in [Network::Regtest, Network::Bitcoin] {
            let prior = Checkpoint::open(dir.path(), network, old.clone()).unwrap();
            prior
                .store(old.height, old.block_hash, &old_stump, true)
                .unwrap();
            let extended = Checkpoint::open(dir.path(), network, later.clone()).unwrap();
            let recovered = extended.recover(|h| (h == old.height).then_some(old.block_hash));
            if network == Network::Bitcoin {
                assert!(recovered.is_err(), "a released assumption cannot move");
                continue;
            }
            assert_eq!(recovered.unwrap(), (old.height, old_stump.clone(), false));
            assert!(extended.recover(|_| Some(later.block_hash)).is_err());
            assert!(extended
                .store(later.height, later.block_hash, &old_stump, true)
                .is_err());
            let switched = Checkpoint::open(dir.path(), Network::Testnet, later.clone()).unwrap();
            assert!(switched.recover(|_| Some(old.block_hash)).is_err());

            // A completed target at the same height with a different accumulator is unsafe.
            let mut changed = old.clone();
            changed.roots.clone_from(&later.roots);
            let wrong = Checkpoint::open(dir.path(), network, changed).unwrap();
            assert!(wrong.recover(|_| Some(old.block_hash)).is_err());

            prior
                .store(1, old.block_hash, &Stump::default(), false)
                .unwrap();
            assert!(extended.recover(|_| Some(old.block_hash)).is_err());
        }
    }

    #[test]
    fn checkpoint_rejects_legacy_unbound_authentication_and_malformed_prefixes() {
        let dir = tempfile::tempdir().unwrap();
        let old = anchor();
        let old_stump = Stump {
            leaves: old.leaves,
            roots: old.roots.clone(),
        };
        let previous = Checkpoint::open(dir.path(), Network::Regtest, old.clone()).unwrap();
        previous
            .store(old.height, old.block_hash, &old_stump, true)
            .unwrap();
        let mut later = old.clone();
        later.height += 1;
        let reopened = Checkpoint::open(dir.path(), Network::Regtest, later).unwrap();
        let signed = std::fs::read(&previous.path).unwrap();
        let body = &signed[MAC_SIZE..];
        let key = std::fs::read(dir.path().join(KEY_FILE)).unwrap();
        let mut legacy = HmacEngine::<sha256::Hash>::new(&key);
        legacy.input(body);
        let mut old_tag = Hmac::from_engine(legacy).to_byte_array().to_vec();
        old_tag.extend(body);
        std::fs::write(&previous.path, old_tag).unwrap();
        assert!(reopened.recover(|_| Some(old.block_hash)).is_err());

        let mut record: Record = serde_json::from_slice(body).unwrap();
        record.anchor = [12; 32];
        let corrupt = serde_json::to_vec(&record).unwrap();
        let mut signed_bad = previous.tag(&corrupt).to_vec();
        signed_bad.extend(corrupt);
        std::fs::write(&previous.path, signed_bad).unwrap();
        assert!(reopened.recover(|_| Some(old.block_hash)).is_err());
    }

    #[test]
    fn reserved_mainnet_replay_requires_new_validated_work_and_matching_active_anchor() {
        if !floresta_chain::SCRIPT_KERNEL_ENABLED {
            return;
        }
        let dir = tempfile::tempdir().unwrap();
        let pin = ChainParams::get_assume_utreexo(Network::Bitcoin);
        let check = Checkpoint::open(dir.path(), Network::Bitcoin, pin.clone()).unwrap();
        let grant = check.reserve(true, true, false).unwrap();
        assert_eq!(grant, Admission::Reserved);
        let status = Historical::default();
        status.begin(100, &pin, grant);
        let tip = pin.height + 30;
        let read = || status.snapshot(tip, tip, false, |_| Some(pin.block_hash));
        assert!(!read().checkpoint_eligible);
        status.advance(100);
        assert!(!read().checkpoint_eligible);
        status.advance(101);
        assert!(read().checkpoint_eligible);
        assert!(
            !status
                .snapshot(tip, tip - 1, false, |_| Some(pin.block_hash))
                .checkpoint_eligible
        );
        assert!(
            !status
                .snapshot(tip, tip, true, |_| Some(pin.block_hash))
                .checkpoint_eligible
        );
        let detached = status.snapshot(tip, tip, false, |_| Some(BlockHash::all_zeros()));
        assert!(!detached.checkpoint_eligible);
        assert_eq!(detached.state, "error");
        status.advance(pin.height);
        assert!(!read().checkpoint_eligible);
        check.fence(Fence::Ready).unwrap(); // orderly partial shutdown
        let restart = Checkpoint::open(dir.path(), Network::Bitcoin, pin).unwrap();
        assert_eq!(
            restart.reserve(false, true, false).unwrap(),
            Admission::Reserved
        );
    }

    #[test]
    fn contradiction_survives_restart_and_requires_a_successful_independent_replay() {
        if !floresta_chain::SCRIPT_KERNEL_ENABLED {
            return;
        }
        let dir = tempfile::tempdir().unwrap();
        let pin = ChainParams::get_assume_utreexo(Network::Bitcoin);
        let check = Checkpoint::open(dir.path(), Network::Bitcoin, pin.clone()).unwrap();
        assert_eq!(
            check.reserve(true, true, false).unwrap(),
            Admission::Reserved
        );
        let valid = Stump {
            leaves: pin.leaves,
            roots: pin.roots.clone(),
        };
        // Even a genuine old positive record cannot retire a subsequent failure.
        check
            .store(pin.height, pin.block_hash, &valid, true)
            .unwrap();
        let bad = Stump::default();
        assert!(check
            .check_replayed_anchor(pin.height, pin.block_hash, None, &bad)
            .is_err());
        assert!(matches!(check.read_fence(false), Some(Fence::Reserved)));
        assert!(check
            .check_replayed_anchor(pin.height, pin.block_hash, Some(pin.block_hash), &bad)
            .is_err());
        let reopen = Checkpoint::open(dir.path(), Network::Bitcoin, pin.clone()).unwrap();
        let (_, _, complete) = reopen.recover(|_| Some(pin.block_hash)).unwrap();
        assert!(complete);
        let denied = reopen.reserve(false, true, complete).unwrap();
        assert_eq!(denied, Admission::Mismatch);
        assert!(denied.requires_replay());
        let status = Historical::default();
        status.begin(0, &pin, denied);
        status.advance(10);
        let snapshot = status.snapshot(pin.height, pin.height, false, |_| Some(pin.block_hash));
        assert!(!snapshot.checkpoint_eligible);
        assert_eq!(
            snapshot.checkpoint_hold,
            Some("previous-accumulator-mismatch")
        );
        reopen
            .check_replayed_anchor(pin.height, pin.block_hash, Some(pin.block_hash), &valid)
            .unwrap();
        reopen
            .store(pin.height, pin.block_hash, &valid, true)
            .unwrap();
        reopen.fence(Fence::Ready).unwrap();
        assert_eq!(
            reopen.reserve(false, true, true).unwrap(),
            Admission::StrictOnly
        );
    }

    #[test]
    fn missing_corrupt_or_wrong_policy_fences_keep_an_existing_store_ineligible() {
        if !floresta_chain::SCRIPT_KERNEL_ENABLED {
            return;
        }
        let dir = tempfile::tempdir().unwrap();
        let pin = ChainParams::get_assume_utreexo(Network::Bitcoin);
        let open = || Checkpoint::open(dir.path(), Network::Bitcoin, pin.clone()).unwrap();
        let check = open();
        assert_eq!(
            check.reserve(false, true, false).unwrap(),
            Admission::Interrupted
        );
        let path = dir.path().join(FENCE_FILE);
        std::fs::remove_file(&path).unwrap();
        assert_eq!(
            open().reserve(true, true, false).unwrap(),
            Admission::Interrupted
        );
        check.fence(Fence::Ready).unwrap();
        assert_eq!(
            open().reserve(false, false, false).unwrap(),
            Admission::Interrupted
        );
        check.fence(Fence::Ready).unwrap();
        let mut bytes = std::fs::read(&path).unwrap();
        bytes[5] ^= 1;
        std::fs::write(&path, bytes).unwrap();
        assert_eq!(
            open().reserve(false, true, false).unwrap(),
            Admission::Interrupted
        );
        for network in [Network::Testnet, Network::Regtest, Network::Signet] {
            let other = Checkpoint::open(
                dir.path(),
                network,
                ChainParams::get_assume_utreexo(network),
            )
            .unwrap();
            assert_eq!(
                other.reserve(true, true, false).unwrap(),
                Admission::StrictOnly
            );
        }
        let mut other_pin = pin.clone();
        other_pin.height -= 1;
        let other = Checkpoint::open(dir.path(), Network::Bitcoin, other_pin).unwrap();
        assert_eq!(
            other.reserve(true, true, false).unwrap(),
            Admission::StrictOnly
        );
    }

    #[test]
    fn abrupt_worker_exit_cannot_reopen_the_same_assumed_grant() {
        if !floresta_chain::SCRIPT_KERNEL_ENABLED {
            return;
        }
        const CHILD: &str = "CHICORY_TEST_FENCE_CRASH_DIRECTORY";
        let pin = ChainParams::get_assume_utreexo(Network::Bitcoin);
        if let Some(dir) = std::env::var_os(CHILD) {
            let check = Checkpoint::open(Path::new(&dir), Network::Bitcoin, pin).unwrap();
            assert_eq!(
                check.reserve(true, true, false).unwrap(),
                Admission::Reserved
            );
            std::process::exit(73); // leave the reservation without a destructor or shutdown
        }
        let dir = tempfile::tempdir().unwrap();
        let exited = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", "p2p_wire::historical::tests::abrupt_worker_exit_cannot_reopen_the_same_assumed_grant"])
            .env(CHILD, dir.path()).output().unwrap();
        assert_eq!(exited.status.code(), Some(73));
        let reopened = Checkpoint::open(dir.path(), Network::Bitcoin, pin).unwrap();
        assert_eq!(
            reopened.reserve(false, true, false).unwrap(),
            Admission::Interrupted
        );
    }

    #[test]
    fn verified_snapshot_requires_active_anchor_and_foreground_validation() {
        let progress = Historical::default();
        let anchor = anchor();
        progress.begin(0, &anchor, Admission::StrictOnly);
        assert_eq!(
            progress
                .snapshot(5, 5, false, |_| Some(anchor.block_hash))
                .state,
            "verifying"
        );
        progress.advance(2);
        progress.verified();
        assert_eq!(
            progress
                .snapshot(5, 5, true, |_| Some(anchor.block_hash))
                .state,
            "verifying"
        );
        assert_eq!(
            progress
                .snapshot(5, 4, false, |_| Some(anchor.block_hash))
                .state,
            "verifying"
        );
        assert_eq!(
            progress
                .snapshot(5, 5, false, |_| Some(anchor.block_hash))
                .state,
            "verified"
        );
        assert_eq!(progress.snapshot(5, 5, false, |_| None).state, "error");
    }
}
