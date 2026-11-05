// SPDX-License-Identifier: MIT OR Apache-2.0

//! Managed replay checkpoints are private to the directory locked by the daemon.
//! Legacy .sync_node_state files cannot establish or advance historical verification.
use std::fs::File;
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

use bitcoin::hashes::{sha256, Hash, HashEngine, Hmac, HmacEngine};
use bitcoin::BlockHash;
use floresta_chain::AssumeUtreexoValue;
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
            anchor: None,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct Historical(Arc<Mutex<Progress>>);

impl Historical {
    pub(crate) fn begin(&self, height: u32, anchor: &AssumeUtreexoValue) {
        *self.0.lock().unwrap() = Progress {
            state: "verifying",
            height,
            target: anchor.height,
            error: None,
            anchor: Some(anchor.block_hash),
        };
    }

    pub(crate) fn failed(&self) -> bool {
        self.0.lock().unwrap().state == "error"
    }

    pub(crate) fn advance(&self, height: u32) {
        self.0.lock().unwrap().height = height;
    }

    pub(crate) fn verified(&self) {
        self.0.lock().unwrap().state = "verified";
    }

    pub(crate) fn fail(&self, message: &str) {
        let mut state = self.0.lock().unwrap();
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
        if result.state == "verified" {
            if hash(result.target) != result.anchor {
                result.state = "error";
                result.error = Some("Historical anchor left the active chain".to_owned());
            } else if ibd || validated != tip {
                result.state = "verifying";
            }
        }
        result
    }
}

const KEY_FILE: &str = "chicory-backfill-v1.key";
const STATE_FILE: &str = "chicory-backfill-v1.state";
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
    pub(crate) fn open(dir: &Path, anchor: AssumeUtreexoValue) -> io::Result<Self> {
        let key_path = dir.join(KEY_FILE);
        let key = match read_bounded(&key_path, MAC_SIZE) {
            Ok(bytes) => bytes
                .try_into()
                .map_err(|_| invalid("Invalid historical checkpoint key"))?,
            Err(error) if error.kind() == io::ErrorKind::NotFound => {
                let mut key = [0; MAC_SIZE];
                OsRng.try_fill_bytes(&mut key).map_err(io::Error::other)?;
                save(&key_path, &key)?;
                key
            }
            Err(error) => return Err(error),
        };
        Ok(Self {
            path: dir.join(STATE_FILE),
            key,
            anchor,
        })
    }

    fn tag(&self, bytes: &[u8]) -> [u8; MAC_SIZE] {
        let mut engine = HmacEngine::<sha256::Hash>::new(&self.key);
        engine.input(bytes);
        Hmac::from_engine(engine).to_byte_array()
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
        if record.version != 1
            || record.target != self.anchor.height
            || record.anchor != self.anchor.block_hash.to_byte_array()
            || record.height > record.target
            || hash_at(record.height) != Some(BlockHash::from_byte_array(record.hash))
            || (record.complete && record.height != record.target)
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
            || (record.height == record.target && !self.matches(&stump))
        {
            return Err(invalid("Historical accumulator mismatch"));
        }
        Ok((record.height, stump, record.complete))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bitcoin::Network;
    use floresta_chain::ChainParams;
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
        let checkpoint = Checkpoint::open(dir.path(), anchor.clone()).unwrap();
        assert_eq!(
            checkpoint.recover(|_| None).unwrap(),
            (0, Stump::default(), false)
        );
        let hash = BlockHash::all_zeros();
        checkpoint.store(1, hash, &Stump::default(), false).unwrap();
        let reopened = Checkpoint::open(dir.path(), anchor.clone()).unwrap();
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
    fn verified_snapshot_requires_active_anchor_and_foreground_validation() {
        let progress = Historical::default();
        let anchor = anchor();
        progress.begin(0, &anchor);
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
