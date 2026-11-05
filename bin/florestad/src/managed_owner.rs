// SPDX-License-Identifier: MIT OR Apache-2.0

//! Identify an app-owned database while its daemon or offline helper holds its lock.
use std::fs;
use std::io::{self, Read};
use std::path::Path;

use bitcoin::Network;

pub(crate) const FILE: &str = "chicory-owner.json";

pub(crate) fn marker(network: Network, fingerprint: &str) -> io::Result<String> {
    let name = match network {
        Network::Bitcoin => "mainnet",
        Network::Testnet => "testnet",
        Network::Regtest => "regtest",
        _ => return Err(io::Error::other("Unsupported managed storage network")),
    };
    if fingerprint.len() != 64
        || !fingerprint
            .bytes()
            .all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase())
    {
        return Err(io::Error::other("Invalid managed storage fingerprint"));
    }
    Ok(format!(
        r#"{{"format":"chicory-floresta/1","network":"{name}","profile":"{fingerprint}"}}"#
    ))
}

pub(crate) fn check(root: &Path, network: Network, expected: Option<&str>) -> io::Result<()> {
    let path = root.join(FILE);
    let stat = match fs::symlink_metadata(&path) {
        Err(e) if e.kind() == io::ErrorKind::NotFound && expected.is_none() => return Ok(()),
        result => result?,
    };
    let mismatch = || io::Error::other("Managed store owner or build differs");
    let expected = marker(network, expected.ok_or_else(mismatch)?)?;
    if !stat.is_file() || stat.len() != expected.len() as u64 {
        return Err(mismatch());
    }
    let mut bytes = Vec::new();
    fs::File::open(path)?.take(1025).read_to_end(&mut bytes)?;
    if bytes != expected.as_bytes() {
        return Err(mismatch());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn only_the_named_build_may_open_an_owned_store() {
        let dir = std::env::temp_dir().join(format!("chicory-owner-test-{}", std::process::id()));
        fs::create_dir(&dir).unwrap();
        let net = Network::Regtest;
        let old = "aa".repeat(32);
        let current = "bb".repeat(32);
        assert!(check(&dir, net, None).is_ok());
        assert!(check(&dir, net, Some(&current)).is_err());
        fs::write(dir.join(FILE), marker(net, &old).unwrap()).unwrap();
        assert!(check(&dir, net, Some(&old)).is_ok());
        assert!(check(&dir, net, None).is_err());
        assert!(check(&dir, net, Some(&current)).is_err());
        assert!(check(&dir, Network::Bitcoin, Some(&old)).is_err());
        fs::remove_file(dir.join(FILE)).unwrap();
        fs::remove_dir(&dir).unwrap();
    }
}
