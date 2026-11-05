// SPDX-License-Identifier: MIT OR Apache-2.0

//! Offline cleanup under the same OS lock as a running managed node.
use std::fs::File;
use std::io::{self, Read};
use std::os::unix::fs::MetadataExt;
use std::path::{Component, Path};

use bitcoin::Network;
use rustix::fs::{fstatfs, openat, unlinkat, AtFlags, Dir, Mode, OFlags, CWD};

const LOCK: &str = "chicory-managed.lock";
const PENDING: &str = "chicory-removal-pending";
const OWNER: &str = "chicory-owner.json";

fn refuse() -> io::Error {
    io::Error::other("Unrecognized or unavailable managed store")
}

#[cfg(target_os = "macos")]
fn verify_volume(directory: &File) -> io::Result<()> {
    let fs = fstatfs(directory)?;
    if fs.f_flags & libc::MNT_LOCAL as u32 == 0
        || !fs
            .f_fstypename
            .iter()
            .take_while(|ch| **ch != 0)
            .map(|ch| *ch as u8)
            .eq(b"apfs".iter().copied())
    {
        return Err(refuse());
    }
    Ok(())
}

#[cfg(target_os = "linux")]
fn verify_volume(directory: &File) -> io::Result<()> {
    use rustix::fs::{statx, StatxFlags};
    // ext2/3/4 share a magic number. Ask the kernel which driver handles the
    // opened directory, then disallow mount crossings below it, including bind mounts.
    if fstatfs(directory)?.f_type as u64 != libc::EXT4_SUPER_MAGIC as u64 {
        return Err(refuse());
    }
    let info = statx(directory, "", AtFlags::EMPTY_PATH, StatxFlags::MNT_ID)?;
    if info.stx_mask & StatxFlags::MNT_ID.bits() == 0 {
        return Err(refuse());
    }
    let mounts = File::open("/proc/self/mountinfo")?;
    if fstatfs(&mounts)?.f_type as u64 != libc::PROC_SUPER_MAGIC as u64 {
        return Err(refuse());
    }
    let mut data = String::new();
    const LIMIT: u64 = 4 * 1024 * 1024;
    mounts.take(LIMIT + 1).read_to_string(&mut data)?;
    let prefix = format!("{} ", info.stx_mnt_id);
    if data.len() as u64 > LIMIT
        || !data.lines().any(|line| {
            line.starts_with(&prefix)
                && line
                    .split_once(" - ")
                    .is_some_and(|(_, fs)| fs.starts_with("ext4 "))
        })
    {
        return Err(refuse());
    }
    Ok(())
}

fn open_child(
    dir: &File,
    name: &str,
    flags: OFlags,
    mode: Mode,
) -> rustix::io::Result<rustix::fd::OwnedFd> {
    #[cfg(target_os = "macos")]
    {
        openat(dir, name, flags, mode)
    }
    #[cfg(target_os = "linux")]
    {
        use rustix::fs::{openat2, ResolveFlags};
        openat2(
            dir,
            name,
            flags,
            mode,
            ResolveFlags::BENEATH | ResolveFlags::NO_XDEV | ResolveFlags::NO_SYMLINKS,
        )
    }
}

fn open_dir(parent: &File, name: &str) -> io::Result<File> {
    Ok(File::from(open_child(
        parent,
        name,
        OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC,
        Mode::empty(),
    )?))
}

fn private_dir(dir: &File, dev: u64) -> io::Result<()> {
    let m = dir.metadata()?;
    if m.mode() & 0o077 != 0 || m.uid() != rustix::process::geteuid().as_raw() || m.dev() != dev {
        return Err(refuse());
    }
    Ok(())
}

fn file_at(dir: &File, name: &str, dev: u64, access: OFlags) -> io::Result<File> {
    let file = File::from(open_child(
        dir,
        name,
        access | OFlags::NONBLOCK | OFlags::NOFOLLOW | OFlags::CLOEXEC,
        Mode::empty(),
    )?);
    let m = file.metadata()?;
    #[cfg(target_os = "linux")]
    if m.uid() != rustix::process::geteuid().as_raw() {
        return Err(refuse());
    }
    if !m.is_file() || m.nlink() != 1 || m.dev() != dev {
        return Err(refuse());
    }
    Ok(file)
}

fn sled_file(name: &str) -> bool {
    if matches!(name, "db" | "conf") {
        return true;
    }
    let snap = name.strip_suffix(".generating").unwrap_or(name);
    snap.strip_prefix("snap.")
        .is_some_and(|lsn| lsn.len() == 16 && lsn.bytes().all(|b| b.is_ascii_hexdigit()))
}

#[derive(Clone, Copy)]
enum Layout {
    Root,
    Chain,
    Watches,
    Blobs,
}

// Never recurse into arbitrary paths. Refuse unfamiliar generated-store layouts,
// mount boundaries, symlinks and hard links before unlinking the first file.
fn walk(dir: &File, layout: Layout, dev: u64, deleting: bool) -> io::Result<()> {
    for entry in Dir::read_from(dir)? {
        let entry = entry?;
        let name = entry.file_name().to_str().map_err(|_| refuse())?;
        if matches!(name, "." | "..") {
            continue;
        }
        if matches!(layout, Layout::Root)
            && [LOCK, OWNER, PENDING, "config.toml", ".DS_Store"].contains(&name)
        {
            continue;
        }
        let directory = match (layout, name) {
            (Layout::Root, "chaindata") => Some(Layout::Chain),
            (Layout::Root, "chicory-watches-v1") => Some(Layout::Watches),
            (Layout::Root | Layout::Watches, "blobs") => Some(Layout::Blobs),
            _ => None,
        };
        if let Some(next) = directory {
            let child = open_dir(dir, name)?;
            let metadata = child.metadata()?;
            #[cfg(target_os = "linux")]
            if metadata.uid() != rustix::process::geteuid().as_raw() || metadata.mode() & 0o022 != 0
            {
                return Err(refuse());
            }
            if metadata.dev() != dev {
                return Err(refuse());
            }
            walk(&child, next, dev, deleting)?;
            if deleting {
                unlinkat(dir, name, AtFlags::REMOVEDIR)?;
            }
            continue;
        }
        let known = match layout {
            Layout::Root => {
                sled_file(name)
                    || matches!(
                        name,
                        "cfilters"
                            | "cfilters-index"
                            | "peers.json"
                            | "anchors.json"
                            | ".sync_node_state"
                            | "chicory-backfill-v1.key"
                            | "chicory-backfill-v1.key.tmp"
                            | "chicory-backfill-v1.state"
                            | "chicory-backfill-v1.state.tmp"
                    )
            }
            Layout::Chain => matches!(
                name,
                "metadata.bin"
                    | "accumulators.bin"
                    | "blocks_index.bin"
                    | "fork_headers.bin"
                    | "headers.bin"
            ),
            Layout::Watches => sled_file(name),
            Layout::Blobs => name
                .parse::<i64>()
                .is_ok_and(|value| value.to_string() == name),
        };
        if !known {
            return Err(refuse());
        }
        file_at(dir, name, dev, OFlags::RDONLY)?;
        if deleting {
            unlinkat(dir, name, AtFlags::empty())?;
        }
    }
    Ok(())
}

pub(crate) fn remove(root: &str, store: &str, network: Network, owner: &str) -> io::Result<()> {
    let network = match network {
        Network::Bitcoin => "mainnet",
        Network::Testnet => "testnet",
        Network::Regtest => "regtest",
        _ => return Err(refuse()),
    };
    if owner.len() != 64
        || !owner
            .bytes()
            .all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase())
    {
        return Err(refuse());
    }
    let root = Path::new(root);
    let store = Path::new(store);
    let base = root.parent().ok_or_else(refuse)?;
    if root.file_name().and_then(|n| n.to_str()) != Some(network)
        || !base.ends_with("chicory-floresta")
    {
        return Err(refuse());
    }
    // Keep every operation anchored to an open directory. Rename, symlink and
    // volume swaps cannot redirect deletion into a new pathname.
    let mut directory = File::from(openat(
        CWD,
        "/",
        OFlags::DIRECTORY | OFlags::CLOEXEC,
        Mode::empty(),
    )?);
    if !base.is_absolute() {
        return Err(refuse());
    }
    for component in base.components() {
        match component {
            Component::RootDir => {}
            Component::Normal(name) => {
                directory = File::from(openat(
                    &directory,
                    name,
                    OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC,
                    Mode::empty(),
                )?)
            }
            _ => return Err(refuse()),
        }
    }
    verify_volume(&directory)?;
    let dev = directory.metadata()?.dev();
    private_dir(&directory, dev)?;
    let root_fd = open_dir(&directory, network)?;
    private_dir(&root_fd, dev)?;
    let marker = file_at(&root_fd, OWNER, dev, OFlags::RDONLY)?;
    let expected =
        format!(r#"{{"format":"chicory-floresta/1","network":"{network}","profile":"{owner}"}}"#);
    let mut bytes = Vec::new();
    marker.take(1024).read_to_end(&mut bytes)?;
    if bytes != expected.as_bytes() {
        return Err(refuse());
    }
    let store = if store == root {
        root_fd
    } else {
        open_dir(
            &root_fd,
            store
                .strip_prefix(root)
                .map_err(|_| refuse())?
                .to_str()
                .ok_or_else(refuse)?,
        )?
    };
    private_dir(&store, dev)?;
    // Never unlink the lock inode or its ancestors, even after an interrupted removal.
    let lock = file_at(&store, LOCK, dev, OFlags::RDWR)?;
    fs2::FileExt::try_lock_exclusive(&lock)?;
    walk(&store, Layout::Root, dev, false)?;
    match open_child(
        &store,
        PENDING,
        OFlags::WRONLY | OFlags::NOFOLLOW | OFlags::CREATE | OFlags::EXCL | OFlags::CLOEXEC,
        Mode::RUSR | Mode::WUSR,
    ) {
        Ok(file) => File::from(file).sync_all()?,
        Err(rustix::io::Errno::EXIST) => {
            if file_at(&store, PENDING, dev, OFlags::RDONLY)?
                .metadata()?
                .len()
                != 0
            {
                return Err(refuse());
            }
        }
        Err(e) => return Err(e.into()),
    }
    store.sync_all()?;
    walk(&store, Layout::Root, dev, true)?;
    store.sync_all()?;
    unlinkat(&store, PENDING, AtFlags::empty())?;
    store.sync_all()
}
