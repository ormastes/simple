# DBFS POSIX Compatibility Matrix (D10 Shim Subset)

Feature: `dbfs-integration` — Phase 4/5 deliverable describing DBFS's POSIX-compat
subset against `doc/04_architecture/dbfs_architecture.md` §D10, the
`test/dbfs/dbfs_posix_shim_spec.spl` contract, and the existing `NvfsPosix` shim
under `examples/nvfs/src/posix/**`.

Sources consulted (read-only):
- `doc/04_architecture/dbfs_architecture.md` §D10 — supported / out-of-scope op
  tables and the COW EXTENT_REF rewrite path.
- `.sstack/dbfs-integration/state.md` — Phase 3 D10 summary; Phase 5 spec
  results (16/19 green).
- `test/dbfs/dbfs_posix_shim_spec.spl` — only spec that directly contracts
  POSIX-edge semantics for DBFS.
- `test/dbfs/dbfs_driver_spec.spl`, `test/dbfs/dbfs_capability_spec.spl` — round-
  trip and capability-probe contracts.
- `examples/nvfs/src/posix/{driver,capabilities,fd_table,cow_engine}.spl` —
  comparison shim.
- `src/lib/nogc_sync_mut/fs_driver/instance.spl` — DriverInstance dispatch
  surface (the `_ → Err(FsError.Unsupported)` arms for non-DbFs drivers).
- `doc/05_design/fs_driver_interface.md` §7 — `FsError → errno` mapping.

Conventions: "Spec line" = `describe`/`it` block in the cited spec. "Phase 4 gap"
= contract not asserted by any spec; should be patched before Phase 7 verify.

---

## 1. Supported Operations

DBFS claims support for the ops below per D10. Support level is one of
`full` (semantics + edge cases asserted), `partial` (round-trip only, no
edge contract), or `no` (D10 lists it but no impl/spec yet).

| Op | Level | Edge-case notes | Spec covering it | COW shadow path | Divergence from POSIX |
|----|-------|-----------------|------------------|-----------------|-----------------------|
| `open(path, flags)` | partial | `O_RDWR` + `create_write` round-trip only; no `O_TRUNC`/`O_EXCL`/`O_APPEND` edge contract | `dbfs_driver_spec.spl` "open with create_write creates file"; `dbfs_posix_shim_spec.spl` (used by every `it`) | n/a | — |
| `close(fd)` | partial | Implicit — used by every spec; "read on closed handle returns error" is the only edge | `dbfs_driver_spec.spl` "read on closed handle returns error" | n/a | — |
| `read(fd, buf, len)` | partial | Sequential round-trip only; short-read on EOF unspecified | `dbfs_driver_spec.spl` "write then read round-trips content" | n/a | — |
| `pread(fd, buf, len, off)` | full | Read-back after `pwrite` at offset is asserted | `dbfs_posix_shim_spec.spl` "pwrite at offset rewrites EXTENT_REF; subsequent pread returns new data" | Reads through latest `EXTENT_REF(ino_id, max(gen))` | — |
| `write(fd, buf, len)` | partial | Sequential round-trip; advance-of-cursor unspecified | `dbfs_driver_spec.spl` "write then read round-trips content" | New EXTENT + BLOCK_BLOB; EXTENT_REF inserted; gen bump | — |
| `pwrite(fd, buf, len, off)` | full | Bytes before offset must be preserved; new bytes overwrite at offset | `dbfs_posix_shim_spec.spl` "pwrite at offset…", "pwrite does not corrupt bytes before the written offset" | Per D10: alloc new `blob_id` → insert/update `EXTENT_REF(ino_id, gen+1, logical_offset)` → trim/delete overlapping old EXTENT_REF → publish gen atomically | — |
| `lseek(fd, off, whence)` | no | **Phase 4 gap**: not in D10 op table. DBFS uses explicit-offset `pread`/`pwrite`. Sequential `read`/`write` cursor implied but not contracted | none | n/a | DBFS pushes positional I/O onto callers; no `SEEK_HOLE`/`SEEK_DATA` |
| `fsync(fd)` | no | **OOS** per D10: "Not exposed; WAL provides per-txn durability" | none (negative — see §2) | n/a | Durability boundary is the txn commit, not a per-fd flush |
| `fdatasync(fd)` | no | Same as `fsync` | none | n/a | Same |
| `stat(path)` | partial | Round-trip on dirs and files; `is_dir` flag asserted; mode/uid/gid/times unchecked | `dbfs_driver_spec.spl` "mkdir creates directory; stat returns is_dir=true", "stat on missing path returns error", `dbfs_posix_shim_spec.spl` "after close, unlinked file is not accessible" | Reads INODE via MVCC snapshot; no lock | — |
| `fstat(fd)` | partial | Implied by `DriverInstance.stat_path`/handle dispatch; not directly asserted | none (Phase 4 gap on direct fstat assertion) | Same as `stat` | — |
| `lstat(path)` | no | **Phase 4 gap**: D10 says `stat`/`fstat` only; symlink-no-follow semantics unspecified | none | Same as `stat` if it existed | — |
| `unlink(path)` | full | Tombstone-while-open semantics asserted; data accessible until close; vacuum after refcount=0 | `dbfs_posix_shim_spec.spl` "unlink while handle open: data accessible until close", "after close, unlinked file is not accessible" | Tombstone DENTRY; decrement `link_count`; queue for vacuum when 0 | — |
| `rename(src, dst)` | full | Rename-over-existing replaces target atomically | `dbfs_posix_shim_spec.spl` "rename-over-existing is atomic (target replaced)"; `dbfs_driver_spec.spl` "rename moves file…" | Lock both parents (D8 order); update DENTRY atomically; COW INODE gen bump | No `renameat2(RENAME_EXCHANGE)` (see §2) |
| `mkdir(path, mode)` | partial | Round-trip via subsequent `stat`; mode bits not asserted | `dbfs_driver_spec.spl` "mkdir creates directory; stat returns is_dir=true" | New INODE + DENTRY insert via 6-step write path | — |
| `rmdir(path)` | no | **Phase 4 gap**: D10 lists `mkdir` but not `rmdir`; presumed reachable through `unlink` on dir-INODE but never asserted | none | Would mirror `unlink` | — |
| `readdir(path)` / `getdents` | partial | Entry count `>= 2` after two `mkdir`s; ordering / `.`/`..` unspecified | `dbfs_driver_spec.spl` "readdir on mounted dir returns created entries" | DENTRY B-tree range scan on `parent_ino` | — |
| `truncate(path, len)` / `ftruncate(fd, len)` | partial | Mentioned in spec docstring ("truncate shrink and grow") but no `it` block actually exercises shrink/grow content semantics | docstring of `dbfs_posix_shim_spec.spl` (Phase 4 gap: contract assertion missing) | COW: remove/trim EXTENT_REFs beyond `len`; update INODE.size | Grow may not zero-fill (sparse-vs-zero semantics unspecified) |
| `chmod(path, mode)` | no | **Phase 4 gap**: INODE has `mode` per D3 schema; D10 op table omits chmod | none | Would COW INODE gen bump | — |
| `chown(path, uid, gid)` | no | **Phase 4 gap**: INODE has `uid`/`gid` fields; no shim op | none | Same | — |
| `utimens(path, ts)` | no | **Phase 4 gap**: INODE has `*_time_ns` fields; no shim op | none | Same | — |
| `dup(fd)` / `dup2(fd, fd2)` | no | **Phase 4 gap + divergence**: NvfsPosix FdTable refcounts on dup; DBFS shim has no exposed dup | none | n/a | NvfsPosix supports it; DBFS doesn't expose it |
| `setxattr(path, name, val)` | partial | Listed in D10 ("XATTR B-tree insert/lookup"); capability probe asserts `Xattr=true`; no round-trip spec | `dbfs_capability_spec.spl` "Xattr capability is present" (probe-only) | XATTR B-tree insert | — |
| `getxattr(path, name)` | partial | Same — probe-only | `dbfs_capability_spec.spl` (probe-only) | XATTR B-tree lookup | — |
| `listxattr(path)` | no | **Phase 4 gap**: D10 op table omits `listxattr` | none | Would be XATTR B-tree range-scan on `ino_id` | — |
| `removexattr(path, name)` | no | **Phase 4 gap**: D10 omits | none | Would be XATTR B-tree delete | — |
| `getfacl(path)` / `setfacl(path, acl)` | partial | D10 lists ACL_ENTRY ops; capability probe asserts `Acl=true`; no round-trip spec | `dbfs_capability_spec.spl` "Acl capability is present" | ACL_ENTRY B-tree insert/lookup | — |
| `symlink(target, path)` | partial | D10 lists ("INODE with `mode=S_IFLNK`; store target in XATTR `symlink.target`"); no spec asserts | none (Phase 4 gap) | New INODE + XATTR `symlink.target` | — |
| `readlink(path)` | partial | D10 lists ("Read `symlink.target` XATTR"); no spec asserts | none (Phase 4 gap) | XATTR lookup | — |

**Tally:** 29 rows. Full: 4. Partial: 14. Not implemented: 11
(of those: `fsync`/`fdatasync` are *deliberate* OOS — also listed in §2 — and
the remaining 9 are unintentional gaps not addressed by D10).

---

## 2. Out-of-Scope Operations (Deliberate)

Per D10's "Explicitly out of scope" table; all return `FsError.Unsupported`,
which `errno_of(err)` maps to `ENOTSUP=95` at the VFS boundary
(`doc/05_design/fs_driver_interface.md §7`).

| Op | Reason | FsError | errno | Future-work pointer |
|----|--------|---------|-------|---------------------|
| `mmap(MAP_SHARED \| PROT_WRITE)` | Requires kernel VM integration; deferred | `FsError.Unsupported` | `ENOTSUP` | D10 future scope; `DriverInstance.mmap_shared_writable_handle` already returns ENOTSUP for all drivers |
| `link(old, new)` (hard link) | `link_count > 1` not tracked in this delivery | `FsError.Unsupported` | `ENOTSUP` | D10; capability probe `Hardlinks=false` (`dbfs_capability_spec.spl`) |
| `fallocate(FALLOC_FL_PUNCH_HOLE)` / `SEEK_HOLE` / `SEEK_DATA` | Hole-punch in EXTENT_REF deferred | `FsError.Unsupported` | `ENOTSUP` | Sparse-files-as-holes is a known follow-up; `SparseFiles` capability is **not** advertised |
| `O_DIRECT` | Bypasses buffer manager; deferred | `FsError.Unsupported` | `ENOTSUP` | Capability probe `DirectIo=false` |
| `fsync(fd)` / `fdatasync(fd)` (per-fd) | Not exposed; WAL provides per-txn durability | `FsError.Unsupported` | `ENOTSUP` | Group commit / explicit barrier API tracked under D4 |
| `flock(fd)` / `fcntl(F_SETLK)` advisory locks | Deferred | `FsError.Unsupported` | `ENOTSUP` | None tracked |
| `O_TMPFILE` / `linkat(AT_EMPTY_PATH)` | Anonymous-inode workflow not modeled | `FsError.Unsupported` | `ENOTSUP` | Phase-4 gap (D10 silent; assumed ENOTSUP) |
| `renameat2(RENAME_EXCHANGE)` / `RENAME_WHITEOUT` | Atomic-swap and overlay primitives not in D10 | `FsError.Unsupported` | `ENOTSUP` | Phase-4 gap |
| `copy_file_range`, `splice`, `tee` | Bulk-copy fastpaths not exposed | `FsError.Unsupported` | `ENOTSUP` | Phase-4 gap |
| `ioctl(...)` (FS-specific) | No DBFS ioctl surface defined | `FsError.Unsupported` | `ENOTSUP` | Possible vendor extension via Extension probe |

**Tally:** 10 rows. (`dup`/`dup2` is *not* counted here — it's an unmodeled
gap, not a deliberate decline; see §1 and §5.3.)

---

## 3. Errno Mapping

All DBFS shim ops returning `Err(_)` route through the single
`errno_of(FsError) -> i32` mapping in
`src/lib/nogc_sync_mut/fs_driver/error.spl` (canonical text:
`doc/05_design/fs_driver_interface.md §7`):

| FsError variant | POSIX errno | Used by DBFS shim for |
|-----------------|-------------|------------------------|
| `Unsupported` | `ENOTSUP` (95) | Every OOS op in §2 |
| `NotFound` | `ENOENT` (2) | `stat`/`open`/`unlink` of missing path |
| `AlreadyExists` | `EEXIST` (17) | `open(O_EXCL)` (Phase-4 gap), `mkdir` collision |
| `Permission` | `EACCES` (13) | (Reserved; ACL enforcement Phase-4 gap) |
| `IoError(_)` | `EIO` (5) | Block-device errors; checksum mismatch via `Corrupt` |
| `Corrupt` | `EIO` (5) | WAL-replay-time CRC failures |
| `NoSpace` | `ENOSPC` (28) | Arena/blob alloc failure |
| `Busy` | `EBUSY` (16) | Unmount with open handles |
| `ReadOnly` | `EROFS` (30) | Write attempted on `mount(read_only=true)` |
| `InvalidArg` | `EINVAL` (22) | Bad offset, null handle |
| `TooLarge` | `EFBIG` (27) | File-size limit exceeded |
| `Transient(_)` | `EAGAIN` (11) | Lock-contention retry hint |
| `Interrupted` | `EINTR` (4) | Signal-aware paths (kernel-linked build) |

**Note:** there is no per-op errno path for OOS ops — all funnel through
`Unsupported → ENOTSUP`. Userland must `strerror(95)` to discriminate.

---

## 4. xfstests / pjdfstest Readiness (Future Scope)

If DBFS were exposed via FUSE/userspace to xfstests, the buckets below
indicate likely outcome. **None of this is contracted today** — pure
projection from D10 + the spec coverage in §1.

| Group | Verdict | Rationale |
|-------|---------|-----------|
| `generic/quick` (open/close/read/write/mkdir/rename/unlink basics) | **PASS-likely** | Round-trips covered in `dbfs_driver_spec`; rename-over-existing in `dbfs_posix_shim_spec`. |
| `generic/hardlink` | **SKIP** | `link()→ENOTSUP`; capability `Hardlinks=false`. |
| `generic/sparse` (punch hole, SEEK_HOLE/DATA, fallocate) | **SKIP** | OOS per D10; capability `SparseFiles` not advertised. |
| `generic/mmap` (MAP_SHARED writable) | **SKIP** | OOS per D10; `mmap_shared_writable_handle→ENOTSUP`. |
| `generic/xattr` (set/get) | **PARTIAL** | set/get listed in D10; **`listxattr`/`removexattr` missing → tests requiring those FAIL/SKIP**. |
| `generic/acl` | **PARTIAL** | get/set listed; no edge contract; ACL enforcement on `open` Phase-4 gap. |
| `generic/atime`, `generic/mtime`, `generic/utimens` | **UNKNOWN** → likely FAIL | INODE has time fields per D3 but no `utimens` shim op (Phase-4 gap). |
| `generic/fsync`, `generic/log_recovery` (durability) | **INDETERMINATE** | WAL is per-txn, not per-fd; per-file `fsync→ENOTSUP`. xfstests' fsync-then-crash-then-replay tests likely don't map cleanly. |
| `generic/dup`, `generic/fcntl` | **SKIP** | `dup`/`dup2`/`fcntl` not in shim. |
| `generic/rename` (RENAME_EXCHANGE / RENAME_WHITEOUT) | **SKIP** | `renameat2` flags OOS. |
| `generic/permissions` (chmod/chown effect on access) | **FAIL-likely** | `chmod`/`chown` not in shim; ACL enforcement also a gap. |
| `generic/quota` | **SKIP** | Capability not advertised. |
| `generic/flock` | **SKIP** | OOS per D10. |
| `generic/large_file` (>4 GiB) | **PASS-likely** | Capability `LargeFiles=true`; INODE.size is i64; not contracted by spec. |
| `pjdfstest/chmod`, `pjdfstest/chown`, `pjdfstest/utimensat` | **FAIL** | Ops missing. |
| `pjdfstest/mkdir`, `pjdfstest/unlink`, `pjdfstest/rename`, `pjdfstest/symlink` | **PARTIAL** | Round-trip only; error-path edges (EEXIST, ENOTDIR, ELOOP) not asserted. |

---

## 5. NvfsPosix Divergence

DBFS deliberately re-uses NvfsPosix's *discipline* (POSIX-shim over append-only
storage, COW for in-place writes) but diverges substantially in capability set
and granularity.

### 5.1 Capability set (near-inverse)

| Capability | NvfsPosix | DBFS | Notes |
|-----------|-----------|------|-------|
| `PosixCompat` | yes | yes | Both shims expose POSIX semantics |
| `CaseSensitive` | yes | (unspecified) | DBFS doesn't probe-assert this |
| `Hardlinks` | **yes** | **no** | NvfsPosix `link()` uses `reflink_bump` on the arena; DBFS asserts `link()→ENOTSUP` |
| `SparseFiles` | **yes** | **no** | NvfsPosix uses arena append; DBFS extents are dense |
| `LargeFiles` | yes | yes | Both: i64 sizes |
| `UnicodeNames` | yes | (unspecified) | — |
| `AsyncIo` | yes | (unspecified) | — |
| `COW` | **deliberately hidden** | **yes** | NvfsPosix has CoW internally but **does not advertise** it ("hides arena features behind POSIX semantics"); DBFS advertises it |
| `Snapshot` | hidden | **yes** | DBFS exposes via `Snapshot` capability |
| `Xattr` | **no** | **yes** | NvfsPosix deliberately hides; DBFS exposes |
| `Acl` | **no** | **yes** | Same |
| `Dedup` | no | no | Both decline |
| `DirectIo` | (unspecified) | no | — |

### 5.2 CoW granularity

- **NvfsPosix**: whole-arena rewrite. `pwrite(off,buf)` ⇒ allocate new arena,
  append `base[0..off] + buf + base[off+len..end]`, then "publish-flip" the
  fd's `arena_id`. Old arena discarded (refcount-aware) when no fd references
  it. Source: `examples/nvfs/src/posix/cow_engine.spl`.
- **DBFS**: per-extent rewrite. `pwrite(off,buf)` ⇒ allocate new BLOCK_BLOB,
  insert/update one or more `EXTENT_REF(ino_id, gen+1, logical_offset)`,
  trim/delete overlapping old EXTENT_REFs, publish new gen atomically.
  Source: D10 "Random write via COW path".

Practical consequence: DBFS scales to large files with sparse rewrites
(per-extent metadata), while NvfsPosix amplifies write cost on large arenas
(whole-arena copy). DBFS is a better fit for `/data`-style workloads where
random overwrites dominate.

### 5.3 FdTable / dup semantics

- NvfsPosix has a `FdTable` per driver with refcount-on-dup (bit-2 / bit-3
  mode flags, `_publish_flip`). `dup`/`dup2` work because the slot's arena_id
  is shared.
- DBFS has no documented FdTable refcount path; `dup`/`dup2` are not exposed.
  Listed as both Phase-4 gap (§1) and divergence here.

### 5.4 Namespace authority

- NvfsPosix uses an in-memory name table at B2 (will be B-tree at N2).
- DBFS uses a DENTRY B-tree from day one (D3 schema). DBFS is namespace-
  authoritative across reboots; NvfsPosix B2 namespace is volatile.

**Tally:** 4 substantive divergences (capability set, CoW granularity, FdTable
refcounts/dup, namespace persistence). At least 5 secondary divergences if you
count individual capability flips as separate.

---

## 6. Acceptance-Test Hooks (Per Op)

For each op asserted as `full` or `partial` in §1, the spec line (file +
`describe`/`it` text). Anything marked **Phase 4 gap** has no contract today
and should be patched before Phase 7 verify.

| Op | Spec hook |
|----|-----------|
| `pwrite` (COW correctness) | `test/dbfs/dbfs_posix_shim_spec.spl` :: describe "DBFS POSIX Shim — random write via COW" :: it "pwrite at offset rewrites EXTENT_REF; subsequent pread returns new data" |
| `pwrite` (no underwrite corruption) | same file :: it "pwrite does not corrupt bytes before the written offset" |
| `rename` (atomic over-existing) | same file :: describe "DBFS POSIX Shim — rename-over-existing" :: it "rename-over-existing is atomic (target replaced)" |
| `unlink` (tombstone-while-open) | same file :: describe "DBFS POSIX Shim — unlink-while-open tombstone" :: it "unlink while handle open: data accessible until close" |
| `unlink` (after close, gone) | same file :: it "after close, unlinked file is not accessible" |
| `mmap_shared_writable` (ENOTSUP) | same file :: describe "DBFS POSIX Shim — out-of-scope ops return ENOTSUP" :: it "mmap_shared_writable returns ENOTSUP" |
| `link` (ENOTSUP) | same file :: it "link (hard link) returns ENOTSUP" |
| `open`/`write`/`read` round-trip | `test/dbfs/dbfs_driver_spec.spl` :: describe "DBFS FsDriver — open, write, read" |
| `read` on closed handle | same file :: it "read on closed handle returns error" |
| `mkdir` + `stat(is_dir)` | same file :: describe "DBFS FsDriver — mkdir and stat" :: it "mkdir creates directory; stat returns is_dir=true" |
| `stat` on missing path | same file :: it "stat on missing path returns error" |
| `readdir` (entry count) | same file :: describe "DBFS FsDriver — readdir" :: it "readdir on mounted dir returns created entries" |
| `unlink` (basic) | same file :: describe "DBFS FsDriver — unlink and rename" :: it "unlink removes file; stat returns error" |
| `rename` (basic move) | same file :: it "rename moves file; old path gone, new path exists" |
| `Xattr` capability probe | `test/dbfs/dbfs_capability_spec.spl` :: it "Xattr capability is present" |
| `Acl` capability probe | same file :: it "Acl capability is present" |
| `PosixCompat` capability probe | same file :: it "PosixCompat capability is present" |
| `Hardlinks` (negative probe) | same file :: it "Hardlinks capability is absent" |
| `DirectIo` (negative probe) | same file :: it "DirectIo capability is absent" |

### 6.1 Phase 4 contract gaps (no spec line today)

These ops appear in D10 (or are necessary to honor it) but have no `it` block
asserting the contract. **Patch before Phase 7 verify.**

1. `truncate`/`ftruncate` shrink semantics (size-after-shrink, EXTENT_REF
   removal, subsequent read returns ENOENT past `len`).
2. `truncate`/`ftruncate` grow semantics (zero-fill vs sparse).
3. `symlink` round-trip (`symlink → readlink == target`).
4. `setxattr`/`getxattr` round-trip (set value, get returns same bytes).
5. `setfacl`/`getfacl` round-trip + ACL enforcement on subsequent `open`.
6. `fstat` direct (vs path-based `stat`).
7. `mkdir` mode-bits visible in `stat.mode`.
8. `readdir` ordering; presence of `.`/`..`.
9. `open(O_EXCL)` returning `AlreadyExists`.
10. `open(O_TRUNC)` zeroing existing content.
11. `rename` cross-directory; rename of dir into descendant (ELOOP-ish).
12. `unlink` of directory (should ENOTDIR / EISDIR? — D10 silent).
13. `O_DIRECT` rejection: spec docstring lists it as out-of-scope but no `it`
    block asserts `open(O_DIRECT) → ENOTSUP`; only the negative capability
    probe `DirectIo=false` covers it. Either accept the probe as sufficient
    or add a direct ENOTSUP assertion.

**Tally:** 12 core unspecified contract gaps (+1 implicit-vs-asserted
O_DIRECT gap) to file against Phase 4.

---

## Summary Counts

- Supported ops (full + partial in §1): **18** (4 full, 14 partial).
- POSIX ops missing from D10 + no spec assertion (unintentional gap rows in §1,
  excluding deliberate-OOS `fsync`/`fdatasync`): **9**.
- Out-of-scope ops in §2 (deliberate decline): **10**.
- NvfsPosix divergences (substantive): **4** (capability set, CoW
  granularity, FdTable/dup, namespace persistence).
- Phase 4 contract gaps (§6.1): **12**.
