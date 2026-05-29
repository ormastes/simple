# NVFS POSIX Wrapper Design

> **Status:** Phase 9-extend design deliverable (2026-04-18).
>
> **Related designs (cross-refs):**
> - `doc/05_design/nvfs_design_v2.md` — NVFS native driver; the POSIX shim sits above it.
> - `doc/05_design/fs_driver_interface.md` — defines `DriverInstance::NvfsPosix`,
>   `Capability::PosixCompat`, and `Extension::PosixCompat(PosixCompatExt)`.
> - `doc/05_design/nvfs/svllm_requirements.md` §120 — svllm explicitly does NOT need POSIX
>   semantics and will not use this shim.

---

## 1. Scope and rationale

NVFS's native API is append-oriented: `arena_create`, `arena_append`, `arena_seal`,
`arena_discard`, `arena_clone_range`. Writes are always appended to the active arena;
arenas are immutable once sealed. There is no concept of "overwrite byte N of an existing
object."

POSIX callers expect a different contract: random-write (`pwrite`), in-place truncate
(`ftruncate`), rename, unlink-while-open, and memory-mapped writable files (`mmap
MAP_SHARED PROT_WRITE`). These operations require reading existing content, modifying it,
writing a new arena, publishing the new arena as the current version, and discarding the
old arena — a copy-on-write shadow operation.

**The shim exists so any POSIX-shaped caller (libc, SimpleOS userspace, external tools)
can target NVFS without knowing about arenas.** It is intentionally slow for random-write
workloads and intentionally fast for read-mostly or append-heavy workloads.

**Opt-in discipline:** callers never receive the POSIX shim accidentally. They must:

1. Mount `DriverType::NvfsPosix` explicitly (not `DriverType::Nvfs`).
2. Or query `driver.probe(Capability::PosixCompat)` and receive `Some(Extension::PosixCompat(...))`.

A pure NVFS-native mount returns `None` from `probe(Capability::PosixCompat)`. The shim
is never silently inserted by the VFS layer.

---

## 2. Placement

```
# Trait contract — main repo (always compiled)
src/lib/nogc_sync_mut/fs/nvfs_posix/
    posix_driver.spl       # NvfsPosixDriver struct implementing FsDriver
    posix_handle.spl       # PosixFileHandle, fd table, open-file table
    posix_ops.spl          # POSIX operation translation functions

# Implementation body — NVFS submodule (compiled only when submodule is present)
examples/nvfs/src/posix/
    cow_engine.spl         # COW shadow arena machinery
    truncate.spl           # ftruncate implementation
    mmap_emul.spl          # mmap MAP_SHARED emulation via page-fault shadow
    posix_compat_ext.spl   # PosixCompatExt struct (implements probe response)
```

The main-repo side (`src/lib/nogc_sync_mut/fs/nvfs_posix/`) defines only the
`NvfsPosixDriver` struct and its trait implementation signatures. The actual arena
manipulation lives in the submodule. This keeps the main repo free of NVFS internals.

---

## 3. Registration in the driver interface

`NvfsPosixDriver` is a sibling to `NvfsDriver` in the `DriverInstance` enum:

```
enum DriverInstance:
    Fat32(Fat32Driver)
    Nvfs(NvfsDriver)
    NvfsPosix(NvfsPosixDriver)   # ← the POSIX shim
    RamFs(RamFsDriver)
```

Users mount either `NvfsDriver` (native, fast) or `NvfsPosixDriver` (POSIX compat, slow
for random writes) on a given path. Both can coexist on different mount points. A process
that wants native semantics mounts `NvfsDriver`; a process that runs legacy POSIX code
mounts `NvfsPosixDriver`.

`NvfsPosixDriver.probe(Capability::PosixCompat)` returns
`Some(Extension::PosixCompat(PosixCompatExt { ... }))`.

`NvfsDriver.probe(Capability::PosixCompat)` returns `None`.

---

## 4. POSIX operation translation table

For each POSIX operation: the native NVFS approach, the shim implementation, performance
cost, and correctness caveats.

### 4.1 `open(O_CREAT)` — create new file

| | |
|---|---|
| **Native NVFS** | `arena_create(class, flags)` → new arena |
| **Shim** | Allocate a new arena via `arena_create`. Record in the open-file table with `fd_state = Growing`. |
| **Cost** | O(1) — same as native. No amplification. |
| **Caveats** | If `O_EXCL`, check the directory B-tree for existing entry first. |

### 4.2 `open(O_RDONLY)` — open existing file for read

| | |
|---|---|
| **Native NVFS** | `arena_readv` handle |
| **Shim** | Look up the manifest entry, return an `arena_readv` handle. |
| **Cost** | O(1). No amplification. Fast path. |
| **Caveats** | None. |

### 4.3 `pwrite(fd, buf, off)` — write at arbitrary offset

| | |
|---|---|
| **Native NVFS** | Not supported directly; all writes are append-only. |
| **Shim** | 1. `arena_readv(0..off)` → read prefix. 2. Append `buf`. 3. `arena_readv(off+len..end)` → read suffix. 4. Write new arena with prefix + buf + suffix via `arena_append`. 5. `arena_seal`. 6. Publish new arena in manifest (atomic CAS on manifest pointer). 7. `arena_discard` old arena (deferred if other fds are open). |
| **Cost** | ~2× write amplification for small random writes. Full-file rewrite for worst case. |
| **Caveats** | For sequential appends at end of file (`off == file_size`): fast path via native `arena_append` without CoW. Detect by checking `off == fd.size`. |

### 4.4 `ftruncate(fd, len)` — truncate file

| | |
|---|---|
| **Native NVFS** | Not supported (arenas are immutable once sealed). |
| **Shim — shrink (`len < current_size`)** | `arena_readv(0..len)` + `arena_seal` new shorter arena. Publish new arena. Discard old. |
| **Shim — extend (`len > current_size`)** | `arena_readv(0..current_size)` + append `len - current_size` zero bytes + `arena_seal`. Publish. |
| **Cost** | O(len) — must copy existing data into new arena. |
| **Caveats** | Extending a large file by a small amount still requires full-file copy if the active arena is sealed. If the file is still in `Growing` state (not sealed), zero-padding can be appended directly. |

### 4.5 `rename(old, new)` — atomic rename

| | |
|---|---|
| **Native NVFS** | Manifest atomic swap via NVFS pmap root CAS. |
| **Shim** | Direct map to `NvfsDriver.rename` — same underlying atomic CAS on the directory B-tree. |
| **Cost** | O(1). Fast path; no data copy. |
| **Caveats** | POSIX rename-over-existing: atomically replace `new` if it exists. The shim must unlink the displaced entry within the same transaction, matching POSIX atomicity guarantee. |

### 4.6 `unlink(path)` with open handle

| | |
|---|---|
| **Native NVFS** | `arena_discard` is immediate when reference count drops to zero. |
| **Shim** | Mark the manifest entry as `dead` (removed from directory) but increment the arena's in-memory ref count. The arena is physically discarded only when the last fd referencing it is closed. |
| **Cost** | O(1) for the unlink itself. Arena discard is deferred. |
| **Caveats** | The fd table must track which arenas are "unlinked but still open". On process crash, recovery must discard these arenas (they are not reachable from any directory entry). |

### 4.7 `mmap(MAP_SHARED, PROT_WRITE)` — writable shared mapping

| | |
|---|---|
| **Native NVFS** | Not supported (arenas are append-only). |
| **Shim** | 1. Allocate a COW shadow arena. Pre-populate shadow with current file content via `arena_clone_range`. 2. Map shadow arena pages into the process address space. 3. Page-fault handler intercepts writes to shadow pages. 4. On `msync(MS_SYNC)` or `munmap`: flush dirty pages from shadow arena → new sealed arena → manifest publish → discard old arena and shadow. |
| **Cost** | Shadow arena pre-population: O(file_size). Each page written: O(1) (page already in shadow). `msync`: O(dirty_pages). |
| **Caveats** | MAP_SHARED across multiple processes is not supported (§9). MAP_PRIVATE (copy-on-write semantics per-process) does not need the shim — it is already file-read-only. |

### 4.8 `link(old, new)` — hard link

| | |
|---|---|
| **Native NVFS** | Increment arena refcount via reflink (§7 of nvfs_design_v2.md). |
| **Shim** | Call `ReflinkExt.reflink` on the underlying arena. Add a new directory entry pointing at the same arena. Increment inode link count. |
| **Cost** | O(1) — metadata only. |
| **Caveats** | On write via either path, CoW creates diverging arenas. Hard links share data until the first write. |

### 4.9 `fsync(fd)` — flush to durable storage

| | |
|---|---|
| **Native NVFS** | `arena_fua_append` (force-unit-access flag) or WAL sync. |
| **Shim** | If fd is in `Growing` state: issue `arena_fua_append` no-op flush (forces NVMe write buffer to persistent media). If fd is sealed: the seal transaction already guarantees durability; `fsync` is a no-op. |
| **Cost** | O(1). No amplification. |
| **Caveats** | `fdatasync` vs `fsync`: `fdatasync` skips metadata (atime, mtime) flush; both are equivalent in NVFS because the manifest update is always atomic. |

### 4.10 `lseek(fd, off, whence)` — seek

| | |
|---|---|
| **Native NVFS** | Not a native concept; NVFS reads are positional (`arena_readv(offset, len)`). |
| **Shim** | Maintain `fd.current_offset` in the open-file table. Update on `lseek`. No NVFS call. |
| **Cost** | O(1). Pure in-memory bookkeeping. |
| **Caveats** | `SEEK_HOLE` / `SEEK_DATA` (sparse file awareness) are not supported (§9). |

### 4.11 `readdir` — list directory entries

| | |
|---|---|
| **Native NVFS** | Walk the directory B-tree (DIR_ITEM entries in the FS tree). |
| **Shim** | Direct delegation to `NvfsDriver.readdir` — same B-tree walk. |
| **Cost** | O(entries). No amplification. |
| **Caveats** | None specific to the shim. |

---

## 5. Failure modes and acceptable workloads

### 5.1 Write amplification analysis

| Workload | Amplification | Notes |
|---|---|---|
| Sequential append to open file | 1× | Fast path: `arena_append` directly |
| Read-mostly, occasional overwrite | ~2× | CoW per overwrite region |
| Small random writes on large file | Up to file_size / write_size | Full-file rewrite in worst case |
| Random writes on 1 GiB file, 4 KiB writes | ~250,000× | Unacceptable; use native NVFS API |
| `cp file1 file2` (full file copy) | 1× | Sequential read + sequential write |
| `sed -i` on 1 MiB config file | ~2× | Full-file CoW once |

### 5.2 Acceptable workloads for the POSIX shim

- **Read-mostly** — databases opening NVFS files for read; ML model loading (svllm uses
  native API, but a legacy POSIX loader could use the shim).
- **Append-heavy** — log files, WAL files where writes are always at end of file.
- **Small files with infrequent overwrites** — config files, metadata blobs (< 1 MiB).
- **One-time writes** — tools that write a file once, seal it, and never overwrite.

### 5.3 Avoid with the POSIX shim

- **Random-write hot loops** — databases doing random page updates, key-value stores with
  in-place B-tree updates. These should use the native NVFS API directly.
- **Large-file frequent-overwrite** — video editing, database UNDO logs. Native API.
- **High-IOPS low-latency** — NVMe latency target is sub-100 µs; a CoW shadow adds
  one full-file read + write. Latency becomes milliseconds. Native API.

---

## 6. Open handle semantics

### 6.1 Open-file table

```
struct PosixFileHandle:
    arena_id: ArenaId           # currently active arena for this file
    current_offset: u64         # for lseek / sequential read emulation
    flags: OpenFlags            # O_RDONLY, O_WRONLY, O_RDWR, O_APPEND, ...
    ref_count: u32              # for dup() / fork() sharing
    state: FdState

enum FdState:
    ReadOnly                    # arena is sealed; reads only
    Growing                     # arena is open for append (O_CREAT or O_WRONLY new)
    CowShadow(ArenaId)          # shadow arena active for pwrite emulation
    MmapShadow(ArenaId, VirtAddr, usize)   # shadow arena + mapped region
```

### 6.2 Ref-counted arena handles

When multiple file descriptors reference the same file (via `dup`, `fork`, or `link`),
the shim maintains a per-file-object ref count on the arena. An `arena_discard` is issued
only when the last fd referencing the arena is closed and the file is unlinked.

### 6.3 O_APPEND fast path

If `fd.flags` includes `O_APPEND`, all `write` calls are treated as appends at the
current end of the arena. The shim issues `arena_append` directly — no CoW shadow. This
is the same throughput as native NVFS.

```
fn posix_write(fd: &mut PosixFileHandle, buf: &[u8]) -> Result<i64, FsError>:
    if fd.flags.has(O_APPEND):
        # fast path: no COW needed
        arena_append(fd.arena_id, buf)
    else:
        # general path: COW shadow
        posix_pwrite_cow(fd, buf, fd.current_offset)
```

---

## 7. Interaction with snapshots and reflinks

The POSIX shim is built on top of the NVFS native driver. When the underlying NVFS
volume supports snapshots (`Capability::Snapshot`) and reflinks (`Capability::Reflink`),
the shim inherits these capabilities:

- **`cp --reflink=always file1 file2`** via the POSIX shim: the VFS layer calls
  `ReflinkExt.reflink` on the underlying native driver — O(1) metadata op.
- **Snapshot of a POSIX-shim volume:** The shim ensures all COW shadows are flushed
  (i.e., all `pwrite` operations committed) before the snapshot is taken. Snapshots are
  consistent at transaction boundaries.
- **Send/receive of a POSIX-shim volume:** Delegated to `SendRecvExt` on the native
  driver. The shim's files are NVFS arenas under the hood; the send stream encodes them
  natively. The receiver replays arenas; the POSIX shim on the target can mount and
  present them as POSIX files.

The POSIX shim does not support `Capability::Dedup` (dedup daemon cannot guarantee
byte-equality of COW shadow arenas). It does not support `Capability::Encrypt`
independently — if the underlying native volume is encrypted, the shim transparently
reads/writes ciphertext via the native driver's decrypt/encrypt path.

---

## 8. Testing strategy

### 8.1 POSIX compliance subset

Run the following test suites against an NVFS-POSIX mount:

| Suite | Focus | Target pass rate |
|---|---|---|
| xfstests `generic/` | Generic POSIX FS tests | ≥ 90% (excluding unsupported ops) |
| `pjdfstest` | POSIX conformance (chmod, chown, truncate, rename) | ≥ 95% |
| `fsstress` | Stress: concurrent open/write/unlink/rename | No deadlock; no data loss |
| ext4 semantics comparison | Compare shim output to ext4 on same operations | Match on all supported ops |

Explicit skip list (documented in the test harness): `O_DIRECT`, `FALLOC_FL_PUNCH_HOLE`,
`MAP_FIXED`, `MAP_PRIVATE` with `PROT_WRITE`, `SEEK_HOLE`, `SEEK_DATA` (see §9).

### 8.2 Write amplification benchmarks

For every POSIX operation in §4, measure:
- Bytes written to NVMe per logical byte written by the caller.
- Latency at p50 / p99 for 4 KiB random writes on a 1 GiB file.
- Throughput for sequential append (must match native NVFS within 5%).

### 8.3 Crash-consistency tests

- Power-cut simulation via `dm-flakey` or equivalent.
- After crash, mount NVFS-POSIX and verify: no dangling arenas, no orphaned unlinked-but-open files, all committed writes visible, all uncommitted writes absent.

---

## 9. Not supported

The following operations are not supported by the POSIX shim. Callers needing these
should use the native NVFS API:

| Operation | Reason | Native alternative |
|---|---|---|
| `O_DIRECT` | Bypasses shim's COW buffer; semantics undefined | `arena_readv` / `arena_append` |
| `fallocate(FALLOC_FL_PUNCH_HOLE)` | Sparse punching requires native arena_discard_range | `arena_discard_range` (native) |
| `fallocate(FALLOC_FL_KEEP_SIZE)` | Preallocation without write is a no-op in NVFS; extents are not preallocated | Use `arena_reserve_size` (native) |
| `MAP_FIXED` | Fixed-address mapping conflicts with COW shadow arena paging | Native arena_readv into pre-mapped buffer |
| `MAP_PRIVATE` + `PROT_WRITE` | Copy-on-write is per-process memory; does not need NVFS interaction | Plain mmap of a read-only arena |
| `SEEK_HOLE` / `SEEK_DATA` | NVFS arenas are dense; no sparse-file hole tracking | N/A (arenas have no holes) |
| Multi-process `MAP_SHARED` | COW shadow arena is per-process; cross-process consistency undefined | IPC via native NVFS or a shared-memory primitive |
| `ioctl(FS_IOC_GETFLAGS)` | NVFS does not expose ext2-style inode flags | Query `SnapshotExt` / `ChecksumExt` directly |

---

## 10. Capability advertisement

`NvfsPosixDriver.probe(Capability::PosixCompat)` returns:

```
Some(Extension::PosixCompat(PosixCompatExt {
    fn posix_compat_enabled() -> bool { true }
    fn supported_ops() -> PosixOpSet  # bitmask of which POSIX ops are supported
    fn unsupported_ops() -> PosixOpSet  # bitmask of explicitly-not-supported ops
}))
```

`NvfsDriver.probe(Capability::PosixCompat)` returns `None`.

Callers can distinguish native from shim at runtime:

```
match mount.driver:
    DriverInstance::Nvfs(d) =>
        # native NVFS: fast, no POSIX compat
        assert(d.probe(Capability::PosixCompat) == None)
    DriverInstance::NvfsPosix(d) =>
        # POSIX shim: slow for random writes, full POSIX compat
        val ext = d.probe(Capability::PosixCompat).unwrap()
        match ext:
            Extension::PosixCompat(p) => log("shim enabled: {p.posix_compat_enabled()}")
            _                         => unreachable()
```

This explicit dispatch ensures the caller always knows which semantics they are getting.
There is no silent fallback from native to shim or vice versa.

---

## 11. COW shadow engine internals

The COW shadow engine is the core mechanism behind `pwrite`, `ftruncate`, and
`mmap MAP_SHARED` emulation. It lives in `examples/nvfs/src/posix/cow_engine.spl`.

### 11.1 Shadow arena lifecycle

```
enum ShadowState:
    Idle                          # no shadow; fd is read-only or in Growing state
    Active(ArenaId, u64, u64)     # shadow arena id, shadow_start_off, shadow_len
    Dirty(ArenaId, u64, u64)      # shadow has been written; pending flush
    Flushing                      # msync or close in progress; waiting for seal
```

A shadow is created lazily on the first `pwrite` call to a sealed arena:

```
fn ensure_shadow(fd: &mut PosixFileHandle) -> Result<ArenaId, FsError>:
    match fd.state:
        FdState::CowShadow(shadow_id) => Ok(shadow_id)
        FdState::ReadOnly =>
            val shadow = arena_create(GENERAL_MUTABLE, ArenaHint::Temp)
            # Clone entire file content into shadow
            arena_clone_range(fd.arena_id, 0, shadow, 0, fd.size)
            fd.state = FdState::CowShadow(shadow)
            Ok(shadow)
        FdState::Growing => Ok(fd.arena_id)   # still open; append directly
        FdState::MmapShadow(s, _, _) => Ok(s)
```

### 11.2 Shadow flush and manifest publish

When the shadow is complete (on `close`, `fsync`, or `msync`):

```
fn flush_shadow(fd: &mut PosixFileHandle) -> Result<(), FsError>:
    val shadow = match fd.state:
        FdState::CowShadow(s) | FdState::Dirty(s, _, _) => s
        _                                                 => return Ok(())
    arena_seal(shadow)
    # Publish new arena as the canonical version of this file
    atomic_pointer_record_publish(
        META_DURABLE,
        "file:<inode_id>",
        shadow,
        fd.expected_gen
    )?
    # Discard old arena (deferred if other fds still reference it)
    decrement_arena_refcount(fd.arena_id)
    fd.arena_id = shadow
    fd.state = FdState::ReadOnly
    Ok(())
```

The `atomic_pointer_record_publish` CAS ensures that concurrent writers do not silently
clobber each other. If two processes both hold `pwrite` shadows open on the same file,
the second to flush will see a generation mismatch and return `FsError::Transient` —
the caller must reload and retry (last-writer-wins semantics, matching POSIX `O_RDWR`
behaviour on shared files without explicit locking).

### 11.3 Shadow size limit

A shadow arena may not exceed `SHADOW_MAX_SIZE` (default: 1 GiB). Writes to a file
larger than `SHADOW_MAX_SIZE` via the POSIX shim fail with `FsError::NoSpace`. Callers
targeting large files must use the native NVFS API. This limit is a mount option:

```
mount -t nvfs_posix -o shadow_max_size=4g /dev/nvme0n1 /mnt/posix
```

---

## 12. Open questions

- **OQ-1:** Should the shadow flush be synchronous (blocking until NVMe confirms durable)
  or asynchronous (returns to caller after shadow is queued)? Current plan: synchronous
  on `close` and `fsync`; asynchronous on `msync(MS_ASYNC)`.

- **OQ-2:** Last-writer-wins on concurrent `pwrite` — is this acceptable, or should the
  shim provide optional advisory locking (`flock`)? Advisory locking requires a
  per-inode lock table in the shim state.

- **OQ-3:** `SHADOW_MAX_SIZE` default — 1 GiB is conservative. Should it be
  configurable per file class (e.g., unlimited for `META_DURABLE` class files)?

- **OQ-4:** `MAP_PRIVATE PROT_WRITE` — currently routed to the OS page cache (read
  NVFS arena → OS maps → private CoW in OS memory). Is this correct? The process's
  writes do not reach NVFS. If a caller expects `MAP_PRIVATE` writes to eventually
  persist (e.g., via a subsequent `write` call), they must use `O_RDWR pwrite` instead.

- **OQ-5:** xfstests target pass rate — 90% is the target (§8.1). Which tests are
  expected to fail? Document the skip list before N4 ships so the CI gate is clear.

- **OQ-6:** `dup2` / `fork` with open shadow — after `fork`, both parent and child hold
  the same `PosixFileHandle`. The shadow arena ref count must be incremented. On `close`
  in child, ref count decrements but no flush occurs until the last holder closes.
  Semantics: last-close-wins. Is this the right model?

- **OQ-7:** `sendfile(fd_in, fd_out, off, len)` — should the shim intercept `sendfile`
  and translate it to `arena_readv` + `arena_append` on the destination? This would
  make `sendfile` between two NVFS-POSIX fds as efficient as a native reflink.

