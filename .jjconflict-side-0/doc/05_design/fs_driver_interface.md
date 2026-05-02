# SimpleOS FS Driver Interface Design

> **Status:** Phase 9-extend design deliverable (2026-04-18).
>
> **Related designs (cross-refs):**
> - `doc/05_design/nvfs_design_v2.md` — NVFS native driver; implements `DriverInstance::Nvfs`.
> - `doc/05_design/nvfs_posix_wrapper.md` — POSIX-over-NVFS shim; implements
>   `DriverInstance::NvfsPosix`.
> - `doc/01_research/fs_driver_interface.md` — research doc; §3 justifies the E' + G
>   recommendation adopted here.

---

## 1. Decision

**Adopted design: Option E' (enum-wrapped extension handle) + G-inspired `DriverInstance`
enum for the heterogeneous mount table.**

Source: `doc/01_research/fs_driver_interface.md` §3.6 recommendation.

Rationale in brief:

1. **No `dyn`** — Simple's `nogc_sync_mut` layer has no allocator and no virtual dispatch.
   E' uses only concrete structs and enum variants. All dispatch is by exhaustive `match`.
2. **Heterogeneous mount table** — A single `Vec<MountEntry>` can hold FAT32, NVFS-native,
   and NVFS-POSIX mounts simultaneously via the `DriverInstance` enum.
3. **Closed-world capability list** — The `Extension` enum is owned by the VFS layer. New
   capabilities add a new variant and a new concrete struct; the compiler flags all
   unhandled match arms.
4. **FAT32 zero-overhead** — FAT32 implements `FsDriver` with `probe` returning `None` for
   all caps and `capabilities()` returning an empty bitmask. No extension struct is ever
   allocated for FAT32 mounts.

Rejected alternatives:
- **Option F (generic specialization):** `Vec<VfsMount<???>>` is impossible — cannot hold
  both `VfsMount<Fat32Driver>` and `VfsMount<NvfsDriver>` in the same list.
- **Option G (handle pool / fd table):** Op-ID assignment is dynamic and collision-prone;
  closure-based dispatch does not map cleanly to Simple's `nogc_sync_mut`.
- **`dyn FsDriver`:** Prohibited by project rules (CLAUDE.md: "no dyn").

---

## 2. Core `FsDriver` trait

Defined in `src/lib/nogc_sync_mut/fs_driver/driver.spl`. All operations are synchronous
(blocking). The async sibling is described in §10.

```
# src/lib/nogc_sync_mut/fs_driver/driver.spl

trait FsDriver:
    # Lifecycle
    fn mount(opts: MountOptions) -> Result<(), FsError>
    fn unmount() -> Result<(), FsError>
    fn remount(opts: MountOptions) -> Result<(), FsError>
    fn statfs() -> Result<FsStats, FsError>

    # Namespace operations
    fn open(path: Path, flags: OpenFlags) -> Result<FileHandle, FsError>
    fn close(handle: FileHandle) -> Result<(), FsError>
    fn read(handle: FileHandle, offset: i64, buf: &mut [u8]) -> Result<i64, FsError>
    fn write(handle: FileHandle, offset: i64, buf: &[u8]) -> Result<i64, FsError>
    fn stat(handle: FileHandle) -> Result<FileStat, FsError>
    fn readdir(handle: DirHandle) -> Result<Vec<DirEntry>, FsError>
    fn unlink(path: Path) -> Result<(), FsError>
    fn rename(old: Path, new: Path) -> Result<(), FsError>
    fn mkdir(path: Path, mode: u32) -> Result<(), FsError>
    fn rmdir(path: Path) -> Result<(), FsError>
    fn symlink(target: Path, link: Path) -> Result<(), FsError>
    fn readlink(path: Path) -> Result<Path, FsError>

    # Extension probe
    fn probe(cap: Capability) -> Option<Extension>
    fn capabilities() -> CapabilitySet   # bitmask for cheap pre-check before probe
```

### 2.1 Mount/unmount concurrency

The mount table holds a per-entry reader-writer spinlock:
- Readers (`open`, `read`, `stat`, `readdir`): hold read lock.
- Writers (`write`, `create`, `unlink`, `rename`): hold write lock.
- Mount/unmount/remount: hold exclusive write lock; drain all readers first.

### 2.2 `FsStats`

```
struct FsStats:
    total_bytes: u64
    free_bytes: u64
    used_bytes: u64
    inodes_total: u64
    inodes_free: u64
    block_size: u32
    fs_type: FsType   # enum: Fat32, NvfsNative, NvfsPosix, RamFs, ...
```

### 2.3 `FileStat`

```
struct FileStat:
    inode: u64
    size: u64
    blocks: u64
    block_size: u32
    mode: u32
    uid: u32
    gid: u32
    nlinks: u32
    atime_ns: u64
    mtime_ns: u64
    ctime_ns: u64
    birth_time_ns: u64
```

---

## 3. `DriverInstance` enum and mount table

Defined in `src/lib/nogc_sync_mut/fs_driver/mount_table.spl`.

```
# src/lib/nogc_sync_mut/fs_driver/mount_table.spl

enum DriverInstance:
    Fat32(Fat32Driver)
    Nvfs(NvfsDriver)
    NvfsPosix(NvfsPosixDriver)
    RamFs(RamFsDriver)
    # future: Ext4Compat, Iso9660, ...

struct MountEntry:
    id: MountId        # u32 mount table index
    mount_point: Path
    driver: DriverInstance
    opts: MountOptions

struct MountTable:
    entries: Vec<MountEntry>
```

### 3.1 VFS dispatch pattern

Every VFS operation dispatches via an exhaustive `match` on `DriverInstance`. Example for
`open`:

```
fn vfs_open(mount: &MountEntry, path: Path, flags: OpenFlags) -> Result<FileHandle, FsError>:
    match &mount.driver:
        DriverInstance::Fat32(d)     => d.open(path, flags)
        DriverInstance::Nvfs(d)      => d.open(path, flags)
        DriverInstance::NvfsPosix(d) => d.open(path, flags)
        DriverInstance::RamFs(d)     => d.open(path, flags)
```

This is verbose but safe. Adding a new driver type:
1. Add a variant to `DriverInstance`.
2. The compiler flags every `match` that lacks the new variant.
3. Implement each arm.

No dynamic dispatch. No vtable. No `dyn`.

### 3.2 Mount table lookup

```
fn mount_lookup(table: &MountTable, path: Path) -> Option<&MountEntry>:
    # Longest-prefix match over mount_point fields
    table.entries
        .filter(|e| path.starts_with(e.mount_point))
        .max_by_key(|e| e.mount_point.len())
```

---

## 4. Extension probe

```
# Extension enum — owned by VFS layer, in fs_driver/extension.spl

enum Extension:
    Snapshot(SnapshotExt)
    Clone(CloneExt)
    Dedup(DedupExt)
    Checksum(ChecksumExt)
    SelfHeal(SelfHealExt)
    SendReceive(SendRecvExt)
    Scrub(ScrubExt)
    Compress(CompressExt)
    Encrypt(EncryptExt)
    Quota(QuotaExt)
    Reflink(ReflinkExt)
    Xattr(XattrExt)
    Acl(AclExt)
    PosixCompat(PosixCompatExt)
    Cow(CowExt)
    Atime(AtimeExt)
    HardLink(HardLinkExt)
    SymLink(SymLinkExt)
    Sparse(SparseExt)
    CaseSensitive(CaseSensitiveExt)
    Verity(VerityExt)
    L2Arc(L2ArcExt)
```

### 4.1 Probe pattern

```
# Caller checks cheaply via bitmask, then probes for the concrete handle:
val caps = driver.capabilities()
if caps.has(Capability::Snapshot):
    match driver.probe(Capability::Snapshot):
        Some(Extension::Snapshot(ext)) =>
            ext.create(vol_id, "snap-2026-04-18")
        None =>
            return Err(FsError::Unsupported)
```

### 4.2 Example extension structs (no `dyn`)

```
struct SnapshotExt:
    # The driver_ref is concrete — *NvfsDriver, not a trait object
    fn create(name: Str) -> Result<SnapshotId, FsError>
    fn delete(id: SnapshotId) -> Result<(), FsError>
    fn list() -> Result<Vec<SnapshotId>, FsError>
    fn info(id: SnapshotId) -> Result<SnapshotInfo, FsError>

struct ReflinkExt:
    fn reflink(src_fd: FileHandle, src_off: u64,
               dst_fd: FileHandle, dst_off: u64,
               len: u64) -> Result<(), FsError>
    fn reflink_extent_same(src: ArenaId, src_off: u64,
                           dst: ArenaId, dst_off: u64,
                           len: u64) -> Result<(), FsError>

struct SendRecvExt:
    fn send(snap: SnapshotId, parent: Option<SnapshotId>,
            raw: bool) -> Result<SendStream, FsError>
    fn receive(stream: RecvStream) -> Result<(), FsError>

struct ScrubExt:
    fn start(throttle_pct: u8) -> Result<ScrubHandle, FsError>
    fn cancel(h: ScrubHandle) -> Result<(), FsError>
    fn status(h: ScrubHandle) -> Result<ScrubStatus, FsError>

struct EncryptExt:
    fn set_key(key: EncryptionKey) -> Result<(), FsError>
    fn change_key(new_key: EncryptionKey) -> Result<(), FsError>
    fn status() -> Result<EncryptStatus, FsError>

struct ChecksumExt:
    fn algo() -> ChecksumAlgo
    fn verify(handle: FileHandle, off: u64, len: u64) -> Result<bool, FsError>

struct PosixCompatExt:
    fn posix_compat_enabled() -> bool
    # see nvfs_posix_wrapper.md for full shim API
```

---

## 5. Capability enum

22 entries. Defined in `src/lib/nogc_sync_mut/fs_driver/capability.spl`.

```
enum Capability:
    COW             # Copy-on-write writes; no in-place overwrite
    Snapshot        # Point-in-time consistent snapshot of a volume
    Clone           # Writable COW clone of a volume
    Dedup           # Offline content-hash deduplication with extent sharing
    Checksum        # Per-block checksum verification
    SelfHeal        # Automatic repair via redundant copies on mismatch
    SendReceive     # Incremental stream serialization for backup/replication
    Compress        # Transparent per-file compression
    Encrypt         # Transparent at-rest encryption
    Quota           # Per-volume space quota and reservation
    Reflink         # COW file-range clone (O(1) metadata op)
    Atime           # Full access-time tracking (not just access-date)
    Xattr           # Extended attributes
    Acl             # POSIX ACLs
    PosixCompat     # POSIX random-write/truncate emulation over NVFS arenas
    HardLink        # Multiple directory entries pointing at same inode
    SymLink         # Symbolic links
    Sparse          # Sparse files (holes map to zero, no physical block)
    CaseSensitive   # Case-sensitive filename matching
    Verity          # fs-verity / immutable signed file trees
    L2Arc           # Secondary read cache (SSD tier)
    Scrub           # Background online data integrity verification
```

`CapabilitySet` is a `u32` bitmask (22 bits used; 10 reserved for future). Drivers set
bits in `capabilities()` for the caps they support; callers check cheaply before calling
`probe`.

---

## 6. Per-driver capability table

| Capability | FAT32 | NVFS-native (N4+) | NVFS-POSIX shim |
|---|---|---|---|
| COW | No | Yes | Yes (shim uses CoW internally) |
| Snapshot | No | Yes | Yes (snapshot of shim state) |
| Clone | No | Yes | Yes |
| Dedup | No | N6+ | No |
| Checksum | No | Yes | Yes (inherits from NVFS) |
| SelfHeal | No | N4+ | No (inherits from NVFS native) |
| SendReceive | No | N4+ | Yes (snapshot-based) |
| Compress | No | future | No |
| Encrypt | No | N7+ | No |
| Quota | No | future | No |
| Reflink | No | N3+ | Yes |
| Atime | Partial (date only) | Yes | Yes |
| Xattr | No | Yes | Yes |
| Acl | No | Yes | Yes |
| PosixCompat | No | No | Yes |
| HardLink | No | Yes | Yes |
| SymLink | No | Yes | Yes |
| Sparse | No | Yes | No (shim materializes zeros) |
| CaseSensitive | No (FAT32 case-insensitive) | Yes | Yes |
| Verity | No | future | No |
| L2Arc | No | future | No |
| Scrub | No | N4+ | No |

---

## 7. Error model

Defined in `src/lib/nogc_sync_mut/fs_driver/error.spl`.

```
enum FsError:
    Unsupported         # operation/capability not supported by this driver
    NotFound            # path or handle does not exist
    PermissionDenied    # caller lacks permission
    IoError(i32)        # hardware I/O error; inner = device error code
    NoSpace             # out of space on device
    InvalidArgument     # bad argument (bad offset, null handle, etc.)
    TooManyHandles      # open handle limit reached
    Transient(i32)      # retryable error; inner = contention hint code
    Corrupt             # data integrity failure (checksum mismatch, bad magic)
    DeviceGone          # device removed while in use
    VersionMismatch     # superblock version incompatible (v1 vs v2)
    WouldBlock          # non-blocking call would block (for async callers)
    Interrupted         # syscall interrupted (for signal-aware callers)
    AlreadyExists       # create of existing path with O_EXCL
    Busy                # resource is busy (e.g., unmount while open handles exist)
```

### 7.1 POSIX errno mapping

| FsError | errno |
|---|---|
| `Unsupported` | `ENOTSUP` |
| `NotFound` | `ENOENT` |
| `PermissionDenied` | `EACCES` |
| `IoError(_)` | `EIO` |
| `NoSpace` | `ENOSPC` |
| `InvalidArgument` | `EINVAL` |
| `TooManyHandles` | `EMFILE` |
| `Transient(_)` | `EAGAIN` |
| `Corrupt` | `EIO` |
| `DeviceGone` | `ENXIO` |
| `VersionMismatch` | `EINVAL` |
| `WouldBlock` | `EAGAIN` |
| `Interrupted` | `EINTR` |
| `AlreadyExists` | `EEXIST` |
| `Busy` | `EBUSY` |

Translation happens at the syscall boundary in the VFS dispatch layer, not inside the
driver. Drivers always return `FsError`; the VFS layer converts.

---

## 8. Driver lifecycle

### 8.1 Mount

```
fn vfs_mount(device: DevicePath, mount_point: Path,
             driver_type: DriverType, opts: MountOptions) -> Result<MountId, FsError>:
    val driver = match driver_type:
        DriverType::Fat32     => DriverInstance::Fat32(Fat32Driver::new(device))
        DriverType::Nvfs      => DriverInstance::Nvfs(NvfsDriver::new(device))
        DriverType::NvfsPosix => DriverInstance::NvfsPosix(NvfsPosixDriver::new(device))
        DriverType::RamFs     => DriverInstance::RamFs(RamFsDriver::new())
    vfs_driver_mount(&driver, opts)?
    mount_table.insert(MountEntry { driver, mount_point, opts })
```

### 8.2 Unmount

```
fn vfs_unmount(id: MountId) -> Result<(), FsError>:
    val entry = mount_table.get(id)?
    if entry.has_open_handles():
        return Err(FsError::Busy)
    vfs_driver_unmount(&entry.driver)?
    mount_table.remove(id)
```

### 8.3 Background threads

Background jobs (scrub, dedup daemon, ARC shrink, balance) run as separate OS threads
or actors (in `nogc_async_mut` if async). They hold a weak reference to the
`MountEntry`; if the mount is unmounted, the weak reference fails and the thread exits.

```
# Scrub thread lifecycle (NVFS only)
fn nvfs_start_scrub(mount: MountId, throttle: u8) -> Result<ScrubHandle, FsError>:
    val ext = probe_or_err(mount, Capability::Scrub)?
    match ext:
        Extension::Scrub(s) => s.start(throttle)
        _                   => Err(FsError::Unsupported)
```

---

## 9. Mount-time capability negotiation

Inspired by FUSE `conn_info->capable/want` (research doc §1.7). The mount process
performs a mutual advertisement:

1. **Driver advertises** — `driver.capabilities()` returns a `CapabilitySet` bitmask.
2. **Caller requests** — `MountOptions.want_caps: CapabilitySet` carries what the caller
   wants enabled.
3. **VFS intersects** — `active_caps = driver.capabilities() & opts.want_caps`. If a
   required capability (`opts.require_caps`) is absent from `active_caps`, mount fails
   with `FsError::Unsupported`.
4. **Stored** — `MountEntry.active_caps` is the negotiated set. Runtime `probe` calls
   only succeed for caps in `active_caps`.

```
struct MountOptions:
    read_only: bool
    want_caps: CapabilitySet    # capabilities caller would like
    require_caps: CapabilitySet # capabilities mount must have (else fail)
    extra: Map<Str, Str>        # driver-specific string options
```

Example: mounting NVFS-POSIX with required `PosixCompat` and optional `Snapshot`:
```
val opts = MountOptions {
    require_caps: CapabilitySet::of(Capability::PosixCompat),
    want_caps:    CapabilitySet::of(Capability::PosixCompat, Capability::Snapshot),
    ...
}
```

---

## 10. Async sibling trait

For use in `nogc_async_mut` contexts (async actors, async I/O). Lives in
`src/lib/nogc_async_mut/fs_driver/`.

```
# src/lib/nogc_async_mut/fs_driver/async_driver.spl

trait AsyncFsDriver:
    async fn open(path: Path, flags: OpenFlags) -> Result<FileHandle, FsError>
    async fn close(handle: FileHandle) -> Result<(), FsError>
    async fn read(handle: FileHandle, offset: i64, buf: &mut [u8]) -> Result<i64, FsError>
    async fn write(handle: FileHandle, offset: i64, buf: &[u8]) -> Result<i64, FsError>
    async fn stat(handle: FileHandle) -> Result<FileStat, FsError>
    async fn readdir(handle: DirHandle) -> Result<Vec<DirEntry>, FsError>
    async fn unlink(path: Path) -> Result<(), FsError>
    async fn rename(old: Path, new: Path) -> Result<(), FsError>
    async fn probe(cap: Capability) -> Option<Extension>
    fn capabilities() -> CapabilitySet   # sync; metadata only
```

The async `DriverInstance` enum mirrors the sync one:

```
enum AsyncDriverInstance:
    Nvfs(AsyncNvfsDriver)
    NvfsPosix(AsyncNvfsPosixDriver)
    # FAT32 does not have an async implementation (no async use case for FAT32)
```

svllm uses `AsyncNvfsDriver` via `src/lib/gc_async_mut/nvfs_client/` (GPU async path).

---

## 11. SimpleOS migration plan

### Phase (a) — Introduce the trait (1 week)

- Create `src/lib/nogc_sync_mut/fs_driver/` with:
  - `driver.spl` — `FsDriver` trait
  - `mount_table.spl` — `DriverInstance`, `MountEntry`, `MountTable`
  - `capability.spl` — `Capability`, `CapabilitySet`
  - `extension.spl` — `Extension` enum + all `*Ext` structs (stubs)
  - `error.spl` — `FsError`
- All structs compile with `bin/simple build lint`. No driver implementations yet.

Files touched: 5 new files under `src/lib/nogc_sync_mut/fs_driver/`.

### Phase (b) — FAT32 behind the trait (2 weeks)

- Create `src/lib/nogc_sync_mut/fs/fat32/fat32_driver.spl` implementing `FsDriver`.
  - All extension `probe` calls return `None`.
  - `capabilities()` returns `CapabilitySet::empty()`.
  - Delegate all actual I/O to the existing FAT32 code in `examples/simple_os/`.
- Add `DriverInstance::Fat32(Fat32Driver)` to the enum.
- Keep the existing direct-call path: FAT32 callers in SimpleOS still call the old
  `fat32_*` functions. No callers updated yet.

Files touched: new `fat32_driver.spl`; extend `mount_table.spl`.

### Phase (c) — Swap userland to VFS calls (3 weeks)

- Update SimpleOS userspace callers from `fat32_open(...)` to `vfs_open(mount_id, ...)`.
- VFS layer dispatches to `DriverInstance::Fat32` which delegates to the old fat32 code.
- Mount table initialized at boot with a FAT32 mount at `/`.

Files touched: all files in `examples/simple_os/` that call `fat32_*` directly
(estimate 8–15 call sites).

### Phase (d) — Remove direct FAT32 path (1 week)

- Delete the old `fat32_*` free functions.
- All callers now go through VFS. FAT32 implementation lives only in `Fat32Driver`.

Files touched: cleanup of `examples/simple_os/arch/x86_64/` and related modules.

### Phase (e) — Plug NVFS in (N4 milestone)

- Add `DriverInstance::Nvfs(NvfsDriver)` and `DriverInstance::NvfsPosix(NvfsPosixDriver)`.
- NVFS mounts available alongside FAT32 mounts.
- The POSIX shim mount enables legacy userspace tools to target NVFS without changes.

Files touched: extend `mount_table.spl`; connect `examples/nvfs/` submodule to the
driver instance enum.

---

## 12. Module placement

```
src/lib/nogc_sync_mut/fs_driver/    # Trait contracts — main repo
    driver.spl                      # FsDriver trait
    mount_table.spl                 # DriverInstance, MountEntry, MountTable
    capability.spl                  # Capability enum, CapabilitySet
    extension.spl                   # Extension enum, *Ext structs
    error.spl                       # FsError

src/lib/nogc_sync_mut/fs/fat32/     # FAT32 driver impl — main repo
    fat32_driver.spl                # Fat32Driver implementing FsDriver
    # (delegates to existing FAT32 code in examples/simple_os/)

src/lib/nogc_sync_mut/fs/nvfs_posix/  # POSIX shim contract — main repo
    posix_driver.spl               # NvfsPosixDriver implementing FsDriver
    # (impl body in examples/nvfs/src/posix/ submodule)

src/lib/nogc_async_mut/fs_driver/   # Async sibling trait — main repo
    async_driver.spl               # AsyncFsDriver trait
    async_mount_table.spl          # AsyncDriverInstance, async dispatch

examples/simple_os/                # FAT32 implementation (existing, unchanged)
examples/nvfs/                     # NVFS implementation (submodule)
    src/driver/                    # NvfsDriver impl
    src/posix/                     # NvfsPosixDriver impl body
```

The trait contracts (`FsDriver`, `DriverInstance`, `Capability`, `Extension`, `FsError`)
live in the main repo so any caller can depend on them without depending on the driver
implementations. Implementations live in `examples/` submodules, which are optional
build targets.

---

## 13. Open questions

- **OQ-1:** Should `DriverInstance` variants be addable from `examples/` submodules, or
  is the closed-world assumption permanent? (Adding a new driver currently requires
  editing the main-repo enum — acceptable for now, but limits third-party drivers.)
- **OQ-2:** Is a `RamFs` driver needed in Phase (a) or can it wait until Phase (e)?
- **OQ-3:** Async FAT32 — is there a use case? Currently planned as sync-only.
- **OQ-4:** `CapabilitySet` as `u32` — will 22 bits be enough? Reserve top 10 bits for
  future.
- **OQ-5:** Should `probe` be fallible (`Result<Option<Extension>, FsError>`) to handle
  driver-side errors during extension initialization, or is `Option<Extension>` sufficient?
- **OQ-6:** Thread safety of `MountEntry` — currently a per-mount reader-writer spinlock.
  Fine-grained locking per inode or file handle may be needed for high-concurrency NVMe
  workloads under SimpleOS.
