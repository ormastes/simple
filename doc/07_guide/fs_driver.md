# FsDriver Developer Guide

How to add a new filesystem driver and how to consume drivers from an application.

**Source files:** `src/lib/nogc_sync_mut/fs_driver/`

---

## 1. Trait Contract

`FsDriver` (defined in `ops.spl`) is a synchronous, non-throwing trait. Every method returns `Result<T, FsError>`. There is no `dyn` dispatch and no vtable — callers match on `DriverInstance`.

### Lifecycle group

| Method | Purpose |
|--------|---------|
| `mount(opts: MountOptions) -> Result<(), FsError>` | Called once before any I/O. Must set internal `mounted` flag. |
| `unmount() -> Result<(), FsError>` | Flush and tear down. Return `FsError.Busy` if open handles remain. |
| `remount(opts: MountOptions) -> Result<(), FsError>` | Change mount options in place (e.g. ro→rw). |
| `statfs() -> Result<FsStatfs, FsError>` | Return volume-level capacity and inode counts. |

### File I/O group

| Method | Semantics |
|--------|-----------|
| `open(path, flags) -> Result<FileHandle, FsError>` | Create or open a file; return an opaque handle. |
| `close(handle) -> Result<(), FsError>` | Release driver-side resources for a handle. |
| `read(handle, offset, buf) -> Result<i64, FsError>` | Read up to `buf.len()` bytes at `offset`; return bytes read. |
| `write(handle, offset, buf) -> Result<i64, FsError>` | Write `buf` at `offset`; return bytes written. |
| `pread` / `pwrite` | Positional variants — do not advance an internal file position. |
| `fstat(handle) -> Result<FileStat, FsError>` | Metadata for an open handle. |
| `stat(path) -> Result<FileStat, FsError>` | Metadata by path (no open required). |
| `truncate(path, length)` / `ftruncate(handle, length)` | Resize a file exactly. |
| `fsync(handle)` / `fdatasync(handle)` | Flush to durable storage (data+metadata / data only). |

### Namespace group

| Method | Semantics |
|--------|-----------|
| `root() -> Result<Inode, FsError>` | Return the root-directory inode. |
| `readdir(handle: DirHandle) -> Result<[DirEntry], FsError>` | List directory entries. |
| `mkdir` / `rmdir` / `unlink` / `rename` | Standard namespace mutation. |
| `symlink(target, link)` / `readlink(path)` | Symbolic link creation/traversal. |
| `link(target, link)` | Hard link (requires `Capability.Hardlinks`). |

### Extension probe group

```
fn capabilities() -> CapabilitySet   # infallible, never blocks
fn probe(cap: Capability) -> Option<Extension>
```

`capabilities()` returns a bitmask of supported features. Always check `capabilities().has(cap)` before calling `probe(cap)`. `probe` may still return `None` even when the bitmask is set (e.g. a capability disabled at mount time).

---

## 2. Capability Declaration

`Capability` (defined in `capability.spl`) is a 22-variant enum. Each variant maps to a bit position in a `CapabilitySet` (u32 bitmask, 22 bits used).

### All 22 capabilities

| Variant | Bit | What it signals |
|---------|-----|-----------------|
| `COW` | 0 | Copy-on-write writes; no in-place overwrite |
| `Snapshot` | 1 | Point-in-time consistent snapshots |
| `Clone` | 2 | Writable COW clone of a volume |
| `Dedup` | 3 | Offline content-hash deduplication |
| `Checksum` | 4 | Per-block checksum verification |
| `SelfHeal` | 5 | Automatic repair via redundant copies |
| `SendReceive` | 6 | Incremental stream serialization |
| `Compress` | 7 | Transparent per-file compression |
| `Encrypt` | 8 | Transparent at-rest encryption |
| `Quota` | 9 | Per-volume space quota and reservation |
| `Reflink` | 10 | COW file-range clone (O(1) metadata op) |
| `Atime` | 11 | Full access-time tracking |
| `Xattr` | 12 | Extended attributes |
| `Acl` | 13 | POSIX ACLs |
| `CaseFold` | 14 | Case-insensitive filename matching |
| `Hardlinks` | 15 | Multiple directory entries → same inode |
| `SparseFiles` | 16 | Holes map to zero; no physical block allocated |
| `LargeFiles` | 17 | Files larger than 4 GiB |
| `UnicodeNames` | 18 | Full Unicode filename support (NFC) |
| `CaseSensitive` | 19 | Case-sensitive filename matching |
| `PosixCompat` | 20 | POSIX random-write/truncate emulation |
| `AsyncIo` | 21 | Async I/O submission path |

### Declaring capabilities in a driver

In your driver's `capabilities()` implementation, build the set from `CapabilitySet.empty()` using `.with(cap)`:

```
fn capabilities() -> CapabilitySet:
    CapabilitySet.empty()
        .with(Capability.CaseSensitive)
        .with(Capability.LargeFiles)
        .with(Capability.UnicodeNames)
```

Only advertise capabilities you actually implement. Advertising a capability but returning `None` from `probe` is allowed when the feature was disabled at mount time — but lying to `capabilities()` is not.

---

## 3. Extensions

`Extension` (defined in `extension.spl`) is a 10-variant enum. Each variant wraps a concrete handle struct with feature-specific state and methods.

| Extension variant | Handle struct | Purpose |
|-------------------|--------------|---------|
| `Snapshot(ext: SnapshotExt)` | `volume_name`, `snap_count` | Point-in-time snapshots |
| `Dedup(ext: DedupExt)` | `bytes_saved`, `scan_active` | Offline dedup |
| `Checksum(ext: ChecksumExt)` | `algo_tag`, `block_size` | Per-block integrity |
| `SendReceive(ext: SendRecvExt)` | `last_sent_gen`, `stream_format` | Incremental backup streams |
| `Scrub(ext: ScrubExt)` | `blocks_verified`, `errors_found` | Background integrity scrub |
| `Compress(ext: CompressExt)` | `default_algo`, `enabled` | Transparent compression |
| `Encrypt(ext: EncryptExt)` | `key_id`, `key_bits` | At-rest encryption |
| `Quota(ext: QuotaExt)` | `marker` (stub) | Volume quotas |
| `Reflink(ext: ReflinkExt)` | `shared_extents`, `cow_pending` | COW range clone |
| `PosixCompat(ext: PosixCompatExt)` | `flags`, `mode` | POSIX shim state |

### Using an extension from a caller

```
match driver.probe(Capability.Snapshot):
    case Some(Extension.Snapshot(ext)):
        # use ext.snap_count, call ext methods
    case _:
        return Err(FsError.Unsupported)
```

Always check `capabilities().has(Capability.Snapshot)` first to avoid the probe overhead on unsupported drivers.

### Implementing probe in a driver

Return `None` for any capability your driver does not support. For supported capabilities, construct and return the appropriate extension:

```
fn probe(cap: Capability) -> Option<Extension>:
    match cap:
        case PosixCompat:
            Some(Extension.PosixCompat(PosixCompatExt(flags: 0, mode: 0o644)))
        case _:
            None
```

---

## 4. Integration with MountTable

### How DriverInstance works

`DriverInstance` (defined in `instance.spl`) is an enum with one variant per concrete driver. VFS dispatch is an exhaustive match — no `dyn`, no vtable:

```
enum DriverInstance:
    Fat32(driver: Fat32Driver)
    Nvfs(driver: NvfsDriver)
    NvfsPosix(driver: NvfsPosixDriver)
    RamFs(driver: RamFsDriver)
```

Every `match &mount.driver` arm must cover all variants. Adding a new driver means adding a variant and the compiler flags every match site that needs updating.

### MountTable API

`MountTable` (defined in `mount_table.spl`) stores `MountEntry` records keyed by mount-point path. Lookup uses longest-prefix match.

```
# Mount a driver
val table_id = g_mount_table.mount(
    Path(raw: "/sqlite"),
    DriverInstance.Sqlite(my_driver),
    MountOptions.default()
)?

# Lookup: returns MountEntry? (nil if no mount covers the path)
val entry_opt = g_mount_table.lookup(Path(raw: "/sqlite/data.db"))

# Unmount
g_mount_table.unmount(Path(raw: "/sqlite"))?
```

Each `MountEntry` holds:
- `id: MountId` — opaque slot index, monotonically assigned
- `mount_point: Path` — absolute path this driver owns
- `driver: DriverInstance` — the concrete driver
- `opts: MountOptions` — options negotiated at mount
- `active_caps: u32` — `CapabilitySet.bits` after mount-time negotiation

---

## 5. Consumer API: g_vfs_* helpers

`src/os/services/vfs/vfs_init.spl` exposes public helpers that route callers through `g_mount_table`. Prefer these over raw driver calls in application code.

| Helper | What it does |
|--------|-------------|
| `g_vfs_read_file_text(name: text) -> text` | Read entire file as UTF-8 text. Returns `""` on error. |
| `g_vfs_write_file_text(name: text, content: text) -> bool` | Write entire file as UTF-8 text. Returns `false` on error. |
| `g_vfs_file_size(name: text) -> i64` | Return file size in bytes, or `-1` on error. |
| `g_vfs_file_exists(name: text) -> bool` | Return whether a file exists. |
| `g_vfs_select_file(name: text)` | Set a stateful file cursor for subsequent write. |
| `g_vfs_write_selected_file_text(content: text) -> bool` | Write to the previously selected file. |
| `g_vfs_clear_selected_file()` | Reset the file cursor. |

### Internal dispatch pattern

Each helper follows this three-step pattern:

1. Convert the name to an absolute `Path` via `g_vfs_abs_path` (prepends `/` if bare).
2. Call `g_mount_table.lookup(abs)` to get the `MountEntry`.
3. Pass `entry.driver` to a `g_vfs_dispatch_*` function that exhaustively matches on `DriverInstance` and calls the appropriate concrete driver.

When you add a new `DriverInstance` variant, **every `g_vfs_dispatch_*` function gains a new match arm**. The compiler enforces completeness — you cannot miss one.

### Boot initialization

`vfs_boot_init()` is the entry point that wires hardware to the mount table:

1. PCI manager discovers the NVMe device.
2. C NVMe adapter is initialized via syscall 86.
3. `Fat32Driver.new(...)` is constructed with the adapter as `BlockDevice`.
4. `fat32_drv.mount(opts)` is called on the driver.
5. `g_mount_table.mount(Path.root(), DriverInstance.Fat32(fat32_drv), opts)` registers it.

Follow this same sequence for any new driver mounted at boot.

---

## 6. Worked Example: Adding SqliteBackedDriver

This example shows the minimal steps to add a hypothetical driver that stores files as SQLite rows.

### Step 1: Define the driver struct

```
struct SqliteDriver:
    name:    text
    db_path: text
    mounted: bool
    # ... internal connection state ...
```

### Step 2: Implement FsDriver

At minimum, implement the full trait. Methods your storage model cannot support should return `Err(FsError.Unsupported)`.

```
impl FsDriver for SqliteDriver:

    me fn mount(opts: MountOptions) -> Result<(), FsError>:
        # open sqlite connection
        self.mounted = true
        Ok(())

    me fn unmount() -> Result<(), FsError>:
        # flush WAL, close connection
        self.mounted = false
        Ok(())

    me fn remount(opts: MountOptions) -> Result<(), FsError>:
        Ok(())   # or renegotiate read-only

    fn statfs() -> Result<FsStatfs, FsError>:
        # query PRAGMA page_count / page_size
        Ok(FsStatfs(...))

    fn root() -> Result<Inode, FsError>:
        Ok(Inode(id: 1))

    me fn open(path: Path, flags: OpenFlags) -> Result<FileHandle, FsError>:
        # INSERT OR IGNORE INTO files (path) VALUES (?1)
        # return allocated FileHandle
        pass_todo

    me fn close(handle: FileHandle) -> Result<(), FsError>:
        Ok(())

    me fn read(handle: FileHandle, offset: i64, buf: [u8]) -> Result<i64, FsError>:
        # SELECT SUBSTR(data, ?1+1, ?2) FROM files WHERE fd_id = ?3
        pass_todo

    me fn write(handle: FileHandle, offset: i64, buf: [u8]) -> Result<i64, FsError>:
        # UPDATE files SET data = ... WHERE fd_id = ?
        pass_todo

    me fn pread(handle: FileHandle, offset: i64, buf: [u8]) -> Result<i64, FsError>:
        self.read(handle, offset, buf)   # no cursor state needed

    me fn pwrite(handle: FileHandle, offset: i64, buf: [u8]) -> Result<i64, FsError>:
        self.write(handle, offset, buf)

    fn fstat(handle: FileHandle) -> Result<FileStat, FsError>:
        pass_todo

    fn stat(path: Path) -> Result<FileStat, FsError>:
        pass_todo

    me fn truncate(path: Path, length: i64) -> Result<(), FsError>:
        pass_todo

    me fn ftruncate(handle: FileHandle, length: i64) -> Result<(), FsError>:
        pass_todo

    fn fsync(handle: FileHandle) -> Result<(), FsError>:
        # PRAGMA wal_checkpoint(FULL)
        Ok(())

    fn fdatasync(handle: FileHandle) -> Result<(), FsError>:
        Ok(())

    fn readdir(handle: DirHandle) -> Result<[DirEntry], FsError>:
        pass_todo

    me fn mkdir(path: Path, mode: u32) -> Result<(), FsError>:
        pass_todo

    me fn rmdir(path: Path) -> Result<(), FsError>:
        pass_todo

    me fn unlink(path: Path) -> Result<(), FsError>:
        pass_todo

    me fn rename(old: Path, new: Path) -> Result<(), FsError>:
        pass_todo

    me fn symlink(target: Path, link: Path) -> Result<(), FsError>:
        Err(FsError.Unsupported)   # SQLite rows cannot be symlinks

    fn readlink(path: Path) -> Result<Path, FsError>:
        Err(FsError.Unsupported)

    me fn link(target: Path, link: Path) -> Result<(), FsError>:
        Err(FsError.Unsupported)

    fn capabilities() -> CapabilitySet:
        CapabilitySet.empty()
            .with(Capability.CaseSensitive)
            .with(Capability.LargeFiles)
            .with(Capability.UnicodeNames)
            # No Hardlinks, no Symlink, no COW

    fn probe(cap: Capability) -> Option<Extension>:
        None   # no extensions implemented yet
```

### Step 3: Add the DriverInstance variant

In `src/lib/nogc_sync_mut/fs_driver/instance.spl`:

```
use std.fs_driver.sqlite_driver.{SqliteDriver}

enum DriverInstance:
    Fat32(driver: Fat32Driver)
    Nvfs(driver: NvfsDriver)
    NvfsPosix(driver: NvfsPosixDriver)
    RamFs(driver: RamFsDriver)
    Sqlite(driver: SqliteDriver)       # <-- new
```

Also extend `driver_name()`:

```
case Sqlite(d): d.name
```

### Step 4: Extend every dispatch match

The compiler will flag every exhaustive match that is now incomplete. For each `g_vfs_dispatch_*` function in `vfs_init.spl`, add:

```
case Sqlite(d):
    # implement or return the appropriate default (e.g. "" or false or -1)
```

### Step 5: Mount the driver

At boot or on-demand:

```
var sqlite_drv = SqliteDriver.new("sqlite-data", "/data/sqlite.db")
sqlite_drv.mount(MountOptions.default())?
g_mount_table.mount(Path(raw: "/sqlite"), DriverInstance.Sqlite(sqlite_drv), MountOptions.default())?
```

### Step 6: Tests to write

Write tests in `test/` using SSpec. Cover:

1. **Lifecycle**: `mount` succeeds; double-`mount` returns an error or is idempotent; `unmount` with open handles returns `FsError.Busy`.
2. **Round-trip I/O**: `open` → `write` → `close` → `open` → `read` returns the same bytes.
3. **Namespace**: `mkdir` creates a directory visible in `readdir`; `unlink` removes it; `rename` moves atomically.
4. **Capabilities**: `capabilities().has(Capability.CaseSensitive)` returns `true`; `capabilities().has(Capability.COW)` returns `false`; `probe(Capability.COW)` returns `None`.
5. **Error paths**: `open` on missing path without `O_CREAT` returns `FsError.NotFound`; `unlink` on missing path returns `FsError.NotFound`.
6. **MountTable integration**: Mount `SqliteDriver` at `/sqlite`; call `g_vfs_read_file_text("/sqlite/test.txt")` and verify dispatch reaches the driver.

---

## 7. Decision Tree: What If My FS Needs Feature X?

```
Need feature X?
│
├─ Stateful cursor (track read position across calls)?
│   → Keep cursor state in the SERVICE layer (see g_vfs_selected_file pattern).
│     Do NOT add cursor state to DriverInstance or FsDriver.
│
├─ Optional capability (snapshots, encryption, compression, ...)?
│   ├─ Does an Extension variant already exist in extension.spl?
│   │   └─ Yes → advertise the Capability in capabilities(); return the
│   │            Extension handle from probe(); fill the handle struct.
│   └─ No  → file a feature request to add an Extension variant +
│            Capability enum value; do not invent a workaround.
│
├─ New required method that ALL drivers must implement?
│   → Add to the FsDriver trait in ops.spl.
│     All existing impls will fail to compile — update them before landing.
│
├─ Whole new driver (new storage backend)?
│   └─ Follow steps 1–6 in §6 above.
│      Add DriverInstance variant → compiler flags incomplete matches.
│
├─ POSIX semantics over an append-only backend (like NVFS)?
│   → Use the PosixCompat capability + NvfsPosixDriver pattern:
│     COW-copy-to-new-arena for pwrite, arena_seal for truncate,
│     deferred discard for unlink-while-open.
│     Do NOT bolt POSIX logic into the core NVFS driver.
│
├─ Async I/O path?
│   → Advertise Capability.AsyncIo.
│     Async scheduling lives outside FsDriver (in the service/actor layer).
│     FsDriver methods remain synchronous.
│
└─ Driver-specific config not covered by MountOptions?
    → Extend MountOptions fields (in types.spl) OR accept config in
      the driver's constructor. Never add driver-specific fields to
      MountEntry or DriverInstance.
```

---

## Reference: File Locations

| File | Purpose |
|------|---------|
| `src/lib/nogc_sync_mut/fs_driver/ops.spl` | `FsDriver` trait — all method signatures |
| `src/lib/nogc_sync_mut/fs_driver/instance.spl` | `DriverInstance` enum — add new variants here |
| `src/lib/nogc_sync_mut/fs_driver/capability.spl` | 22-variant `Capability` enum + `CapabilitySet` bitmask |
| `src/lib/nogc_sync_mut/fs_driver/extension.spl` | 10-variant `Extension` enum + handle structs |
| `src/lib/nogc_sync_mut/fs_driver/mount_table.spl` | `MountTable`, `MountEntry`, `MountId` |
| `src/lib/nogc_sync_mut/fs_driver/ramfs.spl` | `RamFsDriver` — complete reference implementation |
| `src/os/services/vfs/vfs_init.spl` | `g_vfs_*` consumer helpers + boot init |
| `doc/05_design/fs_driver_interface.md` | Design rationale (§2 trait, §3 dispatch, §4 extensions, §5 caps) |
