# SimpleOS Filesystem — Current State Research

> Status: research snapshot, 2026-04-18
> Scope: x86_64 target only unless noted. arm64/riscv64 lack FAT32 support.

---

## 1. Executive Summary

SimpleOS has **two parallel VFS systems** that coexist today:

| System | Trait | Error type | Dispatch | Status |
|--------|-------|-----------|---------|--------|
| **OLD** | `Filesystem` (vfs.spl) | `Result<_, text>` | vtable via trait object | Active in service layer |
| **NEW** | `FsDriver` (fs_driver/ops.spl) | `Result<_, FsError>` | exhaustive match on `DriverInstance` | Defined; not yet the execution path |

Beyond these two trait systems, a third path exists: **direct C-extern calls** (`rt_fat32_*`) that bypass both traits entirely. Entry-point files and the shell use this path today.

**FAT32 is present: YES.** Three real implementations plus one new-trait stub exist. The C runtime driver in `baremetal_stubs.c` is the only one reachable at boot.

---

## 2. Repository Layout — Filesystem-Relevant Files

```
src/
  lib/
    nogc_sync_mut/
      fs_driver/            ← NEW trait surface (Phase 9+)
        __init__.spl
        ops.spl             ← FsDriver trait (135 lines)
        types.spl           ← FileHandle, DirHandle, Inode, Path, etc.
        error.spl           ← FsError enum + errno_of()
        capability.spl      ← Capability enum (22 variants) + CapabilitySet
        extension.spl       ← Extension enum + *Ext handle structs
        instance.spl        ← DriverInstance enum (Fat32/Nvfs/NvfsPosix/RamFs)
        mount_table.spl     ← MountId, MountEntry, MountTable
        fat32_stub.spl      ← Fat32Driver stub (all ops → Err(Unsupported))
  os/
    services/
      vfs/
        vfs.spl             ← OLD: Filesystem trait + VfsManager (319 lines)
        vfs_init.spl        ← vfs_boot_init() chokepoint (290 lines)
      fat32/
        fat32.spl           ← Pure-Simple FAT32 over BlockDevice (1009 lines)
    kernel/
      fs/
        fat32.spl           ← Kernel BPB parser + FileHandle (317 lines)

examples/
  simple_os/
    arch/x86_64/
      fs_test_entry.spl     ← Direct rt_fat32_* calls (98 lines)
      boot_stage2_entry.spl ← vfs_boot_init() call site (43 lines)
      boot_stage3_entry.spl ← vfs_boot_init() + net (47 lines)
      shell_serial_entry.spl← Direct rt_fat32_* calls (60+ lines)
    boot/
      baremetal_stubs.c     ← C runtime, real FAT32 + NVMe (11968 lines)
  nvfs/
    src/
      driver/
        fs_driver_impl.spl  ← NvfsDriver implements FsDriver
      posix/
        fs_driver_impl.spl  ← NvfsPosixDriver implements FsDriver (Phase 9 B2)
        fd_table.spl        ← FdEntry + FdTable
        cow_engine.spl      ← CowShadow for rename/truncate semantics
```

---

## 3. FAT32 Implementations — Inventory

### 3.1 C Runtime Driver (`baremetal_stubs.c` §8b-fat32, line ~1609)

The only FAT32 implementation reachable at boot on real hardware. Lives entirely in C.

**Key data structure** (static, file-scope, line ~1811):
```c
static struct {
    uint32_t bytes_per_sector;
    uint32_t sectors_per_cluster;
    uint32_t reserved_sectors;
    uint32_t num_fats;
    uint32_t fat_size;
    uint32_t root_cluster;
    uint32_t data_start_sector;
    uint32_t total_clusters;
    bool     initialized;
} _fat32;
```

**C-level functions**:
```c
int fat32_find_file(const char *name, uint32_t *out_cluster, uint32_t *out_size);
int fat32_read_file(const char *name, uint8_t *buf, uint32_t max_size, uint32_t *bytes_read);
int fat32_write_file(const char *name, const uint8_t *buf, uint32_t size);
```

**RuntimeValue wrappers** (callable from Simple via extern):
- `rt_fat32_read_file_text(name: text) -> text`
- `rt_fat32_file_size(name: text) -> i64`
- `rt_fat32_file_exists(name: text) -> bool`
- `rt_fat32_write_file_text(name: text, content: text) -> bool`
- `rt_fat32_select_file(name: text) -> bool`
- `rt_fat32_write_selected_file_text(content: text) -> bool`

**Architecture**: x86_64-only. arm64/riscv64/arm32 `baremetal_stubs.c` files contain no FAT32 code.

**Mount**: NOT routed through `VfsManager`. The C driver maintains its own BPB state and is initialized implicitly when `vfs_boot_init()` calls NVMe init (syscall 86).

### 3.2 Pure-Simple FAT32 Service (`src/os/services/fat32/fat32.spl`, 1009 lines)

Implements the OLD `Filesystem` trait over a `BlockDevice` trait.

**`BlockDevice` trait** (line 76):
```
trait BlockDevice:
    fn read_sector(lba: u64, buffer: [u8]) -> Result<bool, text>
    fn write_sector(lba: u64, data: [u8]) -> Result<bool, text>
    fn sector_size() -> u32
```

Key structs: `Fat32Bpb`, `Fat32DirEntry`, `Fat32FileHandle`, `Fat32Volume`. Implements full directory traversal, cluster chain following, allocation table reads. This is the canonical Simple-language FAT32 implementation but it is **not wired** to any boot path.

### 3.3 Kernel BPB Parser (`src/os/kernel/fs/fat32.spl`, 317 lines)

Kernel-side read path. Defines `parse_bpb()`, `FileHandle`, `FileStat`, `Fat32Bpb`. Used by kernel-internal file reads only; does not expose the `Filesystem` or `FsDriver` trait.

### 3.4 New-Trait Stub (`src/lib/nogc_sync_mut/fs_driver/fat32_stub.spl`, 108 lines)

`Fat32Driver` struct with one field (`name: text`). Implements `FsDriver for Fat32Driver` where every operation returns `Err(FsError.Unsupported)` except `capabilities()` → `CapabilitySet.empty()` and `probe()` → `None`. This exists solely so `DriverInstance.Fat32(Fat32Driver)` resolves.

---

## 4. NVMe Block Layer

### 4.1 C Driver (`baremetal_stubs.c` §8b, line ~1000)

Functions: `_nvme_init_controller()`, `_nvme_read_sector_impl()`, `_nvme_write_sector_impl()`. Uses PCIe MMIO polling (no interrupts).

**Syscall bindings**:
| Syscall # | Purpose |
|-----------|---------|
| 84 | AllocDMA |
| 85 | NvmeReadSector |
| 86 | NvmeInit |
| 94 | NvmeWriteSector |

### 4.2 Simple Adapter (`src/os/services/vfs/vfs_init.spl`, lines 43–109)

`CNvmeBlockAdapter` class wraps syscall 85 (`NvmeReadSector`) as a `BlockDevice`. This bridges the C NVMe driver to the pure-Simple FAT32 service — but the bridge is never activated in the current boot path.

---

## 5. OLD VFS System (`src/os/services/vfs/vfs.spl`, 319 lines)

### 5.1 `Filesystem` Trait (line 18)
```
trait Filesystem:
    fn fs_name() -> text
    fn mount(source: text, options: text) -> Result<(), text>
    fn unmount() -> Result<(), text>
    fn open(path: text, flags: i32) -> Result<i32, text>
    fn read(fd: i32, buf: [u8], count: i64) -> Result<i64, text>
    fn write(fd: i32, buf: [u8], count: i64) -> Result<i64, text>
    fn close(fd: i32) -> Result<(), text>
    fn seek(fd: i32, offset: i64, whence: i32) -> Result<i64, text>
    fn stat(path: text) -> Result<FileStat, text>
    fn chmod(path: text, mode: u32) -> Result<(), text>
    fn mkdir(path: text, mode: u32) -> Result<(), text>
    fn rmdir(path: text) -> Result<(), text>
    fn readdir(path: text) -> Result<[DirEntry], text>
    fn unlink(path: text) -> Result<(), text>
    fn rename(old: text, new: text) -> Result<(), text>
    fn symlink(target: text, link: text) -> Result<(), text>
```

### 5.2 `VfsManager` Class
- Holds `[MountEntry]` (mount point → `Filesystem` trait object)
- `resolve_mount(path)`: longest-prefix scan
- Delegates all FS ops through `Filesystem` trait
- Convenience methods: `read_text(path)`, `write_text(path, content)`

### 5.3 Gap: VfsManager Is Never Loaded with a Driver

`vfs_boot_init()` calls NVMe init (syscall 86), marks `g_vfs_initialized = true`, and returns. It does **not** call `g_vfs.mount(...)` with a `Fat32Volume`. The `VfsManager` instance (`g_vfs`) holds an empty mount table at runtime.

---

## 6. NEW FsDriver System (`src/lib/nogc_sync_mut/fs_driver/`)

### 6.1 `FsDriver` Trait (`ops.spl`, 135 lines)
Full POSIX-like surface: mount/unmount/remount/statfs/root/open/close/read/write/ pread/pwrite/fstat/stat/truncate/ftruncate/fsync/fdatasync/readdir/mkdir/rmdir/ unlink/rename/symlink/readlink/link/capabilities/probe. Returns `Result<_, FsError>`.

### 6.2 `DriverInstance` Enum (`instance.spl`, line 28)
```
enum DriverInstance:
    Fat32(driver: Fat32Driver)        ← stub
    Nvfs(driver: NvfsDriver)          ← real (examples/nvfs/src/driver/)
    NvfsPosix(driver: NvfsPosixDriver)← real (examples/nvfs/src/posix/, Phase 9 B2)
    RamFs(driver: RamFsStub)          ← stub
```

### 6.3 `MountTable` (`mount_table.spl`, 131 lines)
`MountId`, `MountEntry`, `MountTable.mount()`, `MountTable.unmount()`, `MountTable.lookup(id)`, `MountTable.resolve(path)`. This is the NEW replacement for `VfsManager`'s mount list.

### 6.4 Capability System (`capability.spl`)
22 `Capability` variants; `CapabilitySet` bitmask. Drivers declare capabilities; callers can probe for optional extensions via `probe(cap) -> Option<Extension>`.

### 6.5 `NvfsPosixDriver` (`examples/nvfs/src/posix/fs_driver_impl.spl`)
Implements `FsDriver` over NVFS arenas with POSIX semantics (random write, truncate, rename visibility). Uses `CowShadow` (`cow_engine.spl`) and `FdTable` (`fd_table.spl`). Phase 9 B2 — complete.

---

## 7. FS Call-Site Inventory

All sites where filesystem operations are invoked, with file, line range, and the call form used.

| # | File | Line(s) | Function | Call form | Path |
|---|------|---------|----------|-----------|------|
| 1 | `examples/simple_os/arch/x86_64/fs_test_entry.spl` | 1–98 | `fs_test_entry()` | `extern rt_fat32_read_file_text`, `rt_fat32_file_size`, `rt_fat32_file_exists` | Direct C-extern |
| 2 | `examples/simple_os/arch/x86_64/fs_test_entry.spl` | ~30 | `fs_test_entry()` | `vfs_boot_init()` | Startup hook |
| 3 | `examples/simple_os/arch/x86_64/shell_serial_entry.spl` | ~40–60 | shell loop | `rt_fat32_read_file_text`, `rt_fat32_file_size` | Direct C-extern |
| 4 | `examples/simple_os/arch/x86_64/shell_serial_entry.spl` | ~10 | init | `vfs_boot_init()` | Startup hook |
| 5 | `examples/simple_os/arch/x86_64/boot_stage2_entry.spl` | 1–43 | `boot_stage2()` | `vfs_boot_init()`, `vfs_is_ready()` | Startup hook |
| 6 | `examples/simple_os/arch/x86_64/boot_stage3_entry.spl` | 1–47 | `boot_stage3()` | `vfs_boot_init()`, `net_boot_init()`, `vfs_is_ready()` | Startup hook |
| 7 | `src/os/services/vfs/vfs_init.spl` | 43–109 | `CNvmeBlockAdapter` | syscall 85 (`NvmeReadSector`) | Syscall |
| 8 | `src/os/services/vfs/vfs_init.spl` | ~200–260 | `vfs_boot_init()` | syscall 86 (`NvmeInit`) | Syscall |
| 9 | `src/os/services/fat32/fat32.spl` | 1–1009 | `Fat32Volume.*` | `BlockDevice.read_sector`, `write_sector` | OLD trait |
| 10 | `src/os/services/vfs/vfs.spl` | 1–319 | `VfsManager.*` | `Filesystem` trait methods | OLD trait vtable |

**Total unique call-site files: 6** (fs_test_entry, shell_serial_entry, boot_stage2, boot_stage3, vfs_init, vfs — plus fat32.spl as internal impl). **Direct C-extern call sites: 2 files** (fs_test_entry, shell_serial_entry).

---

## 8. Module Globals and Init Sequence

From `src/os/services/vfs/vfs_init.spl`:

```
# Module globals
var g_vfs: VfsManager        # OLD VfsManager instance — mount table empty at runtime
var g_nvme: NvmeDriver       # Wraps syscall 86
var g_c_adapter: CNvmeBlockAdapter  # Wraps syscall 85 as BlockDevice
var g_vfs_initialized: bool  # Set true after NVMe init; does NOT mean FS is mounted
```

**`vfs_boot_init()` current sequence**:
1. PCI bus scan (`pcimgr_init()`)
2. NVMe controller init via syscall 86
3. `g_vfs_initialized = true`
4. Return `true`

**Missing steps** (gaps):
- Never constructs `Fat32Volume(g_c_adapter)`
- Never calls `g_vfs.mount("/", fat32_volume)`
- Entry-point files work around this by calling `rt_fat32_*` C externs directly

---

## 9. Architectural Findings

### Finding 1: Three-Path Fragmentation
Three distinct FS execution paths exist simultaneously:
- **Path A**: Direct C externs (`rt_fat32_*`) — used by entry points
- **Path B**: OLD `Filesystem` trait via `VfsManager` — defined but never populated
- **Path C**: NEW `FsDriver` trait via `DriverInstance`/`MountTable` — defined but not connected to hardware

### Finding 2: VfsManager Is a Dead Code Path
`g_vfs` (the `VfsManager` instance) is allocated but never has a driver mounted into it. Any code that calls `g_vfs.open(...)` would get a "no mount found" error. This path is structurally intact but operationally empty.

### Finding 3: NEW Trait is Fully Defined but Not Yet the Execution Path
`FsDriver`, `DriverInstance`, and `MountTable` are complete and correct. `NvfsDriver` and `NvfsPosixDriver` are real implementations. Only `Fat32Driver` (the new-trait stub) and `RamFsStub` are unimplemented. The NEW system is "ready to receive traffic" but nothing routes to it yet.

### Finding 4: FAT32 Has No Pure-Simple Boot Path
The pure-Simple FAT32 (`fat32.spl`) is never instantiated at boot. The kernel BPB parser (`src/os/kernel/fs/fat32.spl`) is separate and kernel-internal. The C driver is the only one actually reading FAT32 sectors at runtime.

### Finding 5: x86_64-Only FAT32
arm64/riscv64/arm32 `baremetal_stubs.c` files contain no FAT32 code. The entire FAT32 stack (including the C driver) is x86_64-specific.

---

## 10. Key Struct and Type Definitions

### OLD system types (in `vfs.spl`)
- `FileStat`: size, mode, is_dir, modified_time
- `DirEntry`: name, is_dir, size
- `MountEntry`: mount_point (text), fs (Filesystem trait)

### NEW system types (in `fs_driver/types.spl`)
- `Inode`: u64 inode number
- `FileHandle`: opaque handle
- `DirHandle`: opaque handle
- `Path`: text wrapper
- `OpenFlags`: bitmask u32
- `MountOptions`: source text + options text
- `FsStatfs`: block size, total/free/available blocks, inode counts
- `FileStat`: full POSIX stat (size, mode, uid, gid, atime/mtime/ctime, inode, nlink)
- `DirEntry`: name, inode, type

---

## 11. Test Coverage

| File | What it tests | Path exercised |
|------|---------------|----------------|
| `examples/simple_os/arch/x86_64/fs_test_entry.spl` | read/size/exists on hello.txt, numbers.txt, hello.spl | Direct C-extern |
| `examples/nvfs/test/unit/posix_shim_test.spl` | NvfsPosixDriver open/read/write/stat/rename/unlink | NEW FsDriver trait |

No test exercises `VfsManager` with a real driver mounted. No test exercises `Fat32Driver` (new-trait stub) — it is entirely unsupported.

---

## 12. Summary Table

| Item | Value |
|------|-------|
| FAT32 present | **YES** — 3 real impls + 1 new-trait stub |
| FAT32 boot path | C runtime only (`baremetal_stubs.c`) |
| FAT32 x86_64-only | YES |
| VfsManager populated at boot | **NO** |
| MountTable (new) connected to hardware | **NO** |
| NvfsDriver real | YES (examples/nvfs/src/driver/) |
| NvfsPosixDriver real | YES (examples/nvfs/src/posix/, Phase 9 B2) |
| Direct C-extern call sites | 2 files (fs_test_entry.spl, shell_serial_entry.spl) |
| Total FS call-site files | 6 |
| Recommended M1 starting file | `src/os/services/vfs/vfs_init.spl` |
