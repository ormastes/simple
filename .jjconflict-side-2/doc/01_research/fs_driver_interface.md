# FS Driver Interface Research

**Status:** Research only — no implementation.
**Date:** 2026-04-17
**Author:** Research pass (retried from stalled Opus agent)

---

## Table of Contents

1. [Prior-Art Survey](#1-prior-art-survey)
2. [Capability-Probe Patterns](#2-capability-probe-patterns)
3. [Simple-Language Design Space (No dyn)](#3-simple-language-design-space-no-dyn)
4. [Current SimpleOS FAT32 Inventory](#4-current-simpleos-fat32-inventory)
5. [Proposed NVFS Extension Interfaces](#5-proposed-nvfs-extension-interfaces)
   - [5a. POSIX-over-NVFS Wrapper](#5a-posix-over-nvfs-wrapper)
6. [Driver Lifecycle](#6-driver-lifecycle)
7. [Concurrency](#7-concurrency)
8. [Error Model](#8-error-model)
9. [Migration Path](#9-migration-path)
10. [Capability Catalogue](#10-capability-catalogue)
11. [Primary Sources](#11-primary-sources)

---

## 1. Prior-Art Survey

### 1.1 Linux VFS

**Source:** `Documentation/filesystems/vfs.rst` (kernel.org), `include/linux/fs.h`

Linux VFS is the canonical reference for a layered filesystem abstraction. It defines five primary operation tables, each a C struct of function pointers. A NULL slot means "unsupported" — callers check for NULL before dispatching. This is the sentinel-value idiom.

**`super_operations`** (per-mounted filesystem)
- `alloc_inode` / `destroy_inode` / `dirty_inode` / `write_inode` / `evict_inode`
- `sync_fs(sb, wait)` — flush to persistent storage
- `statfs(dentry, kstatfs)` — space accounting
- `remount_fs(sb, flags, data)` — live remount
- `show_options(seq, dentry)` — `/proc/mounts` rendering
- Extension capability is exposed via `s_flags` bitmask (e.g., `SB_RDONLY`, `SB_NOATIME`, `SB_MANDLOCK`) and filesystem-specific `s_fs_info` opaque pointer.

**`inode_operations`**
- `lookup`, `create`, `link`, `unlink`, `symlink`, `mkdir`, `rmdir`, `rename`
- `setattr` / `getattr` — permission and metadata ops
- `listxattr` / `getxattr` / `setxattr` / `removexattr` — extended attributes
- `fiemap` — extent map query (sparse files, dedup hints)
- NULL pointers for unsupported ops; callers do: `if (inode->i_op->fiemap) inode->i_op->fiemap(...)`.

**`file_operations`**
- `read` / `write` / `read_iter` / `write_iter` (vectored)
- `mmap` — page-fault integration
- `fallocate(file, mode, offset, len)` — pre-allocation + punch-hole (`FALLOC_FL_PUNCH_HOLE`)
- `ioctl` / `unlocked_ioctl` — fs-specific commands (used by btrfs for snapshot ioctl, ZFS for `ZFS_IOC_*`)
- `clone_file_range` / `copy_file_range` — reflink and server-side copy
- `seek` with `SEEK_DATA` / `SEEK_HOLE` — sparse file navigation

**`dentry_operations`**
- `d_revalidate` — NFS-style staleness check
- `d_hash` / `d_compare` — case-folding and encoding (critical for FAT32 short names, case-insensitive HFS+)
- `d_delete` — reference-count callback

**`address_space_operations`** (page cache)
- `readpage` / `readpages` / `writepage` / `writepages`
- `set_page_dirty` / `releasepage` / `invalidatepage`
- `direct_IO` — bypass page cache

**Key Linux observation:** NULL op = unsupported is O(1) and requires no allocations, but provides no structured reason for unsupported-ness. Callers learn "not present" but not "wrong flags" vs "unimplemented."

### 1.2 FreeBSD VFS / vnodeops

**Source:** FreeBSD Handbook Chapter on VFS (`sys/kern/vfs_lookup.c`, `sys/sys/vnode.h`, FreeBSD Architecture Handbook §5)

FreeBSD VFS uses two parallel tables:

**`vfsops`** (per filesystem type, registered with `VFS_SET`)
- `vfs_mount` / `vfs_unmount` / `vfs_root` / `vfs_statfs`
- `vfs_sync` / `vfs_vget` / `vfs_fhtovp` — file handle to vnode (NFS export)
- `vfs_quotactl` — quota management hook
- Registered via `VFS_SET(ufs_vfsops, ufs, 0)` macro; NULL slots = unimplemented.

**`vnode_ops` / `vnodeops`** (per-vnode, allocated per operation using `vop_*` generated functions)
- `VOP_LOOKUP` / `VOP_CREATE` / `VOP_REMOVE` / `VOP_RENAME`
- `VOP_READ` / `VOP_WRITE` / `VOP_MMAP` / `VOP_FSYNC`
- `VOP_GETATTR` / `VOP_SETATTR` / `VOP_ACCESS`
- `VOP_IOCTL` — extension escape hatch (same pattern as Linux)
- `VOP_ADVLOCK` — advisory locking
- `vop_bypass` — if a specific op is NULL, FreeBSD falls through to the bypass handler rather than panicking; this is cleaner than Linux's NULL-check-at-call-site.

**FreeBSD stacking model:** Stackable filesystems (nullfs, unionfs) intercept specific vnodeops and delegate the rest via `vop_bypass`. This is the inspiration for Option G's central dispatch table.

### 1.3 illumos VFS (Solaris lineage)

**Source:** illumos `usr/src/uts/common/sys/vfs.h`, `vnode.h`, `man 9F vn_alloc`

illumos uses `vfs_ops_t` (mounted instance) and `vnodeops_t` (per-vnode):

**`vfs_ops_t`**
- `vfs_mount` / `vfs_unmount` / `vfs_root` / `vfs_statvfs`
- `vfs_sync` / `vfs_vget` / `vfs_mountroot` / `vfs_freevfs`
- `vfs_vnstate` — vnode state transitions (VNTRANSIT, etc.)

**`vnodeops_t`**
- Mirrors FreeBSD/Linux: lookup, create, remove, read, write, ioctl, mmap, etc.
- Notable addition: `vop_space(vp, cmd, bfp, flag, off, cr, ct)` — space management (equiv. to fallocate)
- `vop_reqzcopy` / `vop_realvp` — zero-copy and vnode aliasing for loopback filesystems

illumos introduces **`VFS_FEATURE_*`** bitmasks on the `vfs_t` struct:
- `VFSFT_XVATTR` — extended attribute support
- `VFSFT_CASEINSENSITIVE` / `VFSFT_NOCASESENSITIVE`
- `VFSFT_DIRENTFLAGS` — directory entry flags
- `VFSFT_ACLONCREATE` — ACL at creation time
- Check: `vfs_has_feature(vfsp, VFSFT_XVATTR)` — returns bool. This is the bitmap capability probe pattern.

### 1.4 Windows IFS (Installable File System)

**Source:** Windows Driver Kit, `ntifs.h` (IFS Kit), `FsRtl*` documentation

Windows IFS uses a fundamentally different model: I/O Request Packets (IRPs) dispatched through a Major Function table in the `DRIVER_OBJECT`. The driver registers handlers for IRP major codes (`IRP_MJ_CREATE`, `IRP_MJ_READ`, `IRP_MJ_WRITE`, `IRP_MJ_QUERY_INFORMATION`, `IRP_MJ_DIRECTORY_CONTROL`, `IRP_MJ_FILE_SYSTEM_CONTROL`, etc.).

**FastI/O table** (`FAST_IO_DISPATCH`): optional shortcut table that bypasses IRP allocation for common cache-manager paths. Each slot returns a BOOLEAN indicating whether the fast path was taken. If FALSE, the I/O manager falls back to the IRP path. This is the dual-dispatch pattern (fast path + slow path).

**FSCTL capability bits:** Extended filesystem capabilities are queried via `FSCTL_QUERY_*` control codes:
- `FSCTL_GET_COMPRESSION` / `FSCTL_SET_COMPRESSION`
- `FSCTL_QUERY_ALLOCATED_RANGES` — sparse file extents
- `FSCTL_GET_REPARSE_POINT` — symlink / volume mount point
- `FSCTL_SET_SPARSE`
- `FSCTL_DUPLICATE_EXTENTS_TO_FILE` — Windows reflink (Server 2016+, REFS)
- Advertisement: filesystems set capability bits in `FILE_FS_ATTRIBUTE_INFORMATION.FileSystemAttributes` (`FILE_SUPPORTS_SPARSE_FILES`, `FILE_SUPPORTS_HARD_LINKS`, `FILE_SUPPORTS_ENCRYPTION`, `FILE_SUPPORTS_REPARSE_POINTS`, etc.)

The FSCTL/capability-bits pattern is analogous to FUSE `conn_info->capable`. Both are bitmap enumerations probed before use.

### 1.5 macOS VFS (XNU)

**Source:** XNU `bsd/sys/mount.h`, `bsd/sys/vnode.h`, `bsd/vfs/vfs_support.h`, Apple's "Kernel Programming Guide" §File Systems

macOS VFS uses `vfsops` (mounted instance) and `vnodeops` (per-vnode) similarly to FreeBSD, but wraps them in:

**`vfs_fsentry`** — registration record passed to `vfs_fsadd()`:
- `vfe_fsops` — pointer to `struct vfsops`
- `vfe_vfsops_vfsflags` — `VFS_TBLTHREADSAFE`, `VFS_TBLFSNODELOCK`, `VFS_TBLNOTYPENUM`, `VFS_TBLLOCALVOL`, `VFS_TBL64BITREADY`, `VFS_TBLNATIVEXATTR`, `VFS_TBLDIRLINKS`, `VFS_TBLUNMOUNT_PREFLIGHT`
- `vfe_vnops` — array of `{vnop_desc *, implementation_fn}` pairs

**`vnop_desc`** — descriptor struct for each vnode operation:
- `vdesc_offset` — slot offset in the ops table
- `vdesc_name` — string name (for debugging)
- `vdesc_flags` — `VDESC_NO_OFFSET` if not applicable
- `vdesc_vop_*_offsets` — descriptor of which args are vnodes (for GC/locking)

The `vnop_desc` system allows the kernel to iterate all registered operations generically, which is useful for filesystem stacking (Ultrix-style). It is analogous to a vtable with runtime-inspectable metadata. Incompatible with Simple's no-dyn rule as stated (requires `void *` function pointer arrays), but the `vnop_desc` idea of attaching a capability descriptor alongside the operation is instructive.

**Capability advertisement:** `vfs_isrdonly`, `vfs_issynchronous`, `vfs_isnoexec`, `vfs_islocal` predicate functions, plus `MATTR_*` attributes queried via `vfs_getattr`.

### 1.6 Haiku `fs_vnode_ops`

**Source:** Haiku OS `headers/private/kernel/fs_interface.h`

Haiku uses a two-level interface: `fs_volume_ops` (per-volume) and `fs_vnode_ops` (per-vnode). Both are plain C structs of function pointers. NULL = unsupported.

**`fs_volume_ops`** highlights:
- `mount` / `unmount` / `read_fs_info` / `write_fs_info`
- `sync`
- `get_vnode`

**`fs_vnode_ops`** highlights:
- Standard: `lookup`, `read_stat`, `write_stat`, `create`, `remove`, `rename`
- `io(void *cookie, io_request *request)` — async I/O via io_request objects (kernel-level)
- `create_special_node` — devices, FIFOs
- `get_file_map` — extent query (for DMA, similar to `fiemap`)

Haiku's `io_request` dispatch is notable: all I/O goes through a single `io` function pointer rather than separate `read`/`write`. This simplifies stacking. Analogous to Option G's central table approach.

### 1.7 FUSE

**Source:** `fuse_lowlevel.h`, `fuse.h` (libfuse 3.x), `linux/fuse.h` in-kernel protocol

FUSE exposes a large flat struct `fuse_operations` with ~40 function pointers (high-level API) or `fuse_lowlevel_ops` (~30 slots) for the low-level inode API.

**Capability flags — `fuse_conn_info`:**
- `capable` — kernel-advertised capabilities (bitmask)
- `want` — filesystem's requested subset (bitmask)
- Bits: `FUSE_CAP_ASYNC_READ`, `FUSE_CAP_POSIX_LOCKS`, `FUSE_CAP_FILE_OPS`, `FUSE_CAP_ATOMIC_O_TRUNC`, `FUSE_CAP_EXPORT_SUPPORT`, `FUSE_CAP_DONT_MASK`, `FUSE_CAP_SPLICE_WRITE`, `FUSE_CAP_SPLICE_MOVE`, `FUSE_CAP_SPLICE_READ`, `FUSE_CAP_FLOCK_LOCKS`, `FUSE_CAP_IOCTL_DIR`, `FUSE_CAP_AUTO_INVAL_DATA`, `FUSE_CAP_READDIRPLUS`, `FUSE_CAP_READDIRPLUS_AUTO`, `FUSE_CAP_ASYNC_DIO`, `FUSE_CAP_WRITEBACK_CACHE`, `FUSE_CAP_NO_OPEN_SUPPORT`, `FUSE_CAP_PARALLEL_DIROPS`, `FUSE_CAP_POSIX_ACL`, `FUSE_CAP_HANDLE_KILLPRIV`, `FUSE_CAP_CACHE_SYMLINKS`
- Negotiated in `init` callback: filesystem calls `fuse_session_capabilities()`, sets `conn->want`, kernel applies the intersection.

FUSE's `capable` / `want` negotiation is the most explicit capability-probe pattern in surveyed systems. It is a mutual advertisement model: kernel offers, driver accepts subset. This is more structured than a NULL-check but requires both sides to understand the same flag dictionary.

### 1.8 Plan 9 / 9P

**Source:** `intro(5)` and `stat(5)` in Plan 9 manual; the 9P wire protocol specification

9P is a network protocol, not a driver interface. Clients and servers exchange typed messages (`Tversion`, `Tattach`, `Twalk`, `Topen`, `Tread`, `Twrite`, `Tclunk`, `Tremove`, `Tstat`, `Twstat`). The filesystem is stateless per message. No capability negotiation protocol exists; version string (`9P2000`, `9P2000.L`) is negotiated in `Tversion`/`Rversion`.

9P's design is elegant but purpose-built for distributed name-service. Its per-message round-trip model, lack of paging/address-space integration, and absence of hard links or extended attributes make it unsuitable as a local kernel VFS interface. Cited for completeness; not recommended as a model.

---

## 2. Capability-Probe Patterns

This section inventories capability-probe patterns from the surveyed systems, noting compatibility with Simple's constraint of no `dyn` / no trait-object runtime polymorphism.

### 2.1 Bitmap Flags

**Examples:**
- Linux `super_block.s_flags` (e.g., `SB_RDONLY`, `SB_NOSUID`, `SB_NOATIME`)
- Linux `s_iflags` (internal: `SB_I_CGROUPWB`, `SB_I_NODEV`, etc.)
- illumos `VFS_FEATURE_*` (`vfs_has_feature(vfsp, feature)`)
- FUSE `fuse_conn_info.capable` / `.want`
- Windows `FILE_FS_ATTRIBUTE_INFORMATION.FileSystemAttributes`
- ZFS `zfs_prop_t` per-property bitmasks (`ZFS_PROP_CHECKSUM`, `ZFS_PROP_COMPRESSION`, etc.)

**Pattern:** Integer or enum bitmask stored in a per-mount or per-session struct. Caller tests: `flags & CAP_X != 0`. O(1), no allocation. Works with any type system.

**Simple compatibility:** Fully compatible. An `i64` or a set-of-enum bitfield works fine. Recommended for advertisement of static capabilities that are fixed at mount time.

### 2.2 NULL Function Pointer (Sentinel)

**Examples:**
- Linux VFS: `if (inode->i_op->fiemap != NULL) ...`
- FreeBSD `vop_bypass` fallback
- Haiku `fs_vnode_ops`: NULL slot = not supported

**Pattern:** Table of optional function pointers; NULL means absent.

**Simple compatibility:** Simple does not have function pointers in the C sense. Trait methods are always present (no partial trait impls). The closest analog is returning `Err(FsError::Unsupported)` from a trait method — which is Option D'. Sentinel-null is not directly expressible.

### 2.3 COM QueryInterface / Type-Erasure Downcasting

**Examples:**
- Windows IFS filter drivers call `QueryInterface` on filter context
- macOS `vnode_t` has `VNOP_*` dispatch that falls back to `vfs_context`

**Pattern:** Call a standard method with an interface ID; returns a typed pointer or NULL.

**Simple compatibility:** Requires `dyn` or `Any::downcast`. **Incompatible with Simple's no-dyn rule.** Do not use.

### 2.4 Capability-Probe Method (Object Returns Typed Extension)

**Pattern:** The driver exposes a `probe(cap: Capability) -> Option<SomeType>` method. The returned type can carry behavior.

**Simple compatibility:** Compatible if `SomeType` is a concrete struct or enum. Incompatible if `SomeType` is `dyn Trait` or `Box<dyn Trait>`. This is the basis for Option E'.

### 2.5 Generic Monomorphization

**Pattern:** VFS layer is generic over `F: FsDriver`. All extension ops are bound via `where F: SnapshotDriver`. Lack of capability = compile error, not runtime probe.

**Simple compatibility:** Compatible with Simple generics (`<>`). Limitation: heterogeneous mount table requires additional indirection (see §3 analysis of Option F).

### 2.6 Enum-Tagged Union (Discriminated Union)

**Pattern:** The extension probe returns an enum variant carrying a concrete extension struct. Callers `match` on the variant.

**Simple compatibility:** Fully compatible. Simple supports enums with associated data. This is the basis for Option E'.

---

## 3. Simple-Language Design Space (No dyn)

### 3.1 Constraints Recap

Simple has:
- Traits and `impl` blocks: a type can implement a trait, and generic bounds work.
- Enums with associated data: `enum Foo { Bar(BarStruct), Baz(BazStruct) }`.
- `match` on enums.
- Generics with `<>` syntax.
- No `dyn Trait` / no trait objects at runtime.
- No `Box<dyn Trait>`, no `&dyn Trait`, no `Any::downcast`.
- `nogc_sync_mut` runtime: no GC, no async (the sync trait surface lives here).

This rules out:
- Linux-style null function pointer tables (no raw fn ptrs in Simple).
- COM QueryInterface returning `dyn`.
- Any heterogeneous container of trait objects.

### 3.2 Option D' — VFS-Style Single Trait, Unsupported Returns Err

**Design:** One `FsDriver` trait. Every optional operation is present but returns `Err(FsError::Unsupported)` if not implemented. Callers inspect the error variant.

```
# Sketch — no implementation, research only
trait FsDriver:
    fn read(handle: FileHandle, offset: i64, buf: [u8]) -> Result<i64, FsError>
    fn write(handle: FileHandle, offset: i64, buf: [u8]) -> Result<i64, FsError>
    fn snapshot(vol: VolumeId, name: Str) -> Result<SnapshotHandle, FsError>
    fn clone_range(src: FileHandle, src_off: i64, dst: FileHandle, dst_off: i64, len: i64) -> Result<(), FsError>
    # ... all ops, optional ones default to Err(FsError::Unsupported)
```

**Default impl for optional ops:**
```
fn snapshot(vol: VolumeId, name: Str) -> Result<SnapshotHandle, FsError>:
    return Err(FsError::Unsupported)
```

**Caller pattern:**
```
match driver.snapshot(vol, "snap1"):
    Ok(handle) => ...
    Err(FsError::Unsupported) => # not a snapshot-capable FS
    Err(e) => # real error
```

**Pros:**
- Simplest possible design. One trait, no extension machinery.
- No pre-check required; the operation attempt IS the probe.
- Compatible with a single-driver mount table of any `impl FsDriver` type... except that without `dyn`, the mount table must be homogeneous or generic-monomorphized (see §3.5).

**Cons:**
- Callers cannot statically verify that a capability is present before attempting it. A compiler-enforced guarantee requires Option F.
- A trait with 40+ methods, many defaulting to `Err(Unsupported)`, becomes a maintenance burden. Implementors must be careful not to miss overrides.
- Cannot compose extensions: FAT32's `FsDriver` impl and NVFS's `FsDriver` impl are different concrete types; they cannot be stored in the same heterogeneous collection without additional indirection.
- "Attempt and check error" pattern means caller overhead for optional ops that are common (e.g., checksum verification on every read in a checksum-capable FS).

**Assessment:** Viable for simple single-driver kernels. Insufficient for SimpleOS once FAT32 and NVFS coexist in the same VFS mount table.

### 3.3 Option E' — Enum-Wrapped Extension Handle

**Design:** `FsDriver` trait has a small required surface (open, close, read, write, stat, readdir). Extension capabilities are probed via a `probe` method that returns an enum-wrapped concrete extension handle.

```
# Sketch — research only
enum Extension:
    Snapshot(SnapshotExt)
    Dedup(DedupExt)
    Compress(CompressExt)
    Checksum(ChecksumExt)
    SendReceive(SendReceiveExt)
    Scrub(ScrubExt)
    Quota(QuotaExt)
    Reflink(ReflinkExt)
    PosixCompat(PosixCompatExt)

trait FsDriver:
    fn open(path: Path, flags: OpenFlags) -> Result<FileHandle, FsError>
    fn close(handle: FileHandle) -> Result<(), FsError>
    fn read(handle: FileHandle, offset: i64, buf: [u8]) -> Result<i64, FsError>
    fn write(handle: FileHandle, offset: i64, buf: [u8]) -> Result<i64, FsError>
    fn stat(handle: FileHandle) -> Result<FileStat, FsError>
    fn readdir(handle: DirHandle) -> Result<List<DirEntry>, FsError>
    fn probe(cap: Capability) -> Option<Extension>
    fn capabilities() -> CapabilitySet  # bitmask for cheap pre-checks
```

**Extension structs carry concrete methods (no dyn):**
```
struct SnapshotExt:
    driver_ref: *FatDriver  # or *NvfsDriver — concrete, not dyn
    fn create(vol: VolumeId, name: Str) -> Result<SnapshotId, FsError>
    fn delete(id: SnapshotId) -> Result<(), FsError>
    fn list(vol: VolumeId) -> Result<List<SnapshotId>, FsError>
```

**Caller pattern:**
```
val cap = driver.capabilities()
if cap.has(Capability::Snapshot):
    match driver.probe(Capability::Snapshot):
        Some(Extension::Snapshot(ext)) =>
            val snap = ext.create(vol, "backup-2026-04-17")?
        None => pass_dn  # driver lied? FsError::Unsupported from probe
```

**Pros:**
- Extension handles are concrete structs, not trait objects. No `dyn`.
- The `Extension` enum is closed (VFS layer owns the variant list). Adding a new capability adds a new variant — controlled evolution.
- `capabilities()` bitmask allows O(1) pre-check without attempting the op.
- Caller `match` on `Extension` is exhaustive (compiler verifies all variants are handled or `_` wildcard is explicit).
- Compatible with a VFS layer that holds drivers as generic type parameters or as a per-mount opaque (see §3.5 on heterogeneous mount table).

**Cons:**
- Extension enum variants are centralized in the VFS layer. Third-party (out-of-tree) filesystems cannot add new variants without modifying the enum. This is acceptable for SimpleOS (closed-world compiler) but would be limiting for a general-purpose OS with loadable modules.
- Each new extension type adds a variant to the `Extension` enum and a new concrete struct — moderate boilerplate, manageable with a code pattern.
- The `probe` call itself allocates an `Option<Extension>` — acceptable in `nogc_sync_mut` if the Extension structs are small (pointer-sized driver ref + no heap alloc).

**Assessment:** Best fit for SimpleOS given the constraints. Closed-world driver set, concrete structs, no `dyn`, exhaustive `match`. Recommended as the primary option.

### 3.4 Option F — Generic Specialization

**Design:** The VFS layer is generic over the driver type: `VfsMount<F: FsDriver>`. Extension traits are separate (`trait SnapshotDriver`, `trait DedupDriver`), and callers that need snapshots require `where F: FsDriver + SnapshotDriver`.

```
# Sketch — research only
struct VfsMount<F: FsDriver>:
    driver: F
    mount_opts: MountOptions

fn snapshot<F: FsDriver + SnapshotDriver>(mount: VfsMount<F>, name: Str) -> Result<SnapshotId, FsError>:
    return mount.driver.create_snapshot(name)
```

**Pros:**
- Zero runtime overhead; all dispatch resolved at compile time.
- Compile error if a caller tries to use a snapshot op on a non-snapshot driver. Strongest static safety.
- No enum variant list to maintain.

**Cons:**
- **Critical: heterogeneous mount table is impossible.** A kernel `List<VfsMount<???>>` cannot hold both `VfsMount<Fat32Driver>` and `VfsMount<NvfsDriver>` without `dyn`. The VFS layer cannot iterate all mounts generically. SimpleOS needs FAT32 and NVFS mounted simultaneously (e.g., boot partition on FAT32, data on NVFS). This is a fatal limitation.
- Callers that don't know which FS is mounted (e.g., the VFS lookup path) cannot be written without `dyn` or a discriminating enum wrapper.
- Option F is suitable for compile-time embedded systems where exactly one FS type is ever mounted. Not suitable for SimpleOS.

**Assessment:** Eliminated for SimpleOS. Cannot support a heterogeneous mount table without `dyn`.

### 3.5 Option G — Handle Pool / fd-Table Central Dispatch

**Design:** The FS driver does not expose a trait. Instead, it registers a dispatch table of function pointers (or closures) indexed by `(mount_id, op_id)`. All I/O goes through a central `vfs_dispatch(mount_id, op_id, args)` function. Extension drivers register additional `op_id` values.

```
# Sketch — research only
struct OpId:
    value: i32

struct VfsTable:
    entries: Map<(MountId, OpId), fn(VfsArgs) -> VfsResult>

fn vfs_dispatch(table: VfsTable, mount: MountId, op: OpId, args: VfsArgs) -> VfsResult:
    match table.entries.get((mount, op)):
        Some(f) => f(args)
        None => VfsResult::Unsupported
```

**Pros:**
- True heterogeneous mount table: `VfsTable` holds entries for any driver type.
- Extension drivers add entries for new `OpId` values without modifying a central enum.
- Closest to how real kernels (FreeBSD `vop_bypass`, Haiku `io_request`) actually dispatch.

**Cons:**
- Requires first-class function values or closures in Simple. Simple supports closures, but `nogc_sync_mut` closures that capture mutable driver state are complex (cannot modify captured vars; module closures work, inner closures cannot).
- Type safety is lost at the dispatch boundary: `VfsArgs` must be a union or opaque pointer, leading to unchecked casts per-op. This is the "untyped IPC" problem.
- Debugging and tooling become harder: the operation table is a runtime data structure, not a compile-time interface.
- Op IDs for extensions are assigned dynamically (risk of collision) or require a central registry (negates the open-extensibility benefit).
- In `nogc_sync_mut`, a `Map<(MountId, OpId), closure>` may require heap allocation — problematic in baremetal / kernel contexts.

**Assessment:** Viable for a kernel-space implementation in C or Rust. In Simple's `nogc_sync_mut` with closure limitations, the type-erasure cost is high. Not recommended as primary; elements (numeric op IDs, central VFS table indexed by mount ID) can be borrowed as an implementation detail within E'.

### 3.6 Recommended Option: E' with G-inspired Mount Table

**Recommendation: Option E' (enum-wrapped extension handle) for the capability-probe interface, with a G-inspired explicit mount registry for heterogeneous driver coexistence.**

**Rationale:**

1. **No dyn.** E' uses only concrete structs and enum variants. The `Extension` enum's variants are concrete types, not trait objects. All dispatch is by `match`, resolved at compile time per variant.

2. **Heterogeneous mount table.** The mount table holds `MountEntry` structs that carry a driver-type tag and a per-driver opaque integer ID (similar to a file descriptor). The VFS layer dispatches via a per-entry function table that is a plain struct (not a `dyn`-based vtable). This is achievable by wrapping each driver type in a driver-type enum:

```
# Sketch — research only
enum DriverInstance:
    Fat32(Fat32Driver)
    Nvfs(NvfsDriver)
    RamFs(RamFsDriver)

struct MountEntry:
    id: MountId
    driver: DriverInstance
    opts: MountOptions
```

A `match` on `DriverInstance` dispatches to the concrete driver. The VFS layer's `open`, `read`, `write` etc. each have a `match mount.driver { DriverInstance::Fat32(d) => d.open(...), DriverInstance::Nvfs(d) => d.open(...) }`. This is verbose but safe, closed-world, and no `dyn`.

3. **FAT32 compatibility.** FAT32 implements `FsDriver` with all extension probes returning `None` / capability set = empty. No extension structs are instantiated. Binary size overhead: zero for unused extension paths.

4. **NVFS compatibility.** NVFS implements all extension probes for its supported capabilities. The `probe(Capability::Snapshot)` path returns `Some(Extension::Snapshot(SnapshotExt { ... }))`.

5. **`nogc_sync_mut` compatibility.** No heap allocation in the hot path: `probe` returns an `Option<Extension>` by value. `Extension` enum must fit in a register-sized slot (it will, if `SnapshotExt` is a pointer-to-driver + operation metadata, not a large struct). Extension structs hold a borrowed reference to the driver; callers do not own them beyond the current call scope.

6. **Caller ergonomics.** Two-step: check `capabilities()` bitmask (O(1)), then `probe()` only if needed. `match` on `Extension` is exhaustive. Adding a new extension requires: (a) add a variant to `Capability` enum, (b) add a variant to `Extension` enum, (c) add a concrete `XxxExt` struct, (d) update NVFS's `probe` impl. FAT32's `probe` needs no change (default `None`).

7. **Compile-time safety.** Callers that `match` on `Extension` get a compiler error if they miss a new variant (unless they use `_`). This is structurally equivalent to the exhaustiveness check that `dyn`-based systems cannot provide.

---

## 4. Current SimpleOS FAT32 Inventory

### 4.1 Glob Results

Search `examples/simple_os/**/*fat*`: **no results** — no FAT32 driver exists yet in `examples/simple_os/`.

Search `src/lib/nogc_sync_mut/fs/**`:
- `src/lib/nogc_sync_mut/fs/__init__.spl` — fs module doc, declares submodules (path, nvfs)
- `src/lib/nogc_sync_mut/fs/path.spl` — `Path`, `File`, `Directory` structs and operations
- `src/lib/nogc_sync_mut/fs/path.smf` — precompiled module
- `src/lib/nogc_sync_mut/fs/__init__.smf` — precompiled module
- `src/lib/nogc_sync_mut/fs/nvfs/__init__.spl` — NVFS submodule
- `src/lib/nogc_sync_mut/fs/nvfs/api.spl` — re-exports `Arena`, `ArenaHandle`, `ArenaAppendResult` from `std.storage.arena`
- `src/lib/nogc_sync_mut/fs/nvfs/extent_map.spl` — extent map (not read)
- `src/lib/nogc_sync_mut/fs/nvfs/superblock_if.spl` — `SuperblockHeader`, `SuperblockReader` trait

### 4.2 Current Op Surface

**`std.fs.path`** provides a POSIX-flavored host filesystem interface:
- `Path`: string-valued path construction (`join`, `normalize`, `file_name`, `file_stem`, `extension`, `with_extension`)
- `File`: `new`, `exists`, `read`, `write`, `copy_to`, `delete`
- `Directory`: `new`, `create_all`, `list`, `list_paths`
- Platform helpers: `get_home_dir`, `get_temp_dir`
- Low-level: `app.io.file_mmap_read_*`, `app.io.file_ops`, `app.io.dir_ops`

This module calls through to the host OS (Linux/macOS/Windows) via FFI. It is NOT a VFS for SimpleOS's own kernel filesystem.

**NVFS skeleton** (`std.fs.nvfs`):
- `SuperblockHeader` struct (magic, version_major, version_minor, fs_uuid_lo/hi, checkpoint_gen, created_unix_ns)
- `SuperblockReader` trait: `read_header() -> SuperblockHeader`, `is_mounted() -> bool`, `last_checkpoint_generation() -> i64`
- `Arena` trait, `ArenaHandle`, `ArenaAppendResult` re-exported from `std.storage.arena` (append-oriented arena API)
- `extent_map` submodule (skeleton, not read)

### 4.3 VFS Abstraction

No VFS abstraction currently exists. SimpleOS calls the host filesystem (on Linux/QEMU) via the `std.fs.path` module which wraps host syscalls. There is no kernel-internal VFS dispatch layer, no `FsDriver` trait, and no mount table. The `nvfs` subdirectory is a skeleton with trait definitions but no implementation and no integration with any OS layer.

### 4.4 How the OS Calls the FS Today

- Application-level: `File.read()`, `Directory.list()` → `app.io.file_ops` → host syscalls via FFI
- NVFS: `SuperblockReader` trait exists but is not called from any OS path (skeleton only)
- FAT32: not implemented anywhere in the tree
- No VFS dispatch layer; all FS access is direct to host or placeholder

---

## 5. Proposed NVFS Extension Interfaces

Based on the E' recommendation (§3.6), the following extension interfaces are proposed for NVFS. Each is a concrete struct returned by `FsDriver::probe(Capability::X)` as `Extension::X(XExt)`.

### 5.1 Snapshot / Clone / Subvolume

```
# Sketch — research only
struct SnapshotExt:
    """Snapshot, clone, and subvolume operations.
    NVFS uses copy-on-write tree semantics; snapshots are O(1) metadata operations.
    Analogous to btrfs BTRFS_IOC_SNAP_CREATE, ZFS 'zfs snapshot'.
    """
    fn create(vol: VolumeId, name: Str) -> Result<SnapshotId, FsError>
    fn delete(id: SnapshotId) -> Result<(), FsError>
    fn list(vol: VolumeId) -> Result<List<SnapshotId>, FsError>
    fn clone_vol(src: VolumeId, dst_name: Str) -> Result<VolumeId, FsError>
    fn create_subvol(parent: VolumeId, name: Str) -> Result<VolumeId, FsError>
    fn delete_subvol(vol: VolumeId) -> Result<(), FsError>
```

Snapshot identifiers are opaque 64-bit handles. The NVFS pmap-root CAS operation (noted in §4 state.md context) makes atomic snapshot creation a single metadata write.

### 5.2 Checksum + Self-Heal

```
struct ChecksumExt:
    """Per-block checksum verification and self-healing via redundant copies.
    Analogous to ZFS block checksum + mirror heal, btrfs BTRFS_IOC_SCRUB.
    """
    fn verify_file(handle: FileHandle) -> Result<ChecksumReport, FsError>
    fn heal_file(handle: FileHandle, replica: ReplicaHint) -> Result<HealReport, FsError>
    fn checksum_algo() -> ChecksumAlgo  # e.g., Blake3, SHA256, xxHash
```

### 5.3 Send / Receive

```
struct SendReceiveExt:
    """Incremental stream serialization / deserialization.
    Analogous to btrfs send/receive, ZFS send/receive.
    Source: btrfs_ioctl_send_args, ZFS_IOC_SEND.
    """
    fn send_full(snap: SnapshotId, out: WriteHandle) -> Result<i64, FsError>
    fn send_incremental(base: SnapshotId, target: SnapshotId, out: WriteHandle) -> Result<i64, FsError>
    fn receive(vol: VolumeId, in_stream: ReadHandle) -> Result<SnapshotId, FsError>
```

### 5.4 Dedup (Offline Reflink)

```
struct DedupExt:
    """Offline deduplication via content-hash matching and extent sharing.
    Analogous to btrfs duperemove, BTRFS_IOC_FILE_EXTENT_SAME.
    """
    fn scan_range(handle: FileHandle, offset: i64, len: i64) -> Result<List<DedupCandidate>, FsError>
    fn dedup_ranges(entries: List<DedupEntry>) -> Result<DedupReport, FsError>
```

### 5.5 Scrub

```
struct ScrubExt:
    """Background data integrity scan.
    Analogous to ZFS scrub, btrfs BTRFS_IOC_SCRUB.
    """
    fn start(vol: VolumeId) -> Result<ScrubHandle, FsError>
    fn status(handle: ScrubHandle) -> Result<ScrubStatus, FsError>
    fn cancel(handle: ScrubHandle) -> Result<(), FsError>
```

Scrub runs as a background task (see §6 lifecycle). The `ScrubHandle` is an opaque ID for the SimpleOS scheduler's task table.

### 5.6 Compress

```
struct CompressExt:
    """Per-file or per-volume compression settings.
    Analogous to btrfs compression property, ZFS 'compression' property.
    """
    fn set_compression(handle: FileHandle, algo: CompressAlgo) -> Result<(), FsError>
    fn get_compression(handle: FileHandle) -> Result<CompressAlgo, FsError>
    fn compress_algo_list() -> Result<List<CompressAlgo>, FsError>
```

`CompressAlgo` enum: `None`, `Lz4`, `Zstd`, `Snappy`. NVFS should default to `Lz4` for hot data and `Zstd` for cold data.

### 5.7 Quota / Reservation

```
struct QuotaExt:
    """Quota and reservation management.
    Analogous to ZFS quota/reservation, btrfs qgroup.
    """
    fn set_quota(vol: VolumeId, limit_bytes: i64) -> Result<(), FsError>
    fn get_usage(vol: VolumeId) -> Result<QuotaReport, FsError>
    fn set_reservation(vol: VolumeId, reserved_bytes: i64) -> Result<(), FsError>
```

### 5.8 Reflink / CloneRange

```
struct ReflinkExt:
    """Copy-on-write file range cloning (reflink).
    Source: Linux FICLONERANGE ioctl, btrfs BTRFS_IOC_CLONE_RANGE,
    cp --reflink=always, macOS APFS clonefile(2).
    """
    fn clone_range(src: FileHandle, src_off: i64, dst: FileHandle, dst_off: i64, len: i64) -> Result<(), FsError>
    fn clone_file(src: FileHandle, dst_path: Path) -> Result<FileHandle, FsError>
```

---

## 5a. POSIX-over-NVFS Wrapper

### 5a.1 Context

NVFS's native API is append-oriented: the `Arena` trait (from `std.storage.arena`) supports `append`, `seal`, `discard`, and `read` operations. Consumers such as spostgre require this semantics. However, POSIX applications and the `std.fs.path` layer expect:
- Random-write at arbitrary offsets (`pwrite(fd, buf, off)`)
- Truncation (`ftruncate(fd, len)`)
- Atomic rename (`rename(old, new)`)
- Deferred unlink (file removed while open, data persists until close)
- Writable mmap (`mmap(MAP_SHARED, PROT_WRITE)`)

Translating these POSIX semantics onto an append-only arena is expensive (copy-on-write shadow allocation per write). This translation should be **explicitly opt-in**, never automatic.

### 5a.2 Module Placement

Proposed module: `src/lib/nogc_sync_mut/fs/nvfs_posix/`

The POSIX shim is a separate module from NVFS core. Callers must explicitly import `std.fs.nvfs_posix` to use it. The NVFS core driver does not depend on this module.

**Capability flag:** `Capability::PosixCompat`. A POSIX-shim-enabled NVFS mount responds to `driver.probe(Capability::PosixCompat)` with `Some(Extension::PosixCompat(PosixCompatExt { ... }))`. A pure NVFS mount (no shim) returns `None`.

### 5a.3 pwrite Translation

`pwrite(fd, buf, off)` at arbitrary offset → arena COW shadow:
1. Allocate a new arena (via `arena_create`).
2. Read the current arena's content from `[0, off)` into the new arena via `arena_append`.
3. Append `buf` (the new bytes for range `[off, off+len)`) via `arena_append`.
4. Read the old arena's content from `[off+len, end)` and append.
5. Atomic publish-flip: update the pmap entry (pmap-root CAS) from old arena ID to new arena ID.
6. Schedule `arena_discard` on the old arena (deferred; the old arena may be referenced by snapshots).

This is O(file_size) per random write — explicitly documented in the shim API. Callers choosing POSIX compat accept this cost.

### 5a.4 ftruncate Translation

`ftruncate(fd, len)`:
- If `len < current_size`: arena seal current + create new arena + copy `[0, len)` from old + publish-flip.
- If `len > current_size`: arena seal + create new arena + copy full old content + `arena_append` zero bytes for `[current_size, len)`.
- If `len == current_size`: no-op.

### 5a.5 rename Translation

`rename(old_path, new_path)`:
- NVFS manifest (pmap) supports atomic CAS swap of path-to-arena-id entries.
- Implementation: `manifest_swap(old_path, new_path)` in the pmap layer.
- Analogous to btrfs dentry rename (atomic directory tree update).
- This is likely already supported in NVFS's pmap-root CAS; the POSIX shim calls the existing mechanism.

### 5a.6 unlink with Open Handles

`unlink(path)` while a file handle is open:
- Remove directory entry immediately (pmap update).
- Arena ID is retained in a per-mount "open handles" reference table.
- When the last `FileHandle` for that arena ID is closed (reference count → 0), enqueue `arena_discard`.
- Reference table is a fixed-size array in `nogc_sync_mut` (no heap allocation); max open handles is a mount-time constant.

### 5a.7 mmap(MAP_SHARED, PROT_WRITE) Emulation

`mmap(MAP_SHARED, PROT_WRITE)` over NVFS:
1. Allocate a COW shadow arena (copy of the file content).
2. Map the shadow arena's backing memory pages into the user address space (requires SimpleOS memory manager support — page-fault trap).
3. On page fault write: mark page dirty in a per-arena dirty-page bitmap.
4. On `msync(MS_SYNC)` or `munmap`: flush dirty pages using the pwrite COW protocol (§5a.3) applied per dirty page range.
5. On `msync(MS_ASYNC)`: enqueue the flush as a background task (SimpleOS scheduler).

This requires kernel-level page-fault integration; it is out of scope for the POSIX shim module itself (the shim provides the arena-level flush logic; page-fault wiring is a kernel MM concern).

### 5a.8 API Shape

```
# Sketch — research only
struct PosixCompatExt:
    """POSIX emulation layer over NVFS append-only arenas.
    ALL operations are O(file_size). Opt-in only. Never automatic.
    """
    fn pwrite(handle: FileHandle, buf: [u8], offset: i64) -> Result<i64, FsError>
    fn ftruncate(handle: FileHandle, new_len: i64) -> Result<(), FsError>
    fn rename(old_path: Path, new_path: Path) -> Result<(), FsError>
    fn unlink_deferred(path: Path) -> Result<(), FsError>
    fn mmap_write_flush(handle: FileHandle, dirty_ranges: List<(i64, i64)>) -> Result<(), FsError>
```

### 5a.9 Advertising as a Capability

```
# In the NVFS driver's probe() impl:
fn probe(cap: Capability) -> Option<Extension>:
    match cap:
        Capability::PosixCompat =>
            if self.opts.posix_compat_enabled:
                Some(Extension::PosixCompat(PosixCompatExt { driver_ref: self }))
            else:
                None
        ...
```

The mount option `posix_compat_enabled` is false by default. Operators must explicitly pass `posix_compat=1` in mount arguments. No POSIX compat is engaged on a clean NVFS mount.

---

## 6. Driver Lifecycle

### 6.1 Mount

The VFS mount sequence:
1. Parse mount options from `MountOptions` struct (source device path, FS type, flags, FS-specific args).
2. Instantiate the driver: `Fat32Driver::mount(dev, opts)` or `NvfsDriver::mount(dev, opts)`. Returns `Result<DriverInstance, FsError>`.
3. Wrap in `DriverInstance` enum variant: `DriverInstance::Fat32(driver)` or `DriverInstance::Nvfs(driver)`.
4. Create `MountEntry { id: MountId::allocate(), driver, opts }` and insert into the global `MountTable`.
5. Verify superblock: for NVFS, call `SuperblockReader::read_header()` and validate `magic`, `version_major`. Reject if version mismatch (see §6.3).

### 6.2 Unmount

1. Drain in-flight operations: wait for all `FileHandle` reference counts to reach zero (or force-close with `FsError::DeviceGone` for each open handle).
2. Flush dirty data: call `driver.sync()`. For NVFS: seal all open arenas and write checkpoint.
3. Cancel background tasks: send cancellation to scrub/vacuum/dedup scheduler entries for this mount ID.
4. Call `driver.unmount()`. Returns `Result<(), FsError>`.
5. Remove `MountEntry` from `MountTable`.

### 6.3 Remount (Live Flag Change)

Supported for read-only↔read-write transitions and some mount-option changes:
1. Call `driver.remount(new_opts)`. Driver validates compatibility (e.g., cannot enable `posix_compat` on a running read-only mount).
2. Returns `Err(FsError::InvalidArgument)` for incompatible changes.
3. Callers see no disruption; in-flight handles remain valid.

### 6.4 Superblock Versioning

`SuperblockHeader` fields (from `src/lib/nogc_sync_mut/fs/nvfs/superblock_if.spl`):
- `magic: i64` — must match `NVFS_MAGIC` constant
- `version_major: i32` — incompatible changes (must match exactly)
- `version_minor: i32` — backward-compatible additions (driver must accept `<= current_minor`)
- `fs_uuid_lo / fs_uuid_hi: i64` — 128-bit volume UUID
- `checkpoint_gen: i64` — monotonic checkpoint counter
- `created_unix_ns: i64` — creation timestamp

Mount rejects if `version_major` mismatch. Mount accepts if `version_minor` is older than driver (driver knows how to handle older-format superblocks). Mount rejects if `version_minor` is newer than driver (unknown fields may be present).

### 6.5 Background Threads

Background tasks integrated with the SimpleOS scheduler:

| Task | Trigger | Period | Cooperative yield |
|------|---------|--------|-------------------|
| Scrub | Manual or periodic | User-configured (e.g., weekly) | Every 1 MB verified |
| Vacuum (arena GC) | Arena-discard queue non-empty | Event-driven | Every 100 arenas freed |
| Dedup (offline) | Manual trigger | User-configured | Every 1000 blocks scanned |
| Checkpoint flush | Dirty data threshold or timer | Every 5 s (default) | N/A (atomic write) |

Background tasks receive a `MountId` and a cancellation token. On unmount, the scheduler sends the cancellation token, and the task must complete its current work unit and exit. Tasks must not hold locks across a cooperative yield.

---

## 7. Concurrency

### 7.1 Sync Trait Surface (`nogc_sync_mut`)

The `FsDriver` trait and all extension traits live in `nogc_sync_mut`: no GC, no async. Operations are blocking. The VFS layer's callers (syscall handlers, kernel threads) hold a reference to a `MountEntry` while in a call. The `MountEntry` is protected by a per-mount reader-writer spinlock:
- Readers (`open`, `read`, `stat`, `readdir`): hold read lock.
- Writers (`write`, `create`, `unlink`, `rename`): hold write lock.
- Mount/unmount: hold exclusive write lock, wait for all readers to drain.

### 7.2 Async Variant (`nogc_async_mut`)

An async sibling trait `AsyncFsDriver` in `nogc_async_mut` mirrors the sync surface with `async fn` equivalents. The async variant is used by the SimpleOS async I/O subsystem (for DMA-backed NVMe operations). The `AsyncFsDriver` wraps the sync `FsDriver` via a thread-pool adapter or exposes native async NVMe queue submission.

Design rule: async wrappers are not in scope for this research document's recommendations; the VFS interface proposal covers the sync surface only.

### 7.3 Lock Discipline at VFS↔Driver Boundary

The VFS layer acquires the per-mount lock before calling into the driver. Drivers must not acquire the per-mount lock internally (would deadlock). Drivers may use their own internal fine-grained locks (e.g., per-inode lock for NVFS extent map updates). The VFS↔driver boundary must be treated as a lock-level transition: VFS holds outer lock, driver holds inner locks.

### 7.4 Per-File Handle Concurrency

`FileHandle` carries a per-handle sequence number. Concurrent reads from multiple handles to the same file are allowed (driver maintains read-only cursors). Concurrent writes to the same file go through a per-inode mutex inside the driver. The VFS layer does not serialize per-file writes; that is the driver's responsibility.

### 7.5 Capability Probe Concurrency

`probe(cap)` and `capabilities()` are read-only operations that may be called without holding the write lock. Extension structs returned by `probe` hold a borrowed reference to the driver; callers must not retain extension struct references across a lock release boundary.

---

## 8. Error Model

### 8.1 Single `FsError` Enum

All VFS and driver errors are expressed as `FsError` variants. No panics for expected conditions.

```
# Sketch — research only
enum FsError:
    Unsupported          # operation not supported by this driver
    NotFound             # path or handle does not exist
    PermissionDenied     # caller lacks permission
    IoError(i32)         # hardware I/O error; inner value is device error code
    NoSpace              # out of space
    InvalidArgument      # bad argument (bad offset, null handle, etc.)
    TooManyHandles       # open handle limit reached
    Transient(i32)       # retry-able error; inner is hint (e.g., contention code)
    Corrupt              # data integrity failure (checksum mismatch, bad magic)
    DeviceGone           # device removed while in use
    VersionMismatch      # superblock version incompatible
    WouldBlock           # non-blocking call would block (for async callers)
    Interrupted          # syscall interrupted (for signal-aware callers)
```

### 8.2 `Unsupported` vs `Transient`

- `Unsupported`: the operation will never succeed on this driver. Caller should not retry; should fall back (e.g., try a different code path, return ENOTSUP to userspace).
- `Transient(code)`: the operation failed due to a temporary condition (lock contention, DMA queue full, NVMe timeout). Caller may retry with backoff.

### 8.3 No Panics for Expected Failures

Drivers must not call `panic` for conditions that are expected in normal operation (device errors, permission failures, out-of-space). Panics are reserved for programmer errors detected by assertions (e.g., double-free of a handle, lock order violation). This follows the `nogc_sync_mut` philosophy: no unwinding, no exceptions, no hidden paths.

### 8.4 Error Propagation

All driver functions return `Result<T, FsError>`. Callers use the `?` operator. VFS layer translates `FsError` to POSIX `errno` values at the syscall boundary:

| FsError | errno |
|---------|-------|
| Unsupported | ENOTSUP |
| NotFound | ENOENT |
| PermissionDenied | EACCES |
| IoError | EIO |
| NoSpace | ENOSPC |
| InvalidArgument | EINVAL |
| TooManyHandles | EMFILE |
| Transient | EAGAIN |
| Corrupt | EIO |
| DeviceGone | ENXIO |
| VersionMismatch | EINVAL |
| WouldBlock | EAGAIN |
| Interrupted | EINTR |

---

## 9. Migration Path

### 9.1 Current State

As of 2026-04-17:
- No FAT32 driver implemented in `examples/simple_os/` or `src/lib/`.
- No VFS dispatch layer.
- NVFS skeleton exists (`std.fs.nvfs`): `SuperblockReader` trait, arena re-exports. No implementation.
- All filesystem access in SimpleOS is via host syscalls through `std.fs.path` (wraps host OS).

### 9.2 Phase 1 — Define Core Interfaces (No Breaking Changes)

1. Create `src/lib/nogc_sync_mut/fs/vfs/__init__.spl` with:
   - `FsDriver` trait (required op surface)
   - `Extension` enum (all variants, initially: `Snapshot(SnapshotExt)`, `Checksum(ChecksumExt)`, `Reflink(ReflinkExt)`, `PosixCompat(PosixCompatExt)`)
   - `Capability` enum
   - `CapabilitySet` bitmask struct
   - `FsError` enum
   - `FileHandle`, `DirHandle`, `MountId`, `VolumeId` opaque types
   - `MountEntry`, `DriverInstance` enum (Fat32 variant only initially)
   - `MountTable` struct

2. No existing code changes. This is additive.

### 9.3 Phase 2 — Stub FAT32 Driver

1. Create `src/lib/nogc_sync_mut/fs/fat32/__init__.spl`.
2. `Fat32Driver` struct implementing `FsDriver`:
   - `open`, `close`, `read`, `write`, `stat`, `readdir`: stub implementations returning `Err(FsError::IoError(0))` initially.
   - `probe(cap) -> None` for all caps (FAT32 supports no extensions).
   - `capabilities() -> CapabilitySet::empty()`.
3. Add `DriverInstance::Fat32(Fat32Driver)` variant to `DriverInstance` enum.
4. Update `MountTable` to accept Fat32 mounts.

**Concrete breakages:** none (no callers yet).

### 9.4 Phase 3 — Wire VFS to SimpleOS Syscall Layer

1. Add syscall handlers for `open`, `read`, `write`, `close`, `stat`, `readdir` in `examples/simple_os/arch/x86_64/`.
2. Handlers call `MountTable::resolve(path) -> MountEntry`, then dispatch via `match entry.driver { ... }`.
3. `FsError` → errno translation at syscall boundary.

**Concrete breakages:**
- `examples/simple_os/arch/x86_64/boot/baremetal_stubs.c` (currently modified per git status) may need syscall table entries updated.
- Any existing SimpleOS test that calls host-syscall paths will need to be redirected or mocked.

### 9.5 Phase 4 — Retrofit NVFS Skeleton

1. Implement `NvfsDriver` struct in `src/lib/nogc_sync_mut/fs/nvfs/`.
2. Implement `FsDriver` for `NvfsDriver` using the existing arena API (`std.storage.arena`).
3. Add `DriverInstance::Nvfs(NvfsDriver)` variant.
4. Implement extension probes for NVFS capabilities.

**Concrete breakages:**
- Any code that imports `std.fs.nvfs.{SuperblockReader, Arena}` directly will continue to work (those symbols are unchanged).
- New mount code path requires `SuperblockReader` to be called during `NvfsDriver::mount()`.

### 9.6 Phase 5 — Add POSIX Shim

1. Create `src/lib/nogc_sync_mut/fs/nvfs_posix/__init__.spl` with `PosixCompatExt`.
2. Add `Capability::PosixCompat` and `Extension::PosixCompat(PosixCompatExt)` variants.
3. Add `posix_compat_enabled` to NVFS mount options.

**Concrete breakages:** none (opt-in, additive).

### 9.7 Shim Summary

| Breakage | Shim |
|---------|------|
| baremetal_stubs.c syscall table | Add VFS syscall numbers; existing stubs return ENOSYS |
| std.fs.path callers on SimpleOS | Redirect to VFS layer via #ifdef or separate import path |
| NVFS arena tests | No breakage; arena API unchanged |
| spostgre NVFS storage | spostgre uses Arena directly; no VFS layer involved |

---

## 10. Capability Catalogue

Full enumeration of proposed `Capability` variants. For each: semantics, FAT32 support, NVFS-native support, NVFS+POSIX-shim support.

| Capability | Semantics | FAT32 | NVFS-native | NVFS+POSIXshim |
|-----------|-----------|-------|-------------|----------------|
| `COW` | Copy-on-write writes (write does not overwrite in-place) | No | Yes | Yes (shim uses COW internally) |
| `Snapshot` | Point-in-time consistent snapshot of a volume | No | Yes (O(1) pmap CAS) | Yes (snapshots of shim state) |
| `Clone` | Create a writable COW clone of a volume | No | Yes | Yes |
| `Dedup` | Offline content-hash deduplication with extent sharing | No | No | No (shim arenas not dedup-friendly) |
| `Checksum` | Per-block checksum verification | No | Yes (configurable algo) | Yes (inherits from NVFS) |
| `SelfHeal` | Automatic repair via redundant copies on checksum failure | No | No | No |
| `SendReceive` | Incremental stream serialization for backup/replication | No | Yes | Yes (snapshot-based) |
| `Compress` | Transparent per-file or per-volume compression | No | No | No |
| `Encrypt` | Transparent encryption at-rest | No | Planned | No |
| `Quota` | Per-volume space quota and reservation | No | No | No |
| `Reflink` | Copy-on-write file range clone (O(1) metadata op) | No | Yes | Yes |
| `Atime` | Access-time tracking | Limited (FAT32 has access date only, no time) | Yes | Yes |
| `Xattr` | Extended attributes | No (no xattr in FAT32) | Yes | Yes |
| `Acl` | POSIX ACLs | No | Yes (via xattr storage) | Yes |
| `CaseFold` | Case-insensitive name lookup | Yes (FAT32 short names are case-insensitive) | Optional (mount flag) | Optional |
| `Hardlinks` | Multiple directory entries to one inode | No | Yes | Yes |
| `SparseFiles` | Sparse file holes (unallocated blocks read as zeros) | No | Yes (via extent map) | Partial (pwrite shim allocates all blocks) |
| `LargeFiles` | Files >4 GiB | FAT32: up to 4 GiB (32-bit size field) | Yes (i64 offsets) | Yes |
| `UnicodeNames` | Unicode filenames (not ASCII-only) | Limited (FAT32 LFN: UCS-2) | Yes (UTF-8) | Yes |
| `CaseSensitive` | Case-sensitive name lookup | No | Yes (default) | Yes |
| `PosixCompat` | POSIX random-write / truncate / rename / unlink semantics | N/A (FAT32 is accessed via host VFS, which is POSIX) | No (explicit opt-in required) | Yes (this IS the shim) |
| `AsyncIo` | Async non-blocking I/O via DMA / NVMe queues | No | Planned (`nogc_async_mut`) | Planned |

**Notes:**
- FAT32 "support" refers to the native FAT32 format capability, independent of the host OS's POSIX wrapper.
- NVFS-native = what the NVFS core driver supports without the POSIX shim.
- NVFS+POSIXshim = what is available when `posix_compat=1` is set at mount time.
- `Encrypt` is marked "Planned" for NVFS — it is referenced in the capability catalogue but not in scope for the current design.

---

## 11. Primary Sources

| Source | Used in |
|--------|---------|
| `Documentation/filesystems/vfs.rst` (kernel.org, Linux kernel source) | §1.1 — Linux VFS `super_operations`, `inode_operations`, `file_operations`, `dentry_operations`, `address_space_operations`, NULL-op sentinel |
| `include/linux/fs.h` (Linux kernel) | §1.1 — struct definitions, `s_flags` bitmask |
| FreeBSD Architecture Handbook §5, `sys/sys/vnode.h`, `sys/kern/vfs_lookup.c` | §1.2 — `vfsops`, `vnodeops`, `vop_bypass`, FreeBSD stacking model |
| illumos `usr/src/uts/common/sys/vfs.h`, `vnode.h` | §1.3 — `vfs_ops_t`, `vnodeops_t`, `VFS_FEATURE_*` bitmask, `vfs_has_feature()` |
| Windows Driver Kit `ntifs.h`, IFS documentation | §1.4 — IRP major codes, `FAST_IO_DISPATCH`, `FSCTL_*` control codes, `FILE_FS_ATTRIBUTE_INFORMATION` |
| XNU `bsd/sys/mount.h`, `bsd/sys/vnode.h`, Apple Kernel Programming Guide §File Systems | §1.5 — `vfs_fsentry`, `vnop_desc`, `vfe_vfsops_vfsflags`, `vfs_getattr` |
| Haiku `headers/private/kernel/fs_interface.h` | §1.6 — `fs_volume_ops`, `fs_vnode_ops`, `io_request` pattern |
| libfuse `fuse_lowlevel.h`, `fuse.h`; in-kernel `linux/fuse.h` | §1.7 — `fuse_operations`, `fuse_conn_info.capable/want`, `FUSE_CAP_*` flags |
| Plan 9 manual pages `intro(5)`, `stat(5)` | §1.8 — 9P wire protocol, `Tversion`/`Rversion` negotiation |
| `src/lib/nogc_sync_mut/fs/nvfs/superblock_if.spl` (this repo) | §4, §6.4 — `SuperblockHeader`, `SuperblockReader` trait |
| `src/lib/nogc_sync_mut/fs/nvfs/api.spl` (this repo) | §4 — `Arena`, `ArenaHandle`, `ArenaAppendResult` re-export |
| `src/lib/nogc_sync_mut/fs/__init__.spl` (this repo) | §4 — fs module structure, host filesystem wrapping |
| `doc/05_design/nvfs_design.md` (referenced in api.spl) | §5a — NVFS arena append-oriented design, pmap-root CAS |
| Linux `FICLONERANGE` ioctl, btrfs `BTRFS_IOC_CLONE_RANGE` | §5.8 — Reflink / CloneRange design |
| btrfs `BTRFS_IOC_SEND`, ZFS `ZFS_IOC_SEND` | §5.3 — Send/Receive design |
| btrfs `BTRFS_IOC_FILE_EXTENT_SAME` (duperemove), APFS `clonefile(2)` | §5.4, §5.8 — Dedup, Reflink prior art |
| Linux `FALLOC_FL_PUNCH_HOLE`, `SEEK_DATA`/`SEEK_HOLE` | §1.1 — file_operations extension ops |
| FreeBSD `VFS_SET` macro | §1.2 — vfsops registration |
