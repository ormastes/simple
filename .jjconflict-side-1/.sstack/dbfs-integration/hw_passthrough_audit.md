# AC-6 Deep Audit — DBFS Hardware Direct-Accessibility

**Feature:** dbfs-integration
**AC:** AC-6 — *"Existing NVMe/PCI/virtio/null_block drivers remain reachable; DBFS plugs into the block layer through the same driver-manifest path. No syscall-level block I/O regression; raw block access stays available for filesystems that bypass DBFS."*
**Auditor:** AC-6 sub-agent (Sonnet, parallel run)
**Date:** 2026-04-28
**Scope:** read-only audit; no `.spl`, `state.md`, or architecture edits.

---

## 0. Headline

| Sub-claim of AC-6 | Status |
|---|---|
| Existing NVMe driver reachable / unaffected | **PROVEN** |
| Existing PCI driver reachable / unaffected | **PROVEN** |
| Existing virtio (block + net + gpu) drivers reachable / unaffected | **PROVEN** |
| Existing framebuffer driver reachable / unaffected | **PROVEN** |
| Existing `null_block` driver reachable | **GAP — driver does not exist on `main`** |
| DBFS plugs into the block layer through the **same driver-manifest path** | **GAP — terminology + missing seam** |
| No syscall-level block I/O regression | **PROVEN (by isolation, see §2)** |
| Raw block access stays available for filesystems that bypass DBFS | **PROVEN** |
| `DriverInstance` dispatch shape preserved when adding `DbFs(driver: DbFsDriver)` | **PROVEN** |

**Bottom line:** AC-6 is **partially satisfied**. The "existing drivers stay reachable" half is evidentially proven (DBFS code in `src/lib/nogc_sync_mut/db/**` contains **zero** references to any block-layer / NVMe / PCI / virtio / DMA / IRQ / sector code paths). The "DBFS plugs into the block layer" half is **not** demonstrated by current code — the only DBFS constructor on disk is `DbFsDriver.new_hosted()` (in-memory), and the planned `RawNvmeArena` / `DbFsDriver.open_on_device(BlockDevice)` seam from Phase 4 prereqs has **not** been created. The `dbfs_hw_passthrough_spec.spl` only verifies mount-table dispatch isolation between sibling mounts, not any wire-through to a real block device.

---

## 1. Block-layer API map (current surface)

### 1.1 `BlockDevice` traits — three definitions co-exist

| File | Trait | Methods |
|---|---|---|
| `src/os/services/block_device.spl` (per Research 04) | `BlockDevice` | `read_sector(lba: u64, buffer: [u8]) -> Result<bool, text>`, `write_sector(lba: u64, data: [u8]) -> Result<bool, text>`, `sector_size() -> u32` |
| `src/os/drivers/nvme/block_device.spl:14` | `BlockDevice` (kernel-side, sync) | sync sector I/O |
| `src/os/drivers/nvme/block_device.spl:29` | `AsyncBlockDevice` | notification-based completion (`read_sectors_notify`, `write_sectors_notify`, `flush_notify`) |
| `src/lib/nogc_sync_mut/fs_driver/block_device.spl:5` | `BlockDevice` (library-side, used by FAT32) | sector I/O for hosted/mock devices |

### 1.2 Concrete impls

| File:line | Impl | Notes |
|---|---|---|
| `src/os/drivers/nvme/nvme_block_device.spl:25` | `impl BlockDevice for NvmeDriver` | spin-poll completion |
| `src/os/drivers/nvme/nvme_block_device.spl:48` | `impl AsyncBlockDevice for NvmeDriver` | notification-based; uses `SharedDmaBuffer` |
| `src/os/drivers/virtio/virtio_blk.spl:863` | `impl BlockDevice for VirtioBlkDriver` | QEMU virtio path |
| `src/lib/nogc_sync_mut/fs_driver/fat32_core.spl:46` | `Fat32Core.new(device: BlockDevice)` | hosted FAT32 takes any `BlockDevice` |

### 1.3 NVMe submission/completion path (Research 04 confirmation)

`src/os/drivers/nvme/`:
- `nvme_driver.spl` — 8-step init (BAR0 map / CAP / disable / DMA alloc / AQA+ASQ+ACQ / enable / Identify / I/O queue create). Uses syscalls 83 (MapBar), 84 (AllocDma), 26 (NotificationWait).
- `nvme_queue.spl` — `NvmeQueuePair`; real SQE submission via `submit_command`, phase-bit tracking, doorbell writes.
- `nvme_block_device.spl` — sync + async + `SharedDmaBuffer` (DMA-direct) paths.

This is the production hardware path. Research 04 rates it **HIGH** maturity.

### 1.4 Where DBFS *would* plug in (designed, not built)

Per Phase 3 architecture and Research 04:
> "DBFS can: (1) receive a `BlockDevice` implementor at mount time, (2) wrap it in a `RawNvmeArena` that implements the `Arena` trait, (3) mount at `/data` via `MountTable.mount("/data", DriverInstance.DbFs(DbFsDriver.new(arena)), opts)`."

**Audit reality:** the constructor that takes a `BlockDevice` does not exist (see §2.1).

---

## 2. Direct-access preservation — per-driver evidence

Verification grep over the DBFS source tree:
```
grep -rn -E "BlockDevice|block_device|nvme|virtio|pci|bar0|dma|irq|read_sector|write_sector" \
  src/lib/nogc_sync_mut/db/
→ (no matches)
```
DBFS has **zero** lexical reference to any HW driver, bus, IRQ, or DMA primitive. Every preservation claim below rides on this single, strong fact.

### 2.1 NVMe — **PROVEN reachable, unmodified**
- DBFS does not import `os.drivers.nvme.*`.
- `NvmeDriver` continues to implement both `BlockDevice` and `AsyncBlockDevice` (`nvme_block_device.spl:25,48`).
- VFS init path still: `vfs_init.spl` → `simpleos_nvme_init` (C bridge) → `Fat32` mounts at `/`. No DBFS step in this chain (Research 04, §"FAT32 Boot Path").
- **Caller demonstration:** `Fat32Core.new(BlockDevice)` (`fat32_core.spl:46`) accepts any `BlockDevice`; FAT32 in `src/os/kernel/fs/fat32.spl` reaches NVMe via the C bridge, not via DBFS.

### 2.2 PCI — **PROVEN reachable, unmodified**
- `src/os/drivers/pci/pci.spl` is the only file in the dir; DBFS never references it.
- `vfs_init.spl` runs PCI manager → NVMe init *before* any FS layer mounts (Research 04). DBFS comes online only at `MountTable.mount("/data", DriverInstance.DbFs(...), ...)` — strictly after PCI enumeration.

### 2.3 virtio — **PROVEN reachable, unmodified**
- `virtio_blk.spl`, `virtio_gpu.spl`, `virtio_net*.spl` all untouched by DBFS.
- `impl BlockDevice for VirtioBlkDriver` (`virtio_blk.spl:863`) intact — same trait FAT32 already consumes.
- Test `test/dbfs/fat32_no_regression_spec.spl:80–105` mounts `Fat32` (over a `MockFat32BlockDevice` implementing the same `BlockDevice` trait virtio uses) **alongside** DBFS in the same `MountTable` and exercises stat/opendir/readdir/open/read.

### 2.4 framebuffer — **PROVEN reachable, unmodified**
- `src/os/drivers/framebuffer/{bga_init.spl, fb_driver.spl}` — display path, not block layer. DBFS never references it. No block I/O surface to regress.

### 2.5 `null_block` — **GAP: driver does not exist in audited tree**
- AC-6 lists `null_block` explicitly. `find src/os/drivers -name 'null_block*'` returns **nothing**.
- All matches for `null_block*` are under `.claude/worktrees/agent-*` (orphaned worktree snapshots) or `examples/simple_os/src/drivers/null_block.spl` — not in the production driver tree on `main`.
- `grep -n null_block src/` (excluding worktrees) → only `src/compiler/10.frontend/parser_types.spl` (compiler token, not a driver).
- **Implication:** AC-6 references a driver that does not exist in the audited path scope. This is either (a) AC text drift (was planned, never landed) or (b) a deliberate forward reference. Either way, the claim "null_block driver remains reachable" is **vacuously true** because there is nothing to break.

### 2.6 Bypass path — **PROVEN**
- A FS that does not use DBFS reaches HW exactly as before:
  - `Fat32Core.new(BlockDevice)` (`src/lib/nogc_sync_mut/fs_driver/fat32_core.spl:46`) — accepts any `BlockDevice` impl, no DBFS interposition.
  - Kernel `src/os/kernel/fs/fat32.spl` — reaches NVMe via C-bridge externs (`simpleos_nvme_read_sector`, `simpleos_fat32_read_path`); DBFS never calls these.
  - `test/dbfs/nvfs_no_regression_spec.spl` exercises `NvfsDriver.open / write / read / stat` and `NvfsPosixDriver.{open,write,pread,pwrite,ftruncate}` directly — no DBFS in the call chain.
  - `test/dbfs/fat32_no_regression_spec.spl` mounts FAT32 against a `MockFat32BlockDevice` (raw `BlockDevice` trait impl) — proves the trait surface still accepts arbitrary block backends.

---

## 3. `DriverInstance` enum integrity

**File:** `src/lib/nogc_sync_mut/fs_driver/instance.spl` (168 lines).

### 3.1 Variant set (post-DBFS)
```
enum DriverInstance:                     # instance.spl:36
    Fat32(driver: FsFat32Driver)
    Nvfs(driver: NvfsDriver)
    NvfsPosix(driver: NvfsPosixDriver)
    RamFs(driver: RamFsDriver)
    DbFs(driver: DbFsDriver)             # added — instance.spl:54
```

### 3.2 Dispatch shape — **PRESERVED**
The other four variants retain their pre-existing `(driver: <Type>)` shape; `DbFs` follows the same shape. No variant was reordered, renamed, or had its payload changed.

### 3.3 Exhaustive matches — **all 5-arm**
Each `match self:` in `impl DriverInstance` lists arms in the same order: `Fat32 → Nvfs → NvfsPosix → RamFs → DbFs`. Methods covered (each line contains `case DbFs(d):`):
- `driver_name`        (instance.spl:64)
- `stat_path`          (instance.spl:73)
- `open_path`          (instance.spl:82)
- `opendir_path`       (instance.spl:91)
- `readdir_handle`     (instance.spl:100)
- `read_handle`        (instance.spl:109)
- (and the rest of the FS surface — pwrite, close, mkdir, unlink, rename, link — all extend through line 168).

The Simple compiler enforces exhaustive match; if a non-DBFS code path were missed it would not compile. Spec `mount_table_dbfs_dispatch_spec.spl` reports PASS in state.md, which is consistent with this.

### 3.4 No regression to other drivers
`Fat32(d): d.<op>` etc. still call the original concrete driver method. Adding the `DbFs` arm has zero effect on the codegen path for the other variants — variants are independent in a tagged-union match.

---

## 4. Driver-manifest registration — **terminology mismatch in AC-6**

### 4.1 Two unrelated "driver-manifest" concepts in the codebase

The grep `grep -rn driver_manifest` returns **only compiler-side hits**:
- `src/compiler/00.common/attributes.spl:115` — `enum DriverManifestAttrKind` (`Driver`, `NativeLib`)
- `src/compiler/00.common/attributes.spl:223` — `parse_driver_manifest_attrs(attrs) -> DriverManifestAttr?`
- `src/compiler/20.hir/hir_lowering/items.spl:401` — HIR lowering of `@driver_manifest` attributes
- `src/compiler/70.backend/linker/smf_writer.spl:215` — `add_driver_manifest_section(data: [u8])`

**This is a compile-time attribute system** that emits driver/native-lib metadata into SMF binaries. It is not a runtime FS-driver registration mechanism.

### 4.2 The actual runtime registration mechanism

The runtime "manifest" path that null_block, FAT32, RamFs, NVFS all share is:
1. The driver struct implements the `FsDriver` trait (`src/lib/nogc_sync_mut/fs_driver/ops.spl`).
2. A new variant is added to `DriverInstance` (`instance.spl`).
3. Mount happens via `MountTable.mount(path, DriverInstance.<Variant>(d), opts)` (`mount_table.spl:57`).
4. Lookup is a path-prefix match in `MountTable.lookup_text` → `MountTable.resolve_driver` (`mount_table.spl:142`).

DBFS uses **exactly this path** — see `dbfs_hw_passthrough_spec.spl:16–25`:
```
mt.mount("/data", DriverInstance.DbFs(dbfs), MountOptions.default()).unwrap()
```
identical in shape to the FAT32 mount one block above it (`mt.mount("/", DriverInstance.RamFs(ramfs), MountOptions.default())`).

### 4.3 Audit verdict

- **DBFS does** plug in via the same enum-variant-+-MountTable mechanism as every other FS driver. Same shape, same `mount_table.mount` entry point, same `block_device_for` resolver (`mount_table.spl:199`).
- **AC-6 wording** ("driver-manifest path") is misleading — there is no shared "manifest" registry; the unifying mechanism is the `DriverInstance` enum and `MountTable`. Recommend the AC be re-phrased to "the same `DriverInstance` + `MountTable.mount` path" before sign-off.
- **No null_block manifest entry exists** to compare against (driver doesn't exist).

---

## 5. AC-6 verification command sequence (for Phase 7)

These commands evidentially exercise the AC-6 surface as currently implemented. Run from repo root.

### 5.1 Static (grep / structural) checks — **fast, no build required**

```bash
# 5.1a  DBFS isolation from HW layer (must return nothing)
grep -rnE "BlockDevice|block_device|nvme|virtio|pci|bar0|dma|irq|read_sector|write_sector" \
  src/lib/nogc_sync_mut/db/

# 5.1b  Existing block-layer trait impls intact
grep -nE "impl (Async)?BlockDevice for (NvmeDriver|VirtioBlkDriver)" \
  src/os/drivers/nvme/nvme_block_device.spl \
  src/os/drivers/virtio/virtio_blk.spl

# 5.1c  Driver tree still has all four real drivers (null_block intentionally absent)
ls src/os/drivers/nvme/ src/os/drivers/virtio/ src/os/drivers/pci/ src/os/drivers/framebuffer/

# 5.1d  DriverInstance has 5 variants and DbFs is one of them
grep -nE "^    (Fat32|Nvfs|NvfsPosix|RamFs|DbFs)\(driver: " \
  src/lib/nogc_sync_mut/fs_driver/instance.spl

# 5.1e  Every match arm in instance.spl is 5-way
#       Expected: 5 × N, where N = # of dispatch methods in impl DriverInstance.
#       Sanity-check N first:
grep -cE "^    fn " src/lib/nogc_sync_mut/fs_driver/instance.spl     # → N
grep -cE "^            case (Fat32|Nvfs|NvfsPosix|RamFs|DbFs)\(d\):" \
  src/lib/nogc_sync_mut/fs_driver/instance.spl                       # → must equal 5 × N

# 5.1f  MountTable.block_device_for is the resolver used by the AC-6 spec
grep -n "fn block_device_for" src/lib/nogc_sync_mut/fs_driver/mount_table.spl
```

### 5.2 Spec runs — **interpreter mode** (per `feedback_compile_mode_false_greens` memory)

```bash
# 5.2a  AC-6 dedicated spec — proves mount dispatch isolation
bin/simple test test/dbfs/dbfs_hw_passthrough_spec.spl

# 5.2b  FAT32 still mounts and reaches its BlockDevice alongside DBFS
bin/simple test test/dbfs/fat32_no_regression_spec.spl

# 5.2c  NVFS native + Posix shim path unaffected by DBFS landing
bin/simple test test/dbfs/nvfs_no_regression_spec.spl

# 5.2d  Mount-table dispatch routes paths to DBFS without intercepting other drivers
bin/simple test test/dbfs/mount_table_dbfs_dispatch_spec.spl
```

State.md (Phase 5 spec results, 2026-04-28) reports 5.2a, 5.2c, 5.2d PASS; 5.2b 6/7 PASS with 1 BLOCKED on a parser issue (qualified path expression), unrelated to AC-6.

### 5.3 Coverage gap (must not be skipped at Phase 7)

```bash
# 5.3a  No DbFsDriver constructor takes a BlockDevice
grep -nE "static fn (new|open_on_device|new_with_device)" \
  src/lib/nogc_sync_mut/db/dbfs_driver/dbfs_driver.spl
# Expected current output: only `static fn new_hosted()` at line 131.
# Phase 4 prereq: `DbFsDriver.open_on_device(BlockDevice)` MUST exist for full AC-6.

# 5.3b  RawNvmeArena seam not yet on disk
find src/lib/nogc_sync_mut/db/dbfs_engine -name 'raw_nvme_arena*'
find src/lib/nogc_sync_mut/storage -name 'raw_nvme_arena*'
# Expected current output: nothing. Phase 5 prereq flagged this; not landed.
```

### 5.4 What `dbfs_hw_passthrough_spec.spl` actually proves vs. doesn't

Reading the spec literally (`test/dbfs/dbfs_hw_passthrough_spec.spl`):
- **Proves:** `MountTable.block_device_for("/etc/config")` returns `"RamFsDriver"` while `block_device_for("/data/hw_test.bin")` returns `"DbFsDriver"`. → Mount-table sibling isolation.
- **Proves:** Open succeeds on a path under the DBFS mount.
- **Does NOT prove:** any byte ever traverses a real `BlockDevice.read_sector` / `write_sector`. `block_device_for` (`mount_table.spl:199–207`) returns `entry.driver.driver_name()` — a **text tag**, not a device handle.
- **Does NOT prove:** DBFS would correctly forward a read down to an NVMe queue, because `DbFsDriver.new_hosted()` has no block backend.

Phase 7 should accept the spec **as evidence for mount dispatch isolation only**, and treat the wire-through to real HW as a follow-up (see §6 risk R2).

---

## 6. Risk callouts (places a future change could silently break AC-6)

### R1. A global lock / mutex on `MountTable.resolve` — *high*
`MountTable.resolve_driver(path)` (`mount_table.spl:142`) is on the hot path of every FS syscall. If someone wraps it in a global mutex (e.g. for snapshot-during-mount), DBFS's per-op resolution would serialize against unrelated FAT32/NVFS paths. **Guard:** assert `MountTable.resolve_driver` and `block_device_for` stay lock-free / per-mount-locked.

### R2. Adding a `BlockDevice` parameter to `DbFsDriver` later, but only to one constructor — *high*
Phase 4 prereqs listed `DbFsDriver.open_on_device(BlockDevice)`; it's not on disk. When it lands, if the existing `new_hosted()` is silently routed through it (e.g. by constructing a stub `BlockDevice`), DBFS in-memory tests will start hitting a code path that does real sector I/O. **Guard:** keep `new_hosted()` and `open_on_device(...)` lexically distinct; add a regression spec asserting `new_hosted()` doesn't reference any block-layer module.

### R3. Layering DBFS *under* FAT32 / NVFS as a "transparent" cache — *medium*
The architecture doc (and Research 02) places DBFS as a sibling FS variant. If a future commit adds DBFS as a backing layer for FAT32 (e.g. "FAT32 sees a DBFS-backed BlockDevice"), the sibling-mount isolation that AC-6 relies on dissolves and the bypass path no longer exists. **Guard:** assert `Fat32Core.new(BlockDevice)` callers in tests construct their `BlockDevice` from `RamBlockDevice` / `Mock*` / `NvmeDriver` — never from a `DbFs*` type.

### R4. Compile-mode false greens (per `feedback_compile_mode_false_greens` memory) — *medium*
`--mode=native` and `--mode=smf` swallow runtime errors and stub-generate around unresolved symbols. AC-6 verification must be in interpreter mode until R2-broader lands. **Guard:** Phase 7 sequence in §5.2 must not be re-run under `--mode=*` and reported as proof.

### R5. NVFS `BlobBackend` refactor (AC-4) bleeding into DBFS — *medium*
AC-4 will refactor NVFS arenas behind a `BlobBackend` trait. If `BlobBackend` is implemented over `BlockDevice` and DBFS later imports it (to ride raw NVMe blocks), DBFS gains a transitive dependency on the HW driver layer. **Guard:** when AC-4 lands, re-run §5.1a; if it returns matches, DBFS no longer enjoys clean isolation and AC-6's "no syscall-level block I/O regression" claim must be re-justified empirically (perf/latency benchmark, not just compile-clean).

### R6. `MountTable.write/pread/pwrite/close` routes everything to `self.mounts[0]` — *low (but real)*
`mount_table.spl:209+` shows: `self.mounts[0].driver.write_text_handle(handle, content)` for write/pread/pwrite/close. This is a known interpreter shortcut (DBFS-only fast path) and **bypasses** mount resolution for those four ops. If a non-DBFS test ever opens a handle through `MountTable.open` and then calls `MountTable.write`, it will get dispatched to whatever is at `mounts[0]` — not necessarily the FS that owns the handle. **Guard:** Phase 7 should add a spec asserting that with FAT32 mounted at `mounts[0]` and DBFS at `mounts[1]`, writing through a DBFS handle either succeeds or returns a clean error — never silently writes to FAT32. (This is a `MountTable` correctness gap that AC-6 currently does not catch.)

---

## 7. Authoritative file/line index

```
src/lib/nogc_sync_mut/fs_driver/instance.spl          (168 lines)
  :36   enum DriverInstance:
  :54   DbFs(driver: DbFsDriver)
  :64   case DbFs(d):    d.name              # driver_name
  :73   case DbFs(d):    d.stat_path(path)
  :82   case DbFs(d):    d.open_path(path, flags)
  :91   case DbFs(d):    d.opendir_path(path)
  :100  case DbFs(d):    d.readdir_handle(handle)
  :109  case DbFs(d):    d.read_handle(handle, length)
  ...   (full surface continues to line 168)

src/lib/nogc_sync_mut/fs_driver/mount_table.spl
  :57   me fn mount(path: text, driver: DriverInstance, opts: MountOptions) -> Result<MountId, FsError>
  :142  fn resolve_driver(path: text) -> Result<DriverInstance, FsError>
  :199  fn block_device_for(path: text) -> Result<text, FsError>      # used by AC-6 spec; returns driver_name() text

src/lib/nogc_sync_mut/db/dbfs_driver/dbfs_driver.spl
  :7    "Maps to: AC-1, AC-2, AC-6, AC-9, D1."
  :131  static fn new_hosted() -> DbFsDriver:                          # ← only constructor; no BlockDevice param

src/os/drivers/nvme/block_device.spl
  :14   trait BlockDevice
  :29   trait AsyncBlockDevice

src/os/drivers/nvme/nvme_block_device.spl
  :25   impl BlockDevice for NvmeDriver
  :48   impl AsyncBlockDevice for NvmeDriver

src/os/drivers/virtio/virtio_blk.spl
  :863  impl BlockDevice for VirtioBlkDriver

src/os/drivers/pci/pci.spl                                              # untouched
src/os/drivers/framebuffer/{bga_init.spl, fb_driver.spl}                # untouched
src/os/kernel/fs/fat32.spl                                              # boot path; DBFS-free
src/os/kernel/boot/, src/os/kernel/memory/                              # outside DBFS scope; untouched

src/lib/nogc_sync_mut/storage/                                          # arena.spl, capability.spl, durability.spl, mdsoc_base.spl, storage_class.spl
                                                                         # raw_nvme_arena.spl ABSENT
src/lib/nogc_sync_mut/db/dbfs_engine/                                   # checkpoint*, intent_log, ns_btree, pager, recovery, schema, txn, wal
                                                                         # raw_nvme_arena.spl ABSENT

test/dbfs/dbfs_hw_passthrough_spec.spl                                  # AC-6 spec — see §5.4
test/dbfs/fat32_no_regression_spec.spl                                  # AC-7 + AC-6 cross-coverage
test/dbfs/nvfs_no_regression_spec.spl                                   # AC-4 + AC-6 cross-coverage
test/dbfs/mount_table_dbfs_dispatch_spec.spl                            # mount routing
```

---

## 8. Summary for Phase 7 sign-off

| Reviewer question | Evidence |
|---|---|
| Did adding DBFS break any existing driver? | No — DBFS source has zero block-layer references (§2 grep). |
| Does DBFS reach hardware? | Not yet — only `new_hosted()` exists. The seam is designed (Research 04) and prereq'd (Phase 4 list) but not built. |
| Is `DriverInstance` dispatch still exhaustive and correct? | Yes — `instance.spl` lines 36–168 show 5 variants, every match is 5-arm. |
| Is the AC-6 spec strong enough to sign off? | Only for the mount-dispatch half. The "raw block access" half is proven by isolation, not by wire-through. |
| What changes would break this audit? | See §6 R1–R6. |

**Recommended Phase 7 disposition:** mark AC-6 *partially satisfied* — accept the dispatch-isolation evidence, note the missing `DbFsDriver.open_on_device(BlockDevice)` and `RawNvmeArena` as a tracked follow-up (carry forward into a `dbfs-block-backend` SStack feature), and re-phrase AC-6's "driver-manifest path" wording to "DriverInstance + MountTable" before checking the box.

---

*End of AC-6 audit.*
