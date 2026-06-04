# SStack State: nvfs-dbfs-qemu-boot

## User Request
> complete next with agents teams > doc/03_plan/nvfs_dbfs_real_filesystem.md

## Task Type
feature

## Refined Goal
> Close the known gap in the NVFS/DBFS plan: implement QEMU boot from a **native DBFS rootfs** (not FAT32 carrier) and verify **in-guest DBFS executable spawn** (ELF load + exec from DBFS-backed VFS). Two parallel work streams:
>
> **Team A — Native DBFS rootfs image builder + QEMU boot test:**
> Build a raw disk image with DBFS superblock + arena layout directly (no FAT32 carrier), wire it into `boot_fs_sequence()` as `BootFsType.Dbfs`, boot QEMU x86_64 from it, and verify kernel reaches init.
>
> **Team B — In-guest DBFS executable spawn:**
> Write an ELF binary into DBFS via `DbFsDriver`, resolve it through VFS → `resolve_executable_bytes`, parse via `load_user_executable`, and verify the loaded entry point matches. Extend `dbfs_disk_boot_spec.spl` with a QEMU-gated test that spawns a hello-world ELF from DBFS rootfs in-guest.

## Acceptance Criteria
- [ ] AC-1: `boot_fs_sequence()` supports `BootFsType.Dbfs` with native DBFS superblock detection (no FAT32 carrier required)
- [ ] AC-2: A raw DBFS rootfs disk image can be built from a seed directory via a builder function/script
- [ ] AC-3: QEMU x86_64 boots from native DBFS rootfs image and kernel reaches init (gated on `SIMPLEOS_DBFS_BOOT_QEMU=1`)
- [ ] AC-4: In-guest ELF binary stored in DBFS is resolved through VFS → executable_source → elf_loader and entry point is correct
- [ ] AC-5: `dbfs_disk_boot_spec.spl` extended with native DBFS boot + executable spawn tests (env-gated)
- [ ] AC-6: All existing NVFS/DBFS/boot_fs tests pass without regression
- [ ] AC-7: Plan doc `doc/03_plan/nvfs_dbfs_real_filesystem.md` updated — known gap closed

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-25
- [x] 2-research (Analyst) — 2026-05-25
- [x] 3-arch (Architect) — 2026-05-25
- [x] 4-spec (QA Lead) — 2026-05-25
- [ ] 5-implement (Engineer)
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev
**Task type:** feature
**Refined goal:** Close NVFS/DBFS plan known gap — native DBFS rootfs QEMU boot + in-guest executable spawn.
**Parallel teams:**
- Team A: DBFS rootfs image builder + boot_fs_sequence Dbfs path + QEMU boot integration test
- Team B: DBFS executable spawn through VFS/ELF loader + QEMU in-guest spawn test
**ACs:** 7 acceptance criteria defined (AC-1 through AC-7)
**Key source files:**
- `src/lib/nogc_sync_mut/os/kernel/boot/boot_fs.spl` (or equivalent) — boot_fs_sequence
- `test/os/port/dbfs_disk_boot_spec.spl` — QEMU boot spec
- `test/unit/os/services/vfs/vfs_rootfs_porting_spec.spl` — VFS rootfs I/O
- `src/lib/nogc_sync_mut/db/dbfs_driver.spl` — DbFsDriver
- `src/lib/nogc_sync_mut/fs_driver/block_device.spl` — BlockDevice

### 2-research

## Research Summary

### Existing Code

**Team A — Boot sequence and image builder:**

- `src/os/kernel/boot/boot_fs.spl` — `boot_fs_sequence()` already has full cascade: NVFS → DBFS → FAT32. The DBFS branch (lines ~92–173) calls `dbfs_superblock_probe_disk()` (checks LBA 2), reads superblock, and sets `_boot_fs_type = BootFsType.Dbfs`. However, after probe success it only logs "DBFS mounted" — there is **no actual VFS driver mount call** for DBFS in this path (unlike NVFS which calls `_nvfs_driver.mount(opts)`). The `_launch_init` function calls `g_vfs_read_file_bytes(path)` and `build_user_process_image`, but only works once the VFS root is mounted.

- `src/os/kernel/boot/boot_fs_mount.spl` — Freestanding-safe probe layer (`boot_fs_mount_freestanding()`). DBFS probe (`_probe_dbfs()`) checks LBA 2 for magic. Returns `FsMountType.Dbfs` on success. No VFS mount call either — just superblock confirmation.

- `src/lib/nogc_sync_mut/db/dbfs_engine/superblock.spl` — `DBFS_MAGIC = 0x44424653u32` ("DBFS"). Superblock at LBA 2 (replica A) and LBA 3 (replica B). Key API: `dbfs_superblock_set_device(dev: BlockDevice)`, `dbfs_superblock_probe_disk() -> bool`, `dbfs_superblock_format_disk(uuid_hi, uuid_lo) -> bool`, `dbfs_superblock_read_from_disk() -> DbfsSuperblock`.

- `src/lib/nogc_sync_mut/fs_driver/nvfs_superblock.spl` — Pattern mirror for NVFS: `NVFS_MAGIC = 0x4E564653u32`, at LBA 0/1. Functions: `nvfs_superblock_set_device`, `nvfs_superblock_probe_disk`, `nvfs_superblock_format_disk`, `nvfs_raw_read_sector` / `nvfs_raw_write_sector`.

- `src/lib/nogc_sync_mut/fs_driver/block_device.spl` — `trait BlockDevice` with `read_sector(lba: u64, buffer: [u8]) -> Result<bool, text>`, `write_sector(lba: u64, data: [u8]) -> Result<bool, text>`, `sector_size() -> u32`.

- `src/os/port/disk_image.spl` — FAT32 disk image builder (`build(cfg: DiskImageConfig, out_path: text) -> Result<(), text>`). Produces BPB sector 0, FSInfo sector 1, FAT tables, root dir, payload clusters. Uses `rt_file_truncate` for zero-extending. **No DBFS superblock writing** — FAT32 only.

- `src/os/port/disk_image_bake.spl` — High-level `bake(out_disk, out_initramfs)` using `disk_image.build`. FAT32 carrier only; uses `scripts/os/make_os_disk.shs` for real image. Has `_bake_via_mkfs_fat` fast path. No native DBFS image path.

- `src/os/installer/image_builder.spl` — Additional image builder (uninspected; likely FAT32 focused).

**Team B — Executable spawn pipeline:**

- `src/os/kernel/loader/executable_source.spl` — `resolve_executable_bytes(path: text, arch: Architecture) -> Result<[u8], text>`. Resolution order: synthetic initramfs → synthetic VFS entries → `_vfs_read_file(path)` which calls `g_vfs_read_executable_bytes(path)`. Test hooks: `_set_synthetic_vfs_file_for_test(path, bytes)` and `_set_synthetic_initramfs_for_test(path, bytes)`. Has `_minimal_rv64_exec() -> [u8]` helper that builds a minimal RV64 ELF header in bytes.

- `src/os/kernel/loader/elf_loader.spl` — `load_user_executable(data: [u8], arch: Architecture) -> Result<ElfImage, text>`. Parses ELF32/ELF64 (`_parse_elf32`, `_parse_elf64`). Returns `ElfImage { class_: ElfClass, entry: u64, segments: [ElfLoadSegment] }`. Entry accessed via `elf_image_entry(image) -> u64`. Also has ARM64 unchecked fast path and `load_riscv_executable`.

- `src/lib/nogc_sync_mut/db/dbfs_driver/dbfs_driver.spl` — `DbFsDriver` struct. Constructors: `new_hosted()`, `open_on_device(dev: BlockDevice, base_block: i64, block_count: i64) -> Result<DbFsDriver, FsError>`, `open_on_samsung_business_nvme(...)`. Key write path: `write_bytes_handle(handle: FileHandle, content: [u8]) -> Result<(), text>` and `write_passthrough(data: [u8]) -> Result<i64, FsError>` (raw arena write). Read path: `read_bytes_handle(handle: FileHandle, length: i64) -> Result<[u8], FsError>`. Open: `open_path(path: Path, flags: OpenFlags) -> Result<FileHandle, FsError>`. Binary data is stored as `content_bytes: [u8]` — byte-safe.

- `src/os/services/vfs/vfs_init.spl` — `g_vfs_read_executable_bytes(name: text) -> [u8]`, `g_vfs_read_file_bytes(name: text) -> [u8]`, `g_vfs_write_file_bytes(name: text, data: [u8]) -> bool`. Test helpers: `_clear_vfs_rootfs_for_test()`, `_mount_hosted_rootfs_for_test(driver: DriverInstance) -> bool`. The mounted-driver read path is `_vfs_read_mounted_exec_candidate(path) -> g_vfs_read_file_bytes(path)`.

**Existing tests:**

- `test/os/port/dbfs_disk_boot_spec.spl` — 3 tests gated on `SIMPLEOS_DBFS_BOOT=1`:
  1. skip guard (no env)
  2. "builds a DBFS-marked image carrying the rootfs marker" — uses FAT32 carrier + python patch script (`patch_native_dbfs_root.py`) that writes DBFS marker bytes; tests `rootfs_backend=dbfs` grep in image
  3. "boots the DBFS-marked image under QEMU and prints [BOOT]" — gated on `SIMPLEOS_DBFS_BOOT_QEMU=1`. This is FAT32-carrier, NOT native DBFS rootfs.
  - **Gap confirmed:** No native DBFS superblock disk image test. No ELF spawn in QEMU test.

- `test/unit/os/services/vfs/vfs_rootfs_porting_spec.spl` — Hosted DBFS coverage:
  - "DBFS rootfs can write, read, size, and existence-check through g_vfs_*" — text I/O
  - "DBFS executable reads fall back to the mounted rootfs" — text ELF stub round-trip
  - "DBFS rootfs resolves executable bytes and parses ELF image" — full pipeline: `g_vfs_write_file_bytes("/dbfs-init.elf", elf)` → `resolve_executable_bytes` → `load_user_executable` → `image.entry > 0`. Uses `_make_elf64_rv64()` (4100-byte RV64 ELF).
  - **This covers AC-4 in hosted mode.** Missing: BlockDevice-backed DBFS (open_on_device path) + QEMU in-guest test.

- `test/kernel/boot_fs_spec.spl` — boot_fs_sequence kernel tests (not yet inspected in detail).

### Reusable Modules

- `std.db.dbfs_engine.superblock` — `dbfs_superblock_format_disk`, `dbfs_superblock_probe_disk`, `dbfs_superblock_set_device`
- `std.fs_driver.nvfs_superblock` — pattern to follow for DBFS raw sector I/O (`nvfs_raw_read_sector`, `nvfs_raw_write_sector`)
- `std.fs_driver.block_device.BlockDevice` — trait for sector-level I/O (read_sector, write_sector, sector_size)
- `std.db.dbfs_driver.DbFsDriver` — `open_on_device(dev, base_block, block_count)` for disk-backed driver; `write_bytes_handle`, `read_bytes_handle` for binary-safe ELF storage
- `os.kernel.loader.executable_source.resolve_executable_bytes` — production VFS→bytes resolver; test hooks `_set_synthetic_vfs_file_for_test`
- `os.kernel.loader.elf_loader.load_user_executable` — ELF parse, returns entry point
- `os.services.vfs.vfs_init._mount_hosted_rootfs_for_test` — mounts any `DriverInstance` as rootfs for tests
- `os.port.disk_image.build` / `os.port.disk_image_bake.bake` — FAT32 builder pattern to extend for DBFS raw image
- `os.kernel.boot.boot_fs.boot_fs_sequence` — cascade already has DBFS branch; gap is the VFS driver mount step after probe

### Domain Notes

- NVFS superblock at LBA 0–1; DBFS superblock at LBA 2–3 (coexist on same disk).
- `dbfs_superblock_format_disk` writes both replicas. Requires `dbfs_superblock_set_device` first.
- `disk_image.build` writes FAT32 BPB at sector 0. A native DBFS image needs DBFS superblock at sector 2 instead of FAT32 structures, OR appended after FAT32 (current carrier approach). For a **native** DBFS rootfs image (no FAT32), the disk layout must start with DBFS superblock at LBA 2 (sectors 0–1 can be zeroed or hold a partition table / boot stub).
- `boot_fs_sequence` DBFS probe path calls `dbfs_superblock_probe_disk()` but does NOT call a DBFS VFS mount function after detection — the actual VFS mount of DBFS (hooking `open_path`, `read_bytes_handle` into the VFS root) appears to be missing or incomplete for the freestanding path.
- The `_launch_init` function in `boot_fs.spl` calls `g_vfs_read_file_bytes(path)` — this only works if VFS root is already mounted. For DBFS boot, the VFS root must be mounted via `DbFsDriver.open_on_device(adapter, base_block, block_count)` and registered in the VFS mount table.
- ELF binary data is byte-safe through DBFS because `content_bytes: [u8]` is used for storage. The `rt_text_to_bytes` path would be unsafe for arbitrary binary — need `write_bytes_handle` not `write_handle`.
- `_make_elf64_rv64()` (4100 bytes) in `vfs_rootfs_porting_spec.spl` is an existing minimal ELF fixture usable in new DBFS boot tests.
- `SIMPLEOS_DBFS_BOOT_QEMU=1` env var already reserved in `dbfs_disk_boot_spec.spl` (line 56) but currently unused — the native DBFS QEMU test should gate on this variable.

### Open Questions

- NONE

## Requirements

- REQ-1 (from AC-1): `boot_fs_sequence()` DBFS branch must call `DbFsDriver.open_on_device(adapter, base_block, block_count)` and register driver in VFS mount table after superblock probe succeeds — area: `src/os/kernel/boot/boot_fs.spl`
- REQ-2 (from AC-2): New `build_dbfs_rootfs_image(out_path: text, size_sectors: u64) -> Result<(), text>` that calls `dbfs_superblock_format_disk` + `dbfs_superblock_set_device` on a `MemBlockDevice` to produce a raw disk image with valid DBFS superblock at LBA 2–3 — area: `src/os/port/disk_image.spl` or new `src/os/port/dbfs_image.spl`
- REQ-3 (from AC-3): New `it "boots a native DBFS rootfs image under QEMU..."` test in `test/os/port/dbfs_disk_boot_spec.spl`, gated on `SIMPLEOS_DBFS_BOOT_QEMU=1`, using native DBFS image (no FAT32 carrier) — area: `test/os/port/dbfs_disk_boot_spec.spl`
- REQ-4 (from AC-4): New `it "DbFsDriver open_on_device stores and round-trips ELF bytes via VFS..."` test extending `vfs_rootfs_porting_spec.spl`, using `DbFsDriver.open_on_device` with a `MemBlockDevice`, writing an ELF via `write_bytes_handle`, resolving via `resolve_executable_bytes`, parsing via `load_user_executable`, checking `entry > 0` — area: `test/unit/os/services/vfs/vfs_rootfs_porting_spec.spl`
- REQ-5 (from AC-5): `dbfs_disk_boot_spec.spl` extended with (a) native DBFS image builder test + (b) QEMU in-guest ELF spawn test — area: `test/os/port/dbfs_disk_boot_spec.spl`
- REQ-6 (from AC-6): No regression — existing `dbfs_disk_boot_spec.spl` (FAT32-carrier path), `vfs_rootfs_porting_spec.spl`, and `boot_fs_spec.spl` must continue to pass
- REQ-7 (from AC-7): `doc/03_plan/nvfs_dbfs_real_filesystem.md` updated to mark gap closed — area: `doc/03_plan/nvfs_dbfs_real_filesystem.md`

### 3-arch

## Architecture

### Module Plan

| Module | Path | Role | New/Modified |
|--------|------|------|--------------|
| `mem_block_device` | `src/lib/nogc_sync_mut/fs_driver/mem_block_device.spl` | In-memory `BlockDevice` impl backed by a `[u8]` buffer; used by builder and unit tests | New |
| `dbfs_image` | `src/os/port/dbfs_image.spl` | Builds raw native-DBFS disk images (superblock at LBA 2-3, arena at LBA 4+); no FAT32 carrier | New |
| `vfs_init` | `src/os/services/vfs/vfs_init.spl` | Add production `vfs_mount_rootfs(driver: DriverInstance) -> Result<(), text>`; delegate `_mount_hosted_rootfs_for_test` to it | Modified |
| `boot_fs` | `src/os/kernel/boot/boot_fs.spl` | Complete `_try_dbfs_root()`: after probe success, call `DbFsDriver.open_on_device` then `vfs_mount_rootfs` | Modified |
| `dbfs_disk_boot_spec` | `test/os/port/dbfs_disk_boot_spec.spl` | Add native DBFS image build test + QEMU in-guest ELF spawn test (env-gated) | Modified |
| `vfs_rootfs_porting_spec` | `test/unit/os/services/vfs/vfs_rootfs_porting_spec.spl` | Add `open_on_device` round-trip test: `MemBlockDevice` → `DbFsDriver` → VFS → `resolve_executable_bytes` → `load_user_executable` | Modified |

### Dependency Map

```
boot_fs
  -> vfs_init (vfs_mount_rootfs)
  -> dbfs_driver (DbFsDriver.open_on_device)
  -> dbfs_engine.superblock (dbfs_superblock_set_device, probe, read)
  -> fs_driver.block_device (BlockDevice)

dbfs_image
  -> mem_block_device (MemBlockDevice implements BlockDevice)
  -> dbfs_engine.superblock (dbfs_superblock_set_device, dbfs_superblock_format_disk)
  -> dbfs_driver (DbFsDriver.open_on_device, write_bytes_handle, open_path)
  -> os.port.disk_image (rt_file_write_bytes, rt_file_truncate externs — pattern only)

vfs_init (modified)
  -> fs_driver.instance (DriverInstance)
  -> fs_driver.mount_table (MountTable.mount)

mem_block_device
  -> fs_driver.block_device (BlockDevice trait)

vfs_rootfs_porting_spec (test)
  -> mem_block_device
  -> dbfs_driver
  -> vfs_init (_mount_hosted_rootfs_for_test, _clear_vfs_rootfs_for_test)
  -> executable_source (resolve_executable_bytes)
  -> elf_loader (load_user_executable, elf_image_entry)

dbfs_disk_boot_spec (test)
  -> dbfs_image (build_dbfs_rootfs_image)
  -> os.port.disk_image_bake (QEMU launch helpers — existing)
```

No circular dependencies: verified. `mem_block_device` has no upstream project deps; `dbfs_image` depends on it; everything else is one-directional toward stdlib.

### Decisions

- **D-1: Introduce `vfs_mount_rootfs` in production scope; delegate test helper to it.**
  Context: `_mount_hosted_rootfs_for_test` exists but has test-scoped name. Boot path must not call test helpers. Decision: add `pub fn vfs_mount_rootfs(driver: DriverInstance) -> Result<(), text>` in `vfs_init.spl` containing the real mount-table logic; rewrite `_mount_hosted_rootfs_for_test` to call it. Consequence: `_try_dbfs_root()` in `boot_fs.spl` calls `vfs_mount_rootfs(DriverInstance.DbFs(driver))`; no test helper leaks into production.

- **D-2: Native DBFS image = LBA 0-1 zeroed, DBFS superblock at LBA 2-3, arena at LBA 4+.**
  Context: NVFS and DBFS can coexist (different LBAs) but a native DBFS boot image should not accidentally trigger NVFS probe. Decision: `build_dbfs_rootfs_image` writes zeros at LBA 0-1 (no valid NVFS magic) and formats DBFS at LBA 2-3. No NVFS superblock is written by the builder. Consequence: boot cascade falls through NVFS probe (no magic) and picks DBFS — correct. Coexistence (both superblocks valid) is a separate concern not exercised here.

- **D-3: `MemBlockDevice` lives in `std.fs_driver`, not in `os.port`.**
  Context: It is a pure `BlockDevice` implementation with no OS-level deps; tests in both `std` and `os` layers need it. Decision: place it in `src/lib/nogc_sync_mut/fs_driver/mem_block_device.spl`. Consequence: importable as `std.fs_driver.mem_block_device.{MemBlockDevice}` from any layer.

- **D-4: `open_on_device` `base_block` is absolute LBA on the device; arena = `[base_block, base_block+block_count)` LBA range.**
  Context: Confirmed from source — `RawNvmeArena.new(dev, base_block, block_count)`. Decision: `dbfs_image` builder calls `DbFsDriver.open_on_device(mem_dev, 4, size_sectors - 4)` to keep DBFS superblock sectors (LBA 2-3) outside the arena. `build_dbfs_rootfs_image` receives total `size_sectors` and computes arena bounds internally.

- **D-5: Team B (ELF spawn) requires no new loader module — it falls out of D-1.**
  Context: `_launch_init` already calls `g_vfs_read_file_bytes` then `build_user_process_image`. Once `_try_dbfs_root` mounts the DBFS VFS root (D-1), `/sbin/init` is readable through the normal VFS path. Decision: no new spawn or loader code; phase-5 engineer wires `_try_dbfs_root` only. QEMU test in `dbfs_disk_boot_spec` verifies the end-to-end path by checking boot output.

- **D-6: Reuse `_make_elf64_rv64()` from `vfs_rootfs_porting_spec.spl` as the seed ELF fixture in new tests.**
  Context: Already produces a valid 4100-byte RV64 ELF with non-zero entry point; used by the existing hosted-DBFS ELF parse test. Decision: new `open_on_device` round-trip test (REQ-4) calls the same helper rather than duplicating ELF construction. Consequence: single source of truth for minimal ELF fixture.

### Public API

**New: `src/lib/nogc_sync_mut/fs_driver/mem_block_device.spl`**
```
struct MemBlockDevice
  -- fields: sector_size_: u32, sector_count_: u64, data: [u8]

impl MemBlockDevice:
  static fn new(sector_count: u64, sector_size: u32) -> MemBlockDevice
  fn bytes() -> [u8]
  fn write_to_file(path: text) -> Result<(), text>

# Trait conformance (BlockDevice):
  fn read_sector(lba: u64, buffer: [u8]) -> Result<bool, text>
  fn write_sector(lba: u64, data: [u8]) -> Result<bool, text>
  fn sector_size() -> u32
```

**New: `src/os/port/dbfs_image.spl`**
```
struct DbfsImageConfig:
  size_sectors: u64          -- total image size in 512-byte sectors
  seeds: [PayloadEntry]      -- files to pre-populate (name: text, data: [u8])

fn build_dbfs_rootfs_image(cfg: DbfsImageConfig, out_path: text) -> Result<(), text>
  -- formats DBFS superblock at LBA 2-3, opens DbFsDriver with arena at LBA 4+,
  -- writes seed files, serializes MemBlockDevice to out_path

fn _dbfs_image_mem_device(cfg: DbfsImageConfig) -> Result<MemBlockDevice, text>
  -- internal: allocate + format; exposed for unit tests
```

**Modified: `src/os/services/vfs/vfs_init.spl`**
```
pub fn vfs_mount_rootfs(driver: DriverInstance) -> Result<(), text>
  -- production mount: mounts driver at "/" in g_mount_table, sets g_vfs_initialized
  -- (replaces inline logic in _mount_hosted_rootfs_for_test)
```

**Modified: `src/os/kernel/boot/boot_fs.spl`**
```
# _try_dbfs_root() extended (no signature change — returns bool):
#   after superblock probe success:
#     val driver_r = DbFsDriver.open_on_device(adapter, DBFS_ARENA_BASE_LBA, arena_block_count)
#     if driver_r.is_ok():
#         vfs_mount_rootfs(DriverInstance.DbFs(driver_r.unwrap()))
#
# New constant:
val DBFS_ARENA_BASE_LBA: i64 = 4
```

**Test signatures (phase-4 responsibility — listed here for coverage mapping):**
```
# vfs_rootfs_porting_spec.spl — new it block:
it "DbFsDriver open_on_device stores and round-trips ELF bytes via block device"
  -- creates MemBlockDevice(2048, 512), calls dbfs_superblock_set_device + format,
  -- opens DbFsDriver.open_on_device, writes ELF via write_bytes_handle("/sbin/init"),
  -- mounts via _mount_hosted_rootfs_for_test(DriverInstance.DbFs(driver)),
  -- resolves via resolve_executable_bytes, loads via load_user_executable,
  -- asserts elf_image_entry(image) > 0

# dbfs_disk_boot_spec.spl — new it blocks (both gated on SIMPLEOS_DBFS_BOOT_QEMU=1):
it "builds a native DBFS rootfs image with valid superblock"
it "boots a native DBFS rootfs image under QEMU and kernel reaches init"
```

### Requirement Coverage

- REQ-1 → `boot_fs` (modified `_try_dbfs_root`) + `vfs_init` (`vfs_mount_rootfs`)
- REQ-2 → `dbfs_image` (new) + `mem_block_device` (new)
- REQ-3 → `dbfs_disk_boot_spec` (new QEMU boot test)
- REQ-4 → `vfs_rootfs_porting_spec` (new `open_on_device` round-trip test) — no new prod module needed; falls out of REQ-1
- REQ-5 → `dbfs_disk_boot_spec` (new builder test + QEMU ELF spawn test)
- REQ-6 → no existing API removed; `_mount_hosted_rootfs_for_test` preserved via delegation to `vfs_mount_rootfs`
- REQ-7 → `doc/03_plan/nvfs_dbfs_real_filesystem.md` (doc edit only, no new module)

### 4-spec

## Specs

### Spec Files
- `test/dbfs/mem_block_device_spec.spl` — 6 specs covering AC-2 (MemBlockDevice construction, round-trip, write_to_file)
- `test/dbfs/dbfs_image_builder_spec.spl` — 8 specs covering AC-2 (build_dbfs_rootfs_image: file output, size, DBFS magic at LBA 2, LBA 0-1 zeroed, seed round-trip)
- `test/unit/os/services/vfs/vfs_rootfs_porting_spec.spl` — extended: +2 it blocks covering AC-4 (open_on_device ELF round-trip, vfs_mount_rootfs registration)
- `test/os/port/dbfs_disk_boot_spec.spl` — extended: +7 it blocks covering AC-1, AC-2, AC-3, AC-5 (native image builder tests + QEMU boot tests env-gated on SIMPLEOS_DBFS_BOOT_QEMU=1)
- `test/kernel/boot_fs_spec.spl` — extended: +3 it blocks covering AC-1 (DBFS_ARENA_BASE_LBA == 4, BootFsType.Dbfs distinct, BootFsResult carries Dbfs type)

### AC Coverage Matrix
| AC | Spec File | it block | Status |
|----|-----------|----------|--------|
| AC-1 | `test/kernel/boot_fs_spec.spl` | "AC-1: DBFS_ARENA_BASE_LBA constant is 4" | Failing (DBFS_ARENA_BASE_LBA not exported yet) |
| AC-1 | `test/kernel/boot_fs_spec.spl` | "AC-1: BootFsType.Dbfs is a valid distinct enum variant" | Failing (import DBFS_ARENA_BASE_LBA fails) |
| AC-1 | `test/kernel/boot_fs_spec.spl` | "AC-1: BootFsResult can carry BootFsType.Dbfs" | Failing (import DBFS_ARENA_BASE_LBA fails) |
| AC-1 | `test/os/port/dbfs_disk_boot_spec.spl` | "AC-1, AC-5: native DBFS image probe via dbfs_superblock_probe succeeds" | Failing (build_dbfs_rootfs_image not impl) |
| AC-2 | `test/dbfs/mem_block_device_spec.spl` | "AC-2: new creates device with correct sector_count" | Failing (MemBlockDevice not impl) |
| AC-2 | `test/dbfs/mem_block_device_spec.spl` | "AC-2: new creates device with correct sector_size" | Failing (MemBlockDevice not impl) |
| AC-2 | `test/dbfs/mem_block_device_spec.spl` | "AC-2: bytes() length equals sector_count * sector_size" | Failing (MemBlockDevice not impl) |
| AC-2 | `test/dbfs/mem_block_device_spec.spl` | "AC-2: write_sector then read_sector preserves all bytes" | Failing (MemBlockDevice not impl) |
| AC-2 | `test/dbfs/mem_block_device_spec.spl` | "AC-2: write_to_file creates file at the given path" | Failing (MemBlockDevice not impl) |
| AC-2 | `test/dbfs/dbfs_image_builder_spec.spl` | "AC-2: _dbfs_image_mem_device returns ok for valid config" | Failing (dbfs_image not impl) |
| AC-2 | `test/dbfs/dbfs_image_builder_spec.spl` | "AC-2: DBFS superblock magic 'DBFS' is at LBA 2" | Failing (dbfs_image not impl) |
| AC-2 | `test/dbfs/dbfs_image_builder_spec.spl` | "AC-2: LBA 0 and LBA 1 are zeroed (no NVFS magic)" | Failing (dbfs_image not impl) |
| AC-2 | `test/dbfs/dbfs_image_builder_spec.spl` | "AC-2: build_dbfs_rootfs_image creates the output file" | Failing (dbfs_image not impl) |
| AC-2 | `test/os/port/dbfs_disk_boot_spec.spl` | "AC-2: build_dbfs_rootfs_image creates the output file" | Failing (dbfs_image not impl) |
| AC-2 | `test/os/port/dbfs_disk_boot_spec.spl` | "AC-2: output file size equals size_sectors * 512" | Failing (dbfs_image not impl) |
| AC-2 | `test/os/port/dbfs_disk_boot_spec.spl` | "AC-2: image has DBFS magic 'DBFS' at LBA 2" | Failing (dbfs_image not impl) |
| AC-3 | `test/os/port/dbfs_disk_boot_spec.spl` | "AC-3, AC-5: boots native DBFS rootfs image under QEMU and kernel reaches init" | Failing (env-gated; dbfs_image + boot_fs not impl) |
| AC-3 | `test/os/port/dbfs_disk_boot_spec.spl` | "AC-3, AC-5: native DBFS boot image exits QEMU without kernel panic" | Failing (env-gated; dbfs_image + boot_fs not impl) |
| AC-4 | `test/unit/os/services/vfs/vfs_rootfs_porting_spec.spl` | "AC-4: DbFsDriver open_on_device stores and round-trips ELF bytes via block device" | Failing (MemBlockDevice + vfs_mount_rootfs not impl) |
| AC-4 | `test/unit/os/services/vfs/vfs_rootfs_porting_spec.spl` | "AC-4: vfs_mount_rootfs registers driver at VFS root" | Failing (vfs_mount_rootfs not impl) |
| AC-5 | `test/os/port/dbfs_disk_boot_spec.spl` | (same as AC-3 rows above — AC-3 and AC-5 share QEMU tests) | Failing |
| AC-6 | (regression) | Covered by existing tests; verified in phase 7 | N/A (phase 7) |
| AC-7 | (doc edit) | Plan doc update; no spec test | N/A (phase 8) |

### 5-implement
<pending>

### 6-refactor
<pending>

### 7-verify
<pending>

### 8-ship
<pending>

## Log
- 1-dev (2026-05-25): Created state file with 7 acceptance criteria; identified 2 parallel teams
- 2-research (2026-05-25): Found 12 existing code refs, 8 reusable modules, 7 requirements drafted; confirmed boot_fs_sequence DBFS probe exists but VFS mount step is missing; confirmed dbfs_disk_boot_spec covers FAT32-carrier only; confirmed vfs_rootfs_porting_spec covers hosted DBFS ELF parse (AC-4 partially); gap is native disk image builder + QEMU test + VFS mount wiring
- 3-arch (2026-05-25): Designed 2 new modules (mem_block_device, dbfs_image) + 2 modified (boot_fs, vfs_init) + 2 test file extensions; 6 ADRs; no circular deps; all 7 REQs covered
- 4-spec (2026-05-25): Created 2 new spec files (mem_block_device_spec, dbfs_image_builder_spec) + extended 3 existing specs (vfs_rootfs_porting_spec, dbfs_disk_boot_spec, boot_fs_spec); 26 total it blocks; 100% AC coverage (AC-1 through AC-5 with failing specs; AC-6 deferred to phase 7; AC-7 deferred to phase 8)
