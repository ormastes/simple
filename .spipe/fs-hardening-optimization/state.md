# SStack State: fs-hardening-optimization

## User Request
> harden file system and compare them with c counter part and improve simple optimization plugin and 3 file system itself and make faster than c, native file system. plan and improve simple file systems

## Task Type
feature

## Refined Goal
> Harden and optimize the three Simple file systems (FAT32, NVFS, RamFS) to outperform their C counterparts. This involves three workstreams:
>
> **W1 — FS Hardening:** Add bounds checking, input validation, error-path robustness, and corruption-recovery to FAT32Driver, NvfsDriver, and RamFsDriver. Audit every public FsDriver trait method for missing error cases (double-close, stale handle, overflow, bad offset, path traversal).
>
> **W2 — Optimization Plugin Enhancement:** Extend the MIR optimization passes (`src/compiler/60.mir_opt/optimization_passes.spl`) with FS-aware optimizations: syscall batching, read-ahead hints, write coalescing, and hot-path inlining. Enhance the dynamic plugin manifest to support FS-specific pass plugins.
>
> **W3 — Performance Parity → Superiority vs C:** Benchmark all three FS implementations against C counterparts (Linux ext4/FAT32 via POSIX, C NVFS reference) using the existing bench harness (`test/dbfs/bench_harness.spl`). Identify bottlenecks via profiling, then apply targeted optimizations: zero-copy I/O paths, arena pre-allocation, extent-cache warming, and reduced allocation pressure. Target: match or beat C on all 4 bench workloads (metadata storm, append-heavy, random-overwrite, mmap read).

## Acceptance Criteria
- [ ] AC-1: FAT32Driver passes hardening audit — all public methods validate inputs, reject stale handles, and return typed FsError (no panics, no silent corruption)
- [ ] AC-2: NvfsDriver passes hardening audit — superblock magic validation, extent-map bounds checks, CoW atomicity on partial-write failure, checksum verification on read
- [ ] AC-3: RamFsDriver passes hardening audit — handle-lifetime tracking, OOM-safe allocation paths, concurrent-access guards
- [ ] AC-4: MIR optimization passes enhanced with at least 3 new FS-relevant optimizations (syscall batching, write coalescing, read-ahead hoisting) — verified by optimizer stats output
- [ ] AC-5: Dynamic optimizer manifest supports FS-specific pass plugins (new `PassScope.FsDriver` scope, capability-gated pass selection)
- [ ] AC-6: Benchmark comparison report: Simple vs C on all 4 workloads, with p50/p99 latency and throughput numbers
- [ ] AC-7: At least 2 of 4 bench workloads show Simple matching or beating C performance (within 10% or faster)
- [ ] AC-8: All existing fs_driver, nvfs, fat32, and dbfs tests pass after changes (zero regressions)
- [ ] AC-9: New hardening spec tests cover at least: double-close, stale-handle read/write, path-traversal rejection, corrupt-superblock mount

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-22
- [x] 2-research (Analyst) — 2026-05-22
- [x] 3-arch (Architect) — 2026-05-22
- [x] 4-spec (QA Lead) — 2026-05-23
- [ ] 5-implement (Engineer)
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev
**Task type:** feature
**Refined goal:** Harden + optimize 3 Simple file systems to outperform C counterparts.
**Three workstreams:** W1 (hardening), W2 (optimizer plugin), W3 (perf parity/superiority).
**9 acceptance criteria defined.**

Key files identified:
- FS drivers: `src/lib/nogc_sync_mut/fs_driver/` (fat32*.spl, nvfs_arena.spl, ramfs.spl, ops.spl, error.spl, capability.spl)
- NVFS core: `src/lib/nogc_sync_mut/fs/nvfs/` (api.spl, extent_map.spl, superblock_if.spl)
- NVFS POSIX: `src/lib/nogc_sync_mut/fs/nvfs_posix/` (api.spl, cow_engine.spl, fd_table.spl, posix_driver.spl)
- Optimizer: `src/compiler/60.mir_opt/optimization_passes.spl`, `optimizer_manifest.spl`
- Backend opts: `src/compiler/70.backend/backend/optimization_passes.spl`
- Bench: `test/dbfs/bench_harness.spl`
- Design docs: `doc/05_design/nvfs_design_v3.md`, `doc/05_design/fs_driver_interface.md`

### 2-research

#### Existing Code

**FAT32 Driver** (`src/os/services/fat32/fat32.spl`):
- `Fat32Driver` class with `open_files: [Fat32OpenFile]`, `next_handle: u64`, linear scan for handle lookup.
- No stale-handle guard: `close()` removes from list but no generation counter prevents reuse of handle IDs.
- No path-traversal rejection: `..` components in paths are not sanitized.
- No cluster-chain cycle detection: infinite loop possible on corrupt FAT.
- Hardening gaps: missing bounds check on `total_clusters` vs FAT table size, no validation of BPB fields on mount.

**NvfsDriver** (`src/lib/nogc_sync_mut/fs_driver/nvfs_driver.spl`):
- Thin wrapper around `DbFsDriver.new_hosted()` — delegates ALL ops to DbFsDriver.
- Real CoW engine + extent map live in `examples/nvfs/` submodule, not stdlib.
- Superblock impl in `src/lib/nogc_sync_mut/fs_driver/nvfs_superblock.spl`: dual-replica write, magic validation (`NVFS_MAGIC`), `_nvfs_checksum()` computation, `_nvfs_sb_from_bytes()` with length guard (`buf.len() < 54`).
- Hardening gaps: no checksum verification on read (only computed on write), no generation-mismatch detection between replicas, `nvfs_superblock_read_from_disk()` falls back silently on short read.

**RamFsDriver** (`src/lib/nogc_sync_mut/fs_driver/ramfs.spl`):
- Fields: `inodes: [InodeEntry]`, `fd_table: [FdEntry]`, `next_ino: u64`, `next_fd: u64`.
- All lookups are linear scan (`find_inode_idx`, `for ent in d.entries`).
- No OOM guard: `alloc_ino()` increments without overflow check on u64.
- No concurrent-access guards (single-threaded assumption, no mutex).
- No double-close detection: closing an already-closed fd silently succeeds or panics depending on fd_table state.

**DbFsDriver** (`src/lib/nogc_sync_mut/db/dbfs_driver/dbfs_driver.spl`):
- Module-level stores (`_dbfs_inodes`, `_dbfs_fds`) keyed by `inst_id`.
- Has `closed: bool` on fd entries — partial stale-handle guard exists here but not in Fat32/RamFS.
- WAL group-commit via `DbfsWal`.

**FsDriver trait** (`src/lib/nogc_sync_mut/fs_driver/ops.spl`):
- All ops return `Result<T, FsError>`. FsError has 15 variants mapping to POSIX errno.
- Dispatch via `DriverInstance` enum match — no dyn, no vtable.
- Capability/Extension probe system in `capability.spl` + `extension.spl`.

**Optimization Passes** (`src/compiler/60.mir_opt/optimization_passes.spl`):
- Current passes: constant folding/propagation, strength reduction, algebraic simplification, CSE, dead code elimination, peephole, cast optimization.
- No FS-aware passes exist today.
- `OptimizationStats` tracks per-pass counts.

**Optimizer Manifest** (`src/compiler/60.mir_opt/optimizer_manifest.spl`):
- `DynamicPassDescriptor` with `scope: PassScope`, `capability_requires: [text]`.
- `DynamicPassRegistry` for session-scoped plugin registration.
- Built-in name conflict guard prevents shadowing.
- `ManifestPassEntry` + `ManifestPassContract` define per-pass I/O + purity.
- Dynamic passes dispatched after built-in PassKind match in `run_pass_on_module`.
- Extension point: add `PassScope.FsDriver` variant to existing `PassScope` enum.

**Bench Harness** (`test/dbfs/bench_harness.spl`):
- 4 workloads: metadata_storm (1000 create/stat/rename/unlink), append_heavy_log (10MB 4KiB chunks), random_overwrite (64MB file, random 4KiB writes), mmap_read_mostly (16MB sequential reads).
- `BenchResult`: p50/p99 latency (us), bytes_written, logical_bytes, recovery_time, mount_time, rss_kib, cache_hit_ratio.
- Coverage gaps: FAT32 not benchmarked at all. RamFS only in metadata_storm. Random-overwrite only on DBFS.

**Direct I/O** (`src/lib/nogc_sync_mut/fs_driver/direct_io.spl`):
- `DirectIoRequest`/`DirectIoResult` with `SharedDmaBuffer` — zero-copy path already exists.
- DMA sync primitives available (`dma_shared_sync_cpu_to_device`, `dma_shared_sync_device_to_cpu`).

#### Reusable Modules
- `std.fs_driver.error.FsError` — typed error enum with POSIX errno mapping (15 variants)
- `std.fs_driver.capability.{Capability, CapabilitySet}` — 23-bit bitmask, probe/has API
- `std.fs_driver.extension.{Extension, DirectIoExt}` — zero-copy DMA extension
- `std.fs_driver.block_device.BlockDevice` — `read_sector`/`write_sector` trait
- `std.fs_driver.direct_io` — `DirectIoRequest`, `SharedDmaBuffer`, DMA sync
- `std.db.dbfs_engine.wal.DbfsWal` — write-ahead log with group-commit
- `std.db.dbfs_engine.raw_nvme_arena.RawNvmeArena` — device-backed arena
- `std.storage.nvme_feature_policy` — Samsung NVMe policy hooks (`nvme_policy_for_class`)
- `_nvfs_checksum()` in `nvfs_superblock.spl` — dual-replica superblock pattern
- `NvfsArena` module-level store — arena alloc/seal/discard/read/write with NVMe backend

#### Constraints
- **C boundary is minimal:** only 4 `rt_*` externs across all FS code (`rt_bytes_alloc`, `rt_text_to_bytes`, `rt_socket_set_nonblocking`). "vs C" comparison (AC-6/AC-7) must use Linux POSIX syscalls on ext4/FAT32 as the C baseline, not internal externs.
- **NvfsDriver delegates to DbFsDriver:** real CoW/extent-map lives in `examples/nvfs/` submodule. Hardening AC-2 scope limited to stdlib superblock + DbFsDriver layer unless examples/ is pulled in.
- **text-typed API byte corruption:** `NvfsDriver.write_handle(handle, content: text)` uses `rt_text_to_bytes` which goes through `String::from_utf8_lossy` — silently corrupts arbitrary bytes (known issue, memory note `feedback_text_only_byte_cliffs.md`).
- **Bench harness incomplete for ACs:** FAT32 absent from all workloads; must extend harness before AC-6/AC-7 claims.

#### Risks
- **Interpreter false-greens:** `--mode=native` and `--mode=smf` may report PASSED for tests that actually fail at runtime. Verify hardening specs in interpreter mode (memory note `feedback_compile_mode_false_greens.md`).
- **it-block var mutation lost:** while-loop iterations inside spipe `it` blocks lose `var` rebindings under interpreter. Use module-level `fn` helpers for stateful test logic (memory note `feedback_it_block_var_mutation.md`).
- **RamFS linear scan perf:** `find_inode_idx` is O(n) — metadata_storm with 1000+ inodes will show poor p99. Needs hash-map or indexed lookup for AC-7.
- **PassScope enum location unknown:** `PassScope` is used in `optimizer_manifest.spl` but enum definition not found in searched files. Architect must locate before adding `FsDriver` variant.

#### Open Questions
- NONE (all resolved or surfaced as constraints/risks above)

#### Requirements
- REQ-1 (AC-1): Add input validation, stale-handle generation counter, path-traversal rejection, cluster-chain cycle detection, BPB bounds checks to `Fat32Driver` — area: `src/os/services/fat32/fat32.spl`
- REQ-2 (AC-2): Add superblock checksum verification on read, replica generation-mismatch detection, short-read error return to `nvfs_superblock.spl`; scope CoW/extent-map hardening to DbFsDriver layer — area: `src/lib/nogc_sync_mut/fs_driver/nvfs_superblock.spl`, `src/lib/nogc_sync_mut/fs_driver/nvfs_driver.spl`
- REQ-3 (AC-3): Add handle-lifetime tracking (generation counter), OOM-safe allocation (overflow check on `next_ino`/`next_fd`), double-close detection to `RamFsDriver` — area: `src/lib/nogc_sync_mut/fs_driver/ramfs.spl`
- REQ-4 (AC-4): Add 3+ FS-relevant MIR passes (syscall batching, write coalescing, read-ahead hoisting) to optimization engine — area: `src/compiler/60.mir_opt/optimization_passes.spl`
- REQ-5 (AC-5): Add `PassScope.FsDriver` variant and capability-gated pass selection to dynamic manifest — area: `src/compiler/60.mir_opt/optimizer_manifest.spl`
- REQ-6 (AC-6): Extend bench harness with FAT32 + all-FS coverage for all 4 workloads; add C/POSIX baseline comparison — area: `test/dbfs/bench_harness.spl`
- REQ-7 (AC-7): Optimize RamFS linear scan, NvfsArena sector I/O, Fat32 cluster-chain walk for perf parity — area: per-driver files
- REQ-8 (AC-8): Run full existing test suite after changes — area: `test/`
- REQ-9 (AC-9): Write hardening spec tests for double-close, stale-handle, path-traversal, corrupt-superblock — area: `test/` (new spec files)

### 3-arch

## Architecture

### Decisions

- **D-1: FsError vocabulary — add 2 new variants.** Add `StaleHandle` and `PathTraversal` to FsError. `StaleHandle` maps to `EBADF` (9); `PathTraversal` maps to `EACCES` (13). Rationale: AC-9 requires testable distinct outcomes for stale-handle vs. bad-offset (`InvalidArg`) and for path-traversal vs. permission-denied (`Permission`). Propagation is limited: new FsError variants only affect code that pattern-matches on FsError (primarily `errno_of` in error.spl + caller error-handling code). DriverInstance dispatch is on driver type, not error type, so it is unaffected.

- **D-2: Handle generation encoding — high-32/low-32 packing.** `FileHandle.id` packs generation (bits 63..32) and slot index (bits 31..0). Each driver maintains a `[HandleSlot]` array; `HandleSlot.generation: u32` increments on close. On use, the driver unpacks the handle, bounds-checks the slot index, and compares generations. Mismatch returns `FsError.StaleHandle`. Rationale: single u64 comparison, no side-table, no ABI change to FileHandle.

- **D-3: RamFS lookup — sorted array + binary search.** No HashMap exists in stdlib. `[InodeEntry]` will be kept sorted by `id` field; `find_inode_idx` replaced with binary search (O(log n)). Insertion uses `insert_sorted`. Rationale: simplest delta, no new data structure needed, sufficient for 1000-file metadata_storm benchmark target.

- **D-4: NvfsDriver hardening boundary — stdlib only.** AC-2 scope is `nvfs_superblock.spl` (checksum-on-read, dual-replica gen check, short-read rejection) plus DbFsDriver layer (already has `closed: bool`; add generation check). `examples/nvfs/` submodule CoW/extent-map is out of scope.

- **D-5: MIR pass scope — pattern recognition + conservative transform.** The 3 new FS passes (syscall_batch, write_coalesce, read_ahead_hoist) recognize MIR patterns (adjacent `rt_*` calls with contiguous offsets) and emit stat counters. Actual transform is conservative (merge only when provably safe). Verified via `OptimizationStats` output. This avoids over-promising full syscall batching transforms.

- **D-6: C POSIX baseline — SFFI externs in bench harness.** Add `test/dbfs/posix_baseline.spl` with `rt_posix_*` externs (open/read/write/close/rename/unlink/stat) calling libc. Bench harness calls these alongside Simple drivers for comparison. No new runtime externs needed — reuse existing `rt_*` where available; add 4 thin SFFI wrappers for the missing POSIX verbs.

### Breaking Changes

- `nvfs_superblock_read_from_disk()` return type changes from `NvfsSuperblock` to `Result<NvfsSuperblock, FsError>`. All callers must be updated to handle the error case.
- `RamFsDriver.next_fd: u64` field is removed (replaced by `handle_slots: [HandleSlot]` length). Any test or code accessing `next_fd` directly must be updated.

### AC-7 Performance Strategy

Primary bet: RamFS `metadata_storm` — binary search replaces O(n) linear scan, directly measurable improvement.
Secondary bet: NVFS/DbFS `append_heavy_log` — DbFsDriver already has `io_unit_bytes` / `batch_bytes` tuning knobs (set by `nvme_policy_for_class`); bench harness will surface whether existing knobs already beat C POSIX baseline.
Implicit: MIR passes (syscall_batch, write_coalesce) improve compiled-mode drivers if rt_* call patterns are recognizable. Conservative — may not contribute to AC-7 in this iteration.

### Module Plan

| Module | Path | Role | New/Modified |
|--------|------|------|--------------|
| fs_error | `src/lib/nogc_sync_mut/fs_driver/error.spl` | Add `StaleHandle`, `PathTraversal` variants + errno mapping | Modified |
| handle_guard | `src/lib/nogc_sync_mut/fs_driver/handle_guard.spl` | HandleSlot struct, pack/unpack fns, generation validation | New |
| ramfs_hardened | `src/lib/nogc_sync_mut/fs_driver/ramfs.spl` | Generation counter, sorted-array lookup, overflow guard, double-close detection, path-traversal rejection | Modified |
| fat32_hardened | `src/os/services/fat32/fat32.spl` | BPB field validation, cluster-chain cycle detection | Modified |
| fat32_stub_hardened | `src/lib/nogc_sync_mut/fs_driver/fat32_stub.spl` | Handle generation guard, path-traversal sanitization (wrapper layer) | Modified |
| nvfs_superblock_hardened | `src/lib/nogc_sync_mut/fs_driver/nvfs_superblock.spl` | Checksum verification on read, short-read rejection, replica gen mismatch | Modified |
| nvfs_driver_hardened | `src/lib/nogc_sync_mut/fs_driver/nvfs_driver.spl` | Delegate hardening to DbFsDriver gen-check layer | Modified |
| dbfs_driver_hardened | `src/lib/nogc_sync_mut/db/dbfs_driver/dbfs_driver.spl` | Generation counter on DbFsFd, stale-handle check on all ops | Modified |
| pass_scope_ext | `src/compiler/60.mir_opt/mir_opt/mod.spl` | Add `PassScope.FsDriver` variant | Modified |
| fs_mir_passes | `src/compiler/60.mir_opt/optimization_passes.spl` | Add 3 FS-aware MIR passes: syscall_batch, write_coalesce, read_ahead_hoist | Modified |
| manifest_fs | `src/compiler/60.mir_opt/optimizer_manifest.spl` | Wire `PassScope.FsDriver` in ManifestPassEntry; capability-gated pass selection via existing `capability_requires` field | Modified |
| bench_fat32 | `test/dbfs/bench_harness.spl` | Add FAT32 + complete RamFS coverage for all 4 workloads | Modified |
| posix_baseline | `test/dbfs/posix_baseline.spl` | C POSIX baseline runner via SFFI externs | New |
| hardening_spec | `test/dbfs/fs_hardening_spec.spl` | Spec tests: double-close, stale-handle, path-traversal, corrupt-superblock | New |

### Dependency Map

- `handle_guard` -> `std.fs_driver.types` (uses FileHandle, DirHandle)
- `ramfs` -> `handle_guard` (uses HandleSlot, pack/unpack)
- `ramfs` -> `error` (uses FsError.StaleHandle, FsError.PathTraversal)
- `fat32_stub` -> `handle_guard` (uses HandleSlot, pack/unpack)
- `fat32_stub` -> `error` (uses FsError.StaleHandle, FsError.PathTraversal)
- `fat32.spl` -> `error` (uses FsError.Corrupt for BPB/cycle detection)
- `nvfs_superblock` -> `error` (uses FsError.Corrupt for checksum mismatch)
- `nvfs_driver` -> `dbfs_driver` (delegates; unchanged dependency)
- `dbfs_driver` -> `handle_guard` (uses HandleSlot)
- `dbfs_driver` -> `error` (uses FsError.StaleHandle)
- `fs_mir_passes` -> `optimization_passes` types (MirFunction, MirModule, OptimizationStats)
- `manifest_fs` -> `pass_scope_ext` (uses PassScope.FsDriver)
- `posix_baseline` -> SFFI externs (rt_posix_open, rt_posix_read, rt_posix_write, rt_posix_close)
- `bench_harness` -> `posix_baseline` (calls C baseline workloads)
- `hardening_spec` -> `ramfs`, `fat32_stub`, `nvfs_superblock`, `error`
- No circular dependencies: verified (DAG flows: types <- guard <- drivers <- tests; optimizer chain is independent)

### Public API

#### handle_guard.spl (New)
- `struct HandleSlot` — fields: `generation: u32`, `ino_id: u64`, `active: bool`
- `fn handle_pack(slot_idx: u32, generation: u32) -> u64` — pack into FileHandle.id
- `fn handle_unpack_slot(packed: u64) -> u32` — extract slot index
- `fn handle_unpack_gen(packed: u64) -> u32` — extract generation
- `fn handle_validate(slots: [HandleSlot], handle_id: u64) -> Result<u32, FsError>` — validate + return slot index or StaleHandle

#### error.spl (Modified — 2 new variants)
- `FsError.StaleHandle` — closed/reused handle detected via generation mismatch
- `FsError.PathTraversal` — path contains `..` or other traversal attempt
- `fn errno_of` — add: `case StaleHandle: EBADF`, `case PathTraversal: EACCES`

#### ramfs.spl (Modified — new fields + methods)
- `RamFsDriver` new fields: `handle_slots: [HandleSlot]`
- `RamFsDriver` removed fields: `next_fd: u64` (replaced by handle_slots length)
- `fn find_inode_idx(id: u64) -> i32` — rewritten as binary search
- `fn insert_inode_sorted(entry: InodeEntry)` — sorted insertion
- `fn sanitize_path(raw: text) -> Result<text, FsError>` — reject `..` components

#### fat32_stub.spl (Modified — new fields)
- `FsFat32Driver` new fields: `handle_slots: [HandleSlot]`

#### fat32.spl (Modified — new validation methods)
- `fn validate_bpb(bpb: Fat32Bpb) -> Result<(), text>` — BPB field range checks
- `fn detect_cluster_cycle(start: u32, max_steps: u32) -> Result<bool, text>` — tortoise-and-hare cycle detection on FAT chain

#### nvfs_superblock.spl (Modified — checksum on read)
- `fn nvfs_superblock_read_from_disk() -> NvfsSuperblock` — changed to `-> Result<NvfsSuperblock, FsError>`, adds checksum verification + short-read error

#### optimization_passes.spl (Modified — 3 new pass functions)
- `fn optimize_syscall_batch(func: MirFunction, stats: OptimizationStats) -> MirFunction` — merge adjacent rt_* calls with contiguous offsets
- `fn optimize_write_coalesce(func: MirFunction, stats: OptimizationStats) -> MirFunction` — merge sequential writes to adjacent regions
- `fn optimize_read_ahead_hoist(func: MirFunction, stats: OptimizationStats) -> MirFunction` — hoist predictable reads before control flow

#### mir_opt/mod.spl (Modified — 1 new enum variant)
- `PassScope.FsDriver` — pass targets FS driver code (used by dynamic manifest gating)

#### PassKind additions in mod.spl
- `PassKind.SyscallBatch`
- `PassKind.WriteCoalesce`
- `PassKind.ReadAheadHoist`

#### posix_baseline.spl (New)
- `extern fn rt_posix_open(path: text, flags: i32) -> i64`
- `extern fn rt_posix_read(fd: i64, buf: [u8], len: i64) -> i64`
- `extern fn rt_posix_write(fd: i64, buf: [u8], len: i64) -> i64`
- `extern fn rt_posix_close(fd: i64) -> i32`
- `extern fn rt_posix_rename(old_path: text, new_path: text) -> i32`
- `extern fn rt_posix_unlink(path: text) -> i32`
- `extern fn rt_posix_stat_size(path: text) -> i64`
- `fn run_posix_metadata_storm() -> BenchResult`
- `fn run_posix_append_log() -> BenchResult`
- `fn run_posix_random_overwrite() -> BenchResult`
- `fn run_posix_mmap_read() -> BenchResult`

#### bench_harness.spl (Modified)
- `fn run_all()` — add FAT32 + RamFS for all 4 workloads + POSIX baseline calls
- `fn make_fat32_table() -> MountTable` — factory for FAT32 bench mount
- `fn make_ramfs_table() -> MountTable` — factory for RamFS bench mount (extend existing)

#### fs_hardening_spec.spl (New)
- Spec blocks: `double_close_ramfs`, `stale_handle_read_ramfs`, `stale_handle_write_fat32`, `path_traversal_rejection_ramfs`, `path_traversal_rejection_fat32`, `corrupt_superblock_mount`, `overflow_handle_id_ramfs`, `bpb_validation_fat32`

### Requirement Coverage

- REQ-1 (AC-1) -> `fat32.spl` (validate_bpb, detect_cluster_cycle), `fat32_stub.spl` (handle_guard, path sanitize), `handle_guard.spl`
- REQ-2 (AC-2) -> `nvfs_superblock.spl` (checksum-on-read, short-read rejection), `dbfs_driver.spl` (generation check)
- REQ-3 (AC-3) -> `ramfs.spl` (handle_slots, sorted lookup, overflow guard, double-close), `handle_guard.spl`
- REQ-4 (AC-4) -> `optimization_passes.spl` (3 new pass functions)
- REQ-5 (AC-5) -> `mir_opt/mod.spl` (PassScope.FsDriver, 3 new PassKind variants), `optimizer_manifest.spl` (capability_requires gating)
- REQ-6 (AC-6) -> `bench_harness.spl` (FAT32/RamFS coverage), `posix_baseline.spl` (C comparison)
- REQ-7 (AC-7) -> `ramfs.spl` (binary search), `fat32.spl` (cycle detection bounds), `posix_baseline.spl` (benchmark target)
- REQ-8 (AC-8) -> all modified files preserve existing behavior; hardening is additive
- REQ-9 (AC-9) -> `fs_hardening_spec.spl` (8 spec blocks covering double-close, stale-handle, path-traversal, corrupt-superblock)

### 4-spec

## Specs

### Spec Files
- `test/unit/lib/fs_driver/fs_hardening_spec.spl` — 15 specs covering AC-1, AC-2, AC-3, AC-9
- `test/unit/compiler/mir_opt/fs_optimization_spec.spl` — 11 specs covering AC-4, AC-5
- `test/dbfs/bench_comparison_spec.spl` — 14 specs covering AC-6, AC-7

### AC Coverage Matrix
| AC | Spec File | it block | Status |
|----|-----------|----------|--------|
| AC-1 | `test/unit/lib/fs_driver/fs_hardening_spec.spl` | "AC-1: validate_bpb rejects zero bytes_per_sector" | Failing (no impl) |
| AC-1 | `test/unit/lib/fs_driver/fs_hardening_spec.spl` | "AC-1: validate_bpb rejects non-power-of-two cluster size" | Failing (no impl) |
| AC-1 | `test/unit/lib/fs_driver/fs_hardening_spec.spl` | "AC-1: detect_cluster_cycle detects a cycle" | Failing (no impl) |
| AC-2 | `test/unit/lib/fs_driver/fs_hardening_spec.spl` | "AC-2: corrupt superblock bytes returns Corrupt error" | Failing (no impl) |
| AC-2 | `test/unit/lib/fs_driver/fs_hardening_spec.spl` | "AC-2: short buffer returns Corrupt error" | Failing (no impl) |
| AC-3 | `test/unit/lib/fs_driver/fs_hardening_spec.spl` | "AC-3: find_inode_idx uses binary search (O log n)" | Failing (no impl) |
| AC-9 | `test/unit/lib/fs_driver/fs_hardening_spec.spl` | "AC-9: handle_pack encodes generation in high 32 bits" | Failing (no impl) |
| AC-9 | `test/unit/lib/fs_driver/fs_hardening_spec.spl` | "AC-9: handle_pack encodes slot index in low 32 bits" | Failing (no impl) |
| AC-9 | `test/unit/lib/fs_driver/fs_hardening_spec.spl` | "AC-9: handle_validate rejects stale generation" | Failing (no impl) |
| AC-9 | `test/unit/lib/fs_driver/fs_hardening_spec.spl` | "AC-9: StaleHandle variant exists and is distinct from InvalidArg" | Failing (no impl) |
| AC-9 | `test/unit/lib/fs_driver/fs_hardening_spec.spl` | "AC-9: PathTraversal variant exists and is distinct from Permission" | Failing (no impl) |
| AC-9 | `test/unit/lib/fs_driver/fs_hardening_spec.spl` | "AC-9: double close returns StaleHandle error" | Failing (no impl) |
| AC-9 | `test/unit/lib/fs_driver/fs_hardening_spec.spl` | "AC-9: read on stale handle returns StaleHandle" | Failing (no impl) |
| AC-9 | `test/unit/lib/fs_driver/fs_hardening_spec.spl` | "AC-9: write on stale handle returns StaleHandle" | Failing (no impl) |
| AC-9 | `test/unit/lib/fs_driver/fs_hardening_spec.spl` | "AC-9: path with dot-dot component is rejected" | Failing (no impl) |
| AC-4 | `test/unit/compiler/mir_opt/fs_optimization_spec.spl` | "AC-4: run_named_pass accepts write_coalesce pass name" | Failing (no impl) |
| AC-4 | `test/unit/compiler/mir_opt/fs_optimization_spec.spl` | "AC-4: write coalesce stat counter exists after pass" | Failing (no impl) |
| AC-4 | `test/unit/compiler/mir_opt/fs_optimization_spec.spl` | "AC-4: optimize_syscall_batch accepts MirFunction" | Failing (no impl) |
| AC-4 | `test/unit/compiler/mir_opt/fs_optimization_spec.spl` | "AC-4: syscall batch stat counter exists after pass" | Failing (no impl) |
| AC-4 | `test/unit/compiler/mir_opt/fs_optimization_spec.spl` | "AC-4: optimize_read_ahead_hoist accepts MirFunction" | Failing (no impl) |
| AC-4 | `test/unit/compiler/mir_opt/fs_optimization_spec.spl` | "AC-4: read-ahead hoist stat counter exists after pass" | Failing (no impl) |
| AC-5 | `test/unit/compiler/mir_opt/fs_optimization_spec.spl` | "AC-5: PassScope.FsDriver variant exists" | Failing (no impl) |
| AC-5 | `test/unit/compiler/mir_opt/fs_optimization_spec.spl` | "AC-5: DynamicPassRegistry accepts FsDriver-scoped pass" | Failing (no impl) |
| AC-5 | `test/unit/compiler/mir_opt/fs_optimization_spec.spl` | "AC-5: PassKind includes SyscallBatch variant" | Failing (no impl) |
| AC-5 | `test/unit/compiler/mir_opt/fs_optimization_spec.spl` | "AC-5: PassKind includes WriteCoalesce variant" | Failing (no impl) |
| AC-5 | `test/unit/compiler/mir_opt/fs_optimization_spec.spl` | "AC-5: PassKind includes ReadAheadHoist variant" | Failing (no impl) |
| AC-6 | `test/dbfs/bench_comparison_spec.spl` | "AC-6: make_fat32_table returns a MountTable" | Failing (no impl) |
| AC-6 | `test/dbfs/bench_comparison_spec.spl` | "AC-6: FAT32 driver name present in run_all results" | Failing (no impl) |
| AC-6 | `test/dbfs/bench_comparison_spec.spl` | "AC-6: make_ramfs_table returns a MountTable" | Failing (no impl) |
| AC-6 | `test/dbfs/bench_comparison_spec.spl` | "AC-6: RamFS driver name present in run_all results" | Failing (no impl) |
| AC-6 | `test/dbfs/bench_comparison_spec.spl` | "AC-6: run_all includes metadata_storm workload" | Failing (no impl) |
| AC-6 | `test/dbfs/bench_comparison_spec.spl` | "AC-6: run_all includes append_heavy_log workload" | Failing (no impl) |
| AC-6 | `test/dbfs/bench_comparison_spec.spl` | "AC-6: run_all includes random_overwrite workload" | Failing (no impl) |
| AC-6 | `test/dbfs/bench_comparison_spec.spl` | "AC-6: run_all includes mmap_read_mostly workload" | Failing (no impl) |
| AC-6 | `test/dbfs/bench_comparison_spec.spl` | "AC-6: run_posix_metadata_storm returns BenchResult with p50" | Failing (no impl) |
| AC-6 | `test/dbfs/bench_comparison_spec.spl` | "AC-6: run_posix_append_log returns BenchResult with p99" | Failing (no impl) |
| AC-6 | `test/dbfs/bench_comparison_spec.spl` | "AC-6: run_posix_random_overwrite returns BenchResult" | Failing (no impl) |
| AC-6 | `test/dbfs/bench_comparison_spec.spl` | "AC-6: run_posix_mmap_read returns BenchResult" | Failing (no impl) |
| AC-6 | `test/dbfs/bench_comparison_spec.spl` | "AC-6: run_all results contain p50_us and p99_us fields" | Failing (no impl) |
| AC-6 | `test/dbfs/bench_comparison_spec.spl` | "AC-6: POSIX baseline included alongside Simple drivers" | Failing (no impl) |
| AC-7 | `test/dbfs/bench_comparison_spec.spl` | Structural coverage — numeric AC-7 verified in phase 7-verify | N/A (phase 7) |
| AC-8 | Existing test suite | Re-run existing tests after implementation | N/A (phase 7) |

## Phase
spec-done

### 5-implement
<pending>

### 6-refactor
<pending>

### 7-verify
<pending>

### 8-ship
<pending>

## Log
- 1-dev: Created state file with 9 acceptance criteria, 3 workstreams
- 2-research: Found 10 reusable modules, 12 source files analyzed, 9 requirements drafted; key findings: NvfsDriver delegates to DbFsDriver, FAT32 missing from bench harness, C boundary is 4 externs only
- 3-arch: Designed 14 modules (3 new, 11 modified), 6 architecture decisions, no circular deps; key decisions: 2 new FsError variants (StaleHandle/PathTraversal), high-32/low-32 handle generation packing, sorted-array binary search for RamFS, stdlib-only NvfsDriver hardening boundary, conservative MIR pass transforms, SFFI-based POSIX baseline
- 4-spec: Created 3 spec files with 40 total specs, 7/9 ACs covered by new specs (AC-1..AC-6, AC-9); AC-7 numeric + AC-8 regression deferred to phase 7-verify
