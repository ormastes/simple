# Filesystem And Compiler Optimization Plugin Plan - 2026-05-26

## Purpose

Consolidate FAT, NVFS, DBFS filesystem performance work with the compiler and
optimization-plugin work needed to make pure Simple implementations competitive
with C/provider baselines.

## Source Plans

- `doc/03_plan/crash_recovery_replan_2026-05-25.md`
- `doc/03_plan/pure_simple_lib_standalone_hw_plan.md`
- `doc/03_plan/nvfs_dbfs_real_filesystem.md`
- `doc/03_plan/agent_tasks/optimization_plugin_jit_hotspot.md`
- `doc/03_plan/sys_test/optimization_plugin_jit_hotspot.md`
- `doc/03_plan/sys_test/nvfs_completion.md`
- `doc/03_plan/sys_test/storage_fat32_handle_metadata.md`
- `doc/03_plan/sys_test/storage_fat32_statfs_truncate.md`
- `doc/10_metrics/fs_driver_vfat_comparison.md`

## Scope

- Make Simple FAT/FAT32 beat the current C FAT path on representative workloads.
- Make NVFS and DBFS beat optimized FAT for executable load, metadata lookup,
  small-file write, and remount/recovery workloads.
- Keep C/SFFI paths as explicit providers or benchmarks, not silent defaults.
- Add compiler/plugin facts and transforms for filesystem hot paths:
  - directory-entry scans
  - cluster-chain walks
  - byte copy/fill/compare
  - endian load/store
  - checksum reducers
  - prefix/name-table scans
  - WAL/checkpoint batching
- Keep the optimization provider general enough for adjacent DB, webserver, and
  SimpleOS/QEMU hot paths; do not make it a filesystem-only or optimizer-only
  special case.
- Tie every performance claim to a metric under `doc/10_metrics/`.

## Crash-Safe Execution Rules

- No live QEMU in this track unless coordinated by the SimpleOS real HW/QEMU
  track.
- Benchmarks must be bounded by timeout, dataset size, and output directory.
- Run only one heavy benchmark family at a time.
- Require at least 250 GiB free disk and 32 GiB available memory before
  benchmark runs.

## Work Queue

1. Refresh FAT vs C FAT benchmark baseline with lookup, sequential read,
   create, append, delete, stat, and directory scan workloads.
2. Add Simple FAT optimizations:
   - directory-entry scan cache
   - cluster-chain prefetch
   - write coalescing
   - exact-hit short-name/long-name decode avoidance
3. Refresh NVFS/DBFS benchmarks against the optimized FAT baseline.
4. Add or tune NVFS/DBFS hot indexes:
   - persistent name table
   - prefix/radix dentry index
   - append/write batching
   - binary-safe executable load with no extra decode pass
5. Feed measured hot paths into the optimization plugin:
   - emit `CLibParityHotspot` or equivalent facts
   - add MIR/native benchmark cases
   - verify warm-start, invalidation, and RSS impact.
   - require semantic-equivalence and provider-boundary proofs before rewrite.

## Verification Gates

- Correctness specs for FAT, NVFS, DBFS, boot FS, VFS rootfs, and ELF loading
  pass before performance claims.
- Benchmark report records C baseline, provider, interpreter, native, and LLVM
  native where available.
- Pure Simple native must reach at least `0.80x` C before replacing a hosted
  default, unless a documented standalone/hardware reason keeps it enabled with
  a follow-up.
- Optimization-plugin changes must not regress MCP/LSP startup latency or RSS.
- General parity rules must include filesystem, database, webserver, and
  SimpleOS/QEMU domains with explicit required proofs.
