# SStack State: fat32-vs-cfat-bench

## User Request
> Create a Simple FAT32 vs C FAT (Linux VFAT) benchmark suite. Start with simple fat vs c fat benchmarks.

## Task Type
feature

## Refined Goal
> Build a benchmark suite that measures Simple FAT32 vs Linux VFAT (C FAT) performance across 7 workloads: lookup, sequential read, create, append, delete, stat, and directory scan. Reuse the existing bench_harness.spl framework (BenchResult, p50/p99 latency). Run Simple FAT32 in-process via FsDriver trait, and Linux VFAT via mounted loopback FAT32 image with std.fs calls. Output results to doc/10_metrics/ in a format consistent with fs_driver_vfat_comparison.md. All benchmarks bounded by timeout, dataset size, and temp directory cleanup per crash-safe execution rules.

## Acceptance Criteria
- [ ] AC-1: Benchmark spec file at test/bench/fat32_vs_cfat_bench.spl compiles and runs via `bin/simple test`
- [ ] AC-2: 7 workloads implemented: lookup, sequential_read, create, append, delete, stat, directory_scan
- [ ] AC-3: Each workload runs against Simple FAT32 (in-process FsDriver) and reports BenchResult with p50/p99 latency
- [ ] AC-4: Each workload runs against Linux VFAT (loopback mount) and reports BenchResult with p50/p99 latency
- [ ] AC-5: Results written to doc/10_metrics/fat32_vs_cfat_benchmark.md with per-workload comparison table
- [ ] AC-6: Dataset bounded (max 64 MiB image, max 1000 files, 30s timeout per workload)
- [ ] AC-7: Temp files and loopback images cleaned up on exit (no leaked mounts or files)

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-26
- [ ] 2-research (Analyst)
- [ ] 3-arch (Architect)
- [ ] 4-spec (QA Lead)
- [ ] 5-implement (Engineer)
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev
**Task type:** feature
**Refined goal:** FAT32 vs C FAT benchmark suite with 7 workloads using existing bench harness.

**Key files:**
- `test/bench/fat32_vs_cfat_bench.spl` — main benchmark (NEW)
- `doc/10_metrics/fat32_vs_cfat_benchmark.md` — results output (NEW)
- `test/dbfs/bench_harness.spl` — existing harness to reuse
- `src/lib/nogc_sync_mut/fs_driver/fat32_core.spl` — Simple FAT32 driver
- `src/lib/nogc_sync_mut/fs_driver/ops.spl` — FsDriver trait

**Design decisions:**
- Simple FAT32: create in-memory or temp-file backed FAT32 image, mount via Fat32Core/FsDriver trait
- C FAT baseline: create loopback FAT32 image with mkfs.fat, mount via `mount -o loop`, operate via std.fs
- Linux VFAT mount requires root or fuse — if not available, skip C FAT and report Simple-only results
- 7 workloads match optimization plan work queue item 1

**ACs:** 7 criteria covering compilation, workloads, dual-driver measurement, results doc, bounds, cleanup.

### 2-research
<pending>

### 3-arch
<pending>

### 4-spec
<pending>

### 5-implement
<pending>

### 6-refactor
<pending>

### 7-verify
<pending>

### 8-ship
<pending>
