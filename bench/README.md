# Phase 9 Storage Benchmarks

## Purpose

Measure the **algorithmic cost** of fs_driver, NVFS, and spostgre primitives
on the current in-memory implementations.

---

## DISCLAIMER — READ FIRST

**These numbers DO NOT reflect real SSD hardware.**

Phase 9 storage components (N1/N3/N5a/N5b NVFS nodes, spostgre M1/M2) use
mocks or in-process byte-vector arenas. Every benchmark here measures:

- CPU cost of the code path (prefix-match dispatch, CRC framing, sort)
- Interpreter-mode tick overhead (see Timing section below)

They do **not** measure:

- NVMe command submission / completion latency (~10–200µs)
- FUA write fence cost (~50–200µs on commodity NVMe)
- Flash Translation Layer (FTL) garbage-collection tail latency
- DRAM cache effects
- Any real I/O

**Real SSD benchmarks require the NVMe driver layer (Phase 10+).**

---

## SSD-iq Honesty Note (research §8 criteria)

The research document (`doc/01_research/spostgre_research.md §8`) identifies
4 mandatory criteria for SSD-honest benchmarking. Current status:

| Criterion | Phase 9 status |
|---|---|
| **Preconditioning** — full-device-write before measurement | Not possible (no real SSD). Can measure once Phase 10 NVMe driver lands. |
| **Latency-under-load** — measure tail at >50% queue depth | Not possible (no NVMe queue). Tick proxy is single-threaded and has no load. |
| **Physical-media writes** — count WAF, not just logical bytes | Not possible (no NAND). |
| **Skew sensitivity** — hot-key / hot-page latency distribution | Partially: bench measures latency distribution (p50/p99/p99.9) on algorithmic paths, but without real IO variance these distributions are flat. |

These benchmarks are useful for **regression-detecting algorithmic regressions**
across refactors. They are not a substitute for SSD-iq-compliant benchmarks.

---

## Timing Limitation

`bench_now_ns()` is a **monotone loop counter** (increments by 1 per call),
not a real nanosecond clock. Simple does not yet expose `clock_gettime(CLOCK_MONOTONIC)`.

- **FR-BENCH-CLOCK-001:** Add `extern fn rt_time_now_ns() -> i64` backed by
  `clock_gettime(CLOCK_MONOTONIC)` to `src/runtime/runtime_native.c`.
  Once landed, replace `g_bench_tick` in `bench/lib/timing.spl` with
  `extern fn rt_time_now_ns() -> i64`.

Until then: column headers say `_ticks` not `_ns`. The percentile math
(p50/p99/p99.9) is correct; only the unit is wrong.

---

## How to Run

```bash
# All benchmarks (combined CSV + markdown summary):
bin/simple run bench/run_all.spl

# Individual benchmarks:
bin/simple run bench/fs_driver_mount_table.spl
bin/simple run bench/nvfs_arena_throughput.spl
bin/simple run bench/spostgre_wal_append.spl
```

---

## CSV Output and Baselines

Each bench prints a CSV block. Save it as a baseline:

```bash
bin/simple run bench/run_all.spl > doc/08_tracking/bench/baseline_2026-04-17.csv
```

To compare two runs:

```bash
diff doc/08_tracking/bench/baseline_2026-04-17.csv \
     doc/08_tracking/bench/baseline_2026-04-18.csv
```

CSV columns: `label,iters,p50_ticks,p99_ticks,p99_9_ticks,min_ticks,max_ticks,total_ticks,ops_per_ktick`

---

## Benchmark Files

| File | Scenarios | Notes |
|---|---|---|
| `bench/lib/timing.spl` | Library | `BenchResult`, `bench_now_ns`, `bench_print`, `bench_csv` |
| `bench/fs_driver_mount_table.spl` | 3 | MountTable resolve/lookup; validates FR-STORAGE-0004 str_char_at perf |
| `bench/nvfs_arena_throughput.spl` | 4 | Arena append/readv/clone_range/seal via in-proc shim |
| `bench/spostgre_wal_append.spl` | 3 | WAL append/commit_group/recover_tail via in-proc shim |
| `bench/run_all.spl` | 2 rep. | Combined runner, CSV + markdown summary |

---

## Submodule Import Limitation

`examples/nvfs` and `examples/spostgre` are separate git submodules. Their
packages are not resolvable via `use examples.nvfs.*` from main-repo
`bin/simple run`. NVFS and WAL scenarios run against local shims that mirror
the real API exactly:

- **FR-BENCH-NVFS-001:** wire real `use examples.nvfs.src.core.arena.*` once
  submodule import resolution is supported in the bench runner.
- **FR-BENCH-WAL-001:** wire real `use examples.spostgre.src.engine.wal.*`
  similarly.

The shim API is intentionally identical to the real API so replacement is a
1-line import change per file.
