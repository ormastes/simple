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

## Timing

`bench_now_ns()` calls `rt_time_now_nanos()`, backed by a monotonic native clock.
CSV columns use nanoseconds and report `kops_per_s` as `(iters * 1_000_000) / total_ns`.

---

## How to Run

```bash
# All benchmarks (combined CSV + markdown summary):
bin/simple run test/perf/bench/run_all.spl

# Individual benchmarks:
bin/simple run test/perf/bench/fs_driver_mount_table.spl
bin/simple run test/perf/bench/nvfs_arena_throughput.spl
bin/simple run test/perf/bench/spostgre_wal_append.spl
bin/simple run test/perf/bench/durable_wal_fsync.spl
python3 test/perf/bench/durable_wal_fsync.py
```

---

## CSV Output and Baselines

Each bench prints a CSV block. Save it as a baseline:

```bash
bin/simple run test/perf/bench/run_all.spl > doc/08_tracking/bench/baseline_2026-04-17.csv
```

To compare two runs:

```bash
diff doc/08_tracking/bench/baseline_2026-04-17.csv \
     doc/08_tracking/bench/baseline_2026-04-18.csv
```

CSV columns: `label,iters,p50_ns,p99_ns,p99_9_ns,min_ns,max_ns,total_ns,kops_per_s`

---

## Benchmark Files

| File | Scenarios | Notes |
|---|---|---|
| `test/perf/bench/lib/timing.spl` | Library | `BenchResult`, `bench_now_ns`, `bench_print`, `bench_csv` |
| `test/perf/bench/fs_driver_mount_table.spl` | 3 | MountTable resolve/lookup; validates FR-STORAGE-0004 str_char_at perf |
| `test/perf/bench/nvfs_arena_throughput.spl` | 4 | Arena append/readv/clone_range/seal via in-proc shim |
| `test/perf/bench/spostgre_wal_append.spl` | 3 | WAL append/commit_group/recover_tail via in-proc shim |
| `test/perf/bench/durable_wal_fsync.spl` | 2 | Simple runtime write-at+fsync durability-fence probe; not raw NVMe/FUA |
| `test/perf/bench/durable_wal_fsync.py` | 3 | Host file write+fsync plus torn-tail recovery probe; not raw NVMe/FUA |
| `test/perf/bench/run_all.spl` | 2 rep. | Combined runner, CSV + markdown summary |

## Durable WAL Host Evidence

`durable_wal_fsync.py` adds a host recovery check around the fsync timing
probe. It writes CRC-framed records, appends a partial torn-tail record,
recovers complete records, truncates to the last valid byte, and re-runs
recovery after truncation. Current evidence on this host:

| probe | result |
|---|---|
| write 256B + fsync each | p50 5.47 ms, ~189 ops/s |
| group 10x256B + fsync | p50 4.91 ms, ~165 group-fsync ops/s |
| torn-tail recovery | 16 records recovered, truncated to 4416 valid bytes |

This proves the host-file WAL probe has a real fsync fence and a deterministic
torn-tail recovery check. It still does not prove production DB durability on
raw NVMe/FUA or under power-loss hardware validation.

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
