# Simple DB Shared Accel Perf Evidence

**Date:** 2026-05-02  
**Scope:** Phase 1 shared accel verification for SDN, DBFS, and `spostgre`

## What Ran

Benchmark script:

- `bin/simple run test/perf/bench/simple_db_shared_accel.spl`

Startup probe:

- `/usr/bin/time -f "run=%i elapsed=%e rss_kib=%M" bin/simple -c "print 1"`

Fallback / behavior coverage already in tree:

- `bin/simple test test/unit/lib/db/accel_spec.spl`
- `bin/simple test test/unit/lib/database/database_query_spec.spl`
- `bin/simple test --clean test/integration/lib/database_query_spec.spl`
- `bin/simple test --clean test/dbfs/dbfs_catalog_schema_spec.spl`
- `bin/simple test --clean examples/spostgre/test/unit/scan_test.spl`

## Host Capability

From `accel_capability_report()` during the benchmark run:

- tier: `x86_64_avx2`
- `simd_active=true`
- `scalar_fallback=true`
- width: `256`

Interpretation:

- host SIMD capability detection is live
- Phase 1 shared accel still executes scalar kernels
- current numbers therefore measure the cost of the shared abstraction layer,
  bitmap materialization, and batching structure, not ISA-specific speedups

## Startup / RSS

External startup probe (`bin/simple -c "print 1"`):

- run 1: `elapsed=0.03`, `rss_kib=16640`
- run 2: `elapsed=0.03`, `rss_kib=16640`
- run 3: `elapsed=0.03`, `rss_kib=16896`

Observed result:

- no obvious startup regression signal from the shared accel tranche
- warm startup stayed at `0.03s`
- max RSS stayed below `17 MiB` on this probe

## Steady-State Benchmark Highlights

Timed whole benchmark invocation:

- `elapsed=30.54`
- `rss_kib=32256`

Representative p50 results from the benchmark body:

| Workload | p50 |
| --- | ---: |
| `accel_text_scan_contains` | `334227307 ns` |
| `scalar_text_scan_contains` | `1644328 ns` |
| `sdn_query_batch_filter` | `85209683 ns` |
| `sdn_query_scalar_filter` | `7624972 ns` |
| `dbfs_find_child_accel` | `33531271 ns` |
| `dbfs_find_child_scalar` | `7577160 ns` |
| `dbfs_prefix_accel` | `37763728 ns` |
| `dbfs_prefix_scalar` | `8752143 ns` |
| `spostgre_scan_accel` | `350007651 ns` |
| `spostgre_scan_scalar` | `1625942 ns` |

## Findings

1. Phase 1 shared accel is functionally wired, but it is not yet a speed win on this host.
2. The current accel path is slower than the direct scalar baselines for all measured workloads.
3. That matches the implementation reality:
   - bitmap materialization is real
   - batching is real
   - host capability reporting is real
   - ISA-specific SIMD kernels are **not** landed yet
4. The benchmark is still useful because it establishes a pre-SIMD baseline for:
   - SDN batch filtering
   - DBFS namespace summary/prefix scans
   - `spostgre` tuple-text filtering

## Conclusion

Status: `WARN`

- correctness and fallback coverage are in place
- startup/RSS look stable for this tranche
- steady-state latency evidence shows the current shared layer is a structural
  baseline, not a performance win yet

Next action:

- use `test/perf/bench/simple_db_shared_accel.spl` as the before/after harness
  when real AVX2/NEON kernels are added to `std.db.accel`
