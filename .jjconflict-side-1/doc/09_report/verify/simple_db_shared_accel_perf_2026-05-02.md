# Simple DB Shared Accel Perf Evidence

**Report file date:** 2026-05-02  
**Latest verification in this update:** 2026-05-03  
**Scope:** Phase 1 shared accel verification for SDN, DBFS, and `spostgre`

## Status

Status: `WARN`

- The benchmark harness was rerun successfully on 2026-05-03.
- The current runtime semantics are shared-path plus scalar fallback, not active
  SIMD kernels.
- The old 2026-05-02 statement that `simd_active=true` is not valid for the
  current harness and is superseded by the rerun below.

## What Ran In This Update

Focused correctness check:

- `bin/simple test test/unit/lib/db/accel_spec.spl`

Startup probe:

- `/usr/bin/time -f "run=%C elapsed=%e rss_kib=%M" bin/simple -c "print 1"`

Benchmark rerun:

- `/usr/bin/time -f "elapsed=%e rss_kib=%M" bin/simple run test/perf/bench/simple_db_shared_accel.spl`

## Current Verified Semantics (2026-05-03)

From the successful benchmark rerun:

- tier: `x86_64_avx2`
- `simd_available=true`
- `simd_active=false`
- `scalar_fallback=true`
- width: `256`

Interpretation:

- host SIMD capability detection is live
- Phase 1 DB accel kernels are still running the scalar-oracle path
- benchmark labels that say `shared` or `shared_fallback` currently measure
  shared API, bitmap, row-id, and coarse-filter overhead around scalar behavior

## Correctness Cross-Check

Verified in this update:

- `test/unit/lib/db/accel_spec.spl` passed: `11` examples, `0` failures
- `test/perf/bench/simple_db_shared_accel.spl` now runs a preflight before
  timing and completed successfully on 2026-05-03

Preflight scope inside the benchmark:

- shared text scan count vs scalar text count
- SDN shared query row count vs scalar row count
- DBFS `find_child_accel` result vs scalar lookup
- DBFS prefix result count vs scalar prefix count
- `spostgre` shared fullscan count vs scalar fullscan count
- `spostgre` BRIN-refine count vs scalar BRIN-refine count

## Startup / RSS (2026-05-03)

External startup probe (`bin/simple -c "print 1"`):

- run 1: `elapsed=0.03`, `rss_kib=16640`
- run 2: `elapsed=0.02`, `rss_kib=17152`
- run 3: `elapsed=0.02`, `rss_kib=17152`

Observed result:

- no obvious startup regression signal from this benchmarked path
- warm startup stayed within `0.02s` to `0.03s`
- max RSS stayed below `17 MiB` on this probe

## Benchmark Rerun Highlights (2026-05-03)

Timed whole benchmark invocation:

- `elapsed=7.36`
- `rss_kib=35540`

Representative p50 results from the rerun:

| Workload | p50 |
| --- | ---: |
| `shared_text_scan_fallback_contains` | `9564555 ns` |
| `shared_text_scan_fallback_contains_row_ids` | `14120971 ns` |
| `scalar_text_scan_contains_loop` | `1671610 ns` |
| `scalar_text_scan_contains_bitmap_build` | `4995404 ns` |
| `sdn_querybuilder_execute_rows_shared_fallback` | `10647902 ns` |
| `sdn_handrolled_scalar_filter_rows` | `8240588 ns` |
| `dbfs_find_child_accel` | `2194959 ns` |
| `dbfs_find_child_scalar` | `7433728 ns` |
| `dbfs_prefix_accel` | `5213110 ns` |
| `dbfs_prefix_scalar` | `8579786 ns` |
| `spostgre_shared_fallback_fullscan` | `8031719 ns` |
| `spostgre_shared_fallback_brin_refine` | `68678279 ns` |
| `spostgre_scalar_brin_refine` | `22837608 ns` |
| `spostgre_scalar_fullscan_count_only` | `2487618 ns` |
| `spostgre_text_search_candidates` | `26559912 ns` |

## Reading The Numbers

Current takeaways:

1. The rerun confirms the harness is measuring shared-scalar fallback behavior,
   not active SIMD execution.
2. The text and `spostgre` shared/fallback paths remain slower than their
   leaner scalar baselines on this host.
3. The SDN shared row-materializing path is still slower than the hand-rolled
   scalar row-materializing loop.
4. DBFS is mixed: the current shared accel helpers beat the local scalar loops
   for `find_child` and prefix scans in this rerun.
5. `spostgre_shared_fallback_brin_refine` must be compared against
   `spostgre_scalar_brin_refine`, not the count-only fullscan baseline.

## Historical Note About 2026-05-02

This file name remains dated `2026-05-02`, but the report now contains a
2026-05-03 rerun because the prior text no longer matched current harness
semantics.

Treat the following as historical-only and superseded:

- the old claim that `simd_active=true`
- older benchmark labels such as `accel_text_scan_contains`,
  `sdn_query_batch_filter`, and `spostgre_scan_accel`
- any interpretation that the Phase 1 numbers reflected active ISA-specific
  DB kernels

## Conclusion

The benchmark is still useful, but only as a shared-fallback baseline and
correctness guard for later SIMD work. Use
`test/perf/bench/simple_db_shared_accel.spl` as the before/after harness when
real DB accel SIMD kernels land.
