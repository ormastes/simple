# ctype Static LUT Benchmark Export Fix

## Closed 2026-09-13 — confirmed fixed: the exports exist and the benchmark runs
- **measured** — `test/05_perf/ctype/ctype_lut_tables.spl:28` reads
  `export CTYPE_FLAG_TABLE, CTYPE_BYTE_SMOKE_TABLE` — the missing exports this entry
  records adding.
- **measured** — `bin/simple run test/05_perf/ctype/bench_ctype_static_lut.spl`
  (Rust seed v1.0.0-rc.1, Windows) completes all four benchmarks, e.g.
  `lang=simple_static_lut bench=is_alpha ops=128000000 ops_per_ms=80369 checksum=52000000`,
  ending `combined_checksum=142000000`.

Date: 2026-06-21

## Summary

`test/05_perf/ctype/global_static_array_smoke.spl` and
`test/05_perf/ctype/bench_ctype_static_lut.spl` imported static lookup tables
from `ctype_lut_tables`, but the table module did not export those symbols.

## Fix

- Exported `CTYPE_FLAG_TABLE`.
- Added and exported the benchmark-local `CTYPE_BYTE_SMOKE_TABLE` used by the
  static-array smoke check.
- Routed benchmark timing/exit helpers through `std.io_runtime`.

## Evidence

- `bin/simple check test/05_perf/ctype/ctype_lut_tables.spl`: PASS
- `bin/simple check test/05_perf/ctype/global_static_array_smoke.spl`: PASS
- `bin/simple check test/05_perf/ctype/bench_ctype_static_lut.spl`: PASS
- `bin/simple run test/05_perf/ctype/global_static_array_smoke.spl`: prints
  `[ctype-static-array] ok`
