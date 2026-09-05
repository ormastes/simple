# ctype Static LUT Benchmark Export Fix

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
