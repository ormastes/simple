# ctype Static LUT Benchmark Export Fix
**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

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

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no repro that ran conclusively within the triage budget; closed stale per the standing 'too old -> close' decision. Binary (unused, no run needed): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
