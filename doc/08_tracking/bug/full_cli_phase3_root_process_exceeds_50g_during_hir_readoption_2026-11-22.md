# Full-CLI Phase 3 root process exceeds 50G during HIR re-adoption

- **Date:** 2026-11-22
- **Status:** open
- **Severity:** P1

## Symptom

The Phase 3 full-CLI build root process grows past 50G while adopting HIR from workers and is OOM-killed (rc=137).

## Evidence

Build f28 (Stage 2 integ27, release 263f49ab6c5, MemoryMax=50G, 10 cores) was killed at HIR adopt 3667/4139 modules. The root process alone passed 50G; peak for the unit was 50.0G. Two concurrent full-CLI builds therefore cannot share a 121G host.

## Repro

Full-CLI Phase 3 native-build under `MemoryMax=50G`; watch root RSS during HIR adoption.

## Workaround

Run one full-CLI build at a time with a MemoryMax above 50G.

## Fix direction

Stream or drop adopted HIR once consumed, and measure root RSS per adopted module to find the growth source.

## Related

f28's separate failure (`runtime_c_compile_pool_v1.spl` importing `cpu_count_checked` from `std.io_runtime`, introduced by e0aea49c8e9) is already fixed by #10777 (5d5c17bf4e0); no separate row.
