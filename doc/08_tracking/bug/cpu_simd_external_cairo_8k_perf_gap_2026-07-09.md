# CPU-SIMD External Cairo 8K Perf Gap

- **Date:** 2026-07-09
- **Status:** open
- **Severity:** high
- **Area:** GUI Web 2D, CPU-SIMD, performance

## Summary

The retained full-size 8K GUI benchmark shows Simple Web CPU-SIMD is still
slower than the available external CPU drawing-library baseline on this host.
This is an optimization blocker, not a correctness blocker.

## Evidence

`doc/09_report/gui_perf_benchmark_2026-07-08.md` records:

- Simple Web CPU-SIMD: `1282.166 ms` p50 at `7680x4320`, 300dpi, no screen-size
  reduction, checksum `sum32:135445232233405312`.
- Node Canvas/Cairo: `80.201 ms` p50 at the same 8K size.
- `gui_perf_cpu_base_compare_target_met=no`.

`doc/09_report/cpu_simd_render_scale_contract_2026-07-08.md` separately proves
the CPU-SIMD path beats the in-repo scalar software path for the focused 4K/8K
contract, so the remaining gap is external drawing-library parity.

## Expected

Either Simple Web CPU-SIMD reaches the external CPU drawing-library baseline for
the retained 8K scene, or the report keeps this blocker open with the measured
ratio and the bottleneck owner.

## Next Step

Profile the native Simple Web CPU-SIMD 8K row and remove the largest retained
render-loop cost without changing viewport size, DPI, checksum, or GPU backend
selection semantics.
