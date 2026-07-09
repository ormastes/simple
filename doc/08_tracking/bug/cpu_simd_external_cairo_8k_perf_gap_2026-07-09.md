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

Follow-up optimization on 2026-07-09 removed per-character glyph row-array
allocation from the CPU text path and re-ran the same retained 8K row:

- Simple Web CPU-SIMD: `938.678 ms` p50 at `7680x4320`, 300dpi, no screen-size
  reduction, checksum `sum32:135445232233405312`.
- Improvement versus the recorded 2026-07-08 row: `26.8%`.
- Remaining gap versus Node Canvas/Cairo: `11.7x` slower.
- Evidence report: `doc/09_report/cpu_simd_text_glyph_inline_perf_2026-07-09.md`.
- Current owner blocker:
  `doc/08_tracking/bug/browser_layout_large_simd_fill_facade_unsafe_2026-07-09.md`.

The current external CPU baseline refresh after the text paint-loop width-scan
skip records:

- Simple Web CPU-SIMD: `796.960 ms` p50 at `7680x4320`, 300dpi, no screen-size
  reduction, checksum `sum32:135445232233405312`.
- Simple Web scalar software: `912.982 ms` p50 with the same checksum.
- Node Canvas/Cairo: `72.510 ms` p50 at the same 8K size.
- `gui_perf_cpu_base_compare_dpi_source=default`.
- `gui_perf_cpu_base_compare_schedule_order=cpu_simd_first`.
- `gui_perf_cpu_base_compare_target_met=no`.
- Current evidence report:
  `doc/09_report/gui_perf_benchmark_2026-07-09_cpu_base.md`.
- Remaining gap versus Node Canvas/Cairo: `11.0x` slower.

`doc/09_report/cpu_simd_render_scale_contract_2026-07-08.md` separately proves
the CPU-SIMD path beats the in-repo scalar software path for the focused 4K/8K
contract, so the remaining gap is external drawing-library parity.

## Expected

Either Simple Web CPU-SIMD reaches the external CPU drawing-library baseline for
the retained 8K scene, or the report keeps this blocker open with the measured
ratio and the bottleneck owner.

## Next Step

Profile the next largest retained render-loop cost after glyph row lookup. The
gap is still dominated by Simple Web layout/DrawIR/text presentation rather than
viewport size, DPI, checksum, or GPU backend selection semantics.
