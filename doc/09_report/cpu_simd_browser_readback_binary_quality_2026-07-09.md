# CPU-SIMD Browser Readback Binary Quality Evidence - 2026-07-09

## Scope

Verify that CPU-SIMD browser readback keeps color, `rgba()` alpha composition,
and CSS `opacity` composition stable when the focused spec is run through the
native/binary test mode.

## Evidence

- Commit under test: `6682fe9ac85a` (`test(simd): cover css opacity cpu readback`)
- Command:
  `SIMPLE_LIB=src bin/simple test test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_cpu_simd_paint_spec.spl --mode=native --clean`
- Result: PASS, 3 examples, 0 failures
- Quality assertions:
  - Solid color readback: `0xFF336699`
  - `rgba(255,0,0,.5)` over white: `0xFFFF8080`
  - `background-color:#336699; opacity:0.5` over white: `0xFF99B3CC`
  - Readback source remains `cpu_mirror`
  - CPU-SIMD browser readback does not route through GPU paint offload counters

## Notes

This report records binary-mode quality evidence only. It does not close the
remaining 8K performance blocker tracked by the mutable-array/fill owner work.
