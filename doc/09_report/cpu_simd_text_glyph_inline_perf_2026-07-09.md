# CPU-SIMD Text Glyph Inline Perf Evidence

**Date:** 2026-07-09
**Scope:** Simple Web CPU-SIMD retained 4K/8K render loop

## Change

`SoftwareBackend.draw_text` now reads glyph rows directly from the shared packed
5x7 atlas (`glyph_index_for_char_code` + `glyph_row_bits`) instead of creating a
per-character row array through `glyph_data`.

This does not change viewport size, DPI, checksum policy, GPU backend selection,
or glyph source data.

## Evidence

Command shape:

```bash
SIMPLE_LIB=src bin/simple run src/app/wm_compare/backend_measurement_software_export.spl --mode=native -- \
  --software-render-backend cpu_simd \
  --width 7680 --height 4320 \
  --warmup-count 1 --sample-count 1 \
  --dpi 300 \
  --fixture gui-perf-8k-cpu-simd \
  --shell simple-web \
  --command bench-8k \
  --host local
```

Observed after the change:

- 4K CPU-SIMD p50: `243530us`, checksum `sum32:32105444634193792`,
  pixel proof `nonzero_pixels:8294400`.
- 8K CPU-SIMD p50: `938678us`, checksum `sum32:135445232233405312`,
  pixel proof `nonzero_pixels:33177600`.
- DPI metadata: `gui_perf_benchmark_dpi=300`,
  `gui_perf_benchmark_density_profile=retina`.
- Screen-size metadata: `gui_perf_benchmark_screen_size_reduced=false`.

The retained 8K checksum matches the prior external-compare report, so this is a
performance-only change for that workload.

## Remaining Gap

The prior external Node Canvas/Cairo row remains `80.201ms` p50 at the same 8K
size. The CPU-SIMD row improved from `1282.166ms` to `938.678ms`, but remains
about `11.7x` slower than that external CPU drawing-library baseline.

## Rejected Follow-ups

Two smaller follow-ups were tried and reverted because they preserved the
checksum but did not improve the retained 8K row:

- Coalescing adjacent glyph-bit spans in `SoftwareBackend.draw_text`: 8K
  `938812us`, checksum `sum32:135445232233405312`.
- Returning selector-backed HTML to full layout before heuristic color scans:
  8K `947898us`, checksum `sum32:135445232233405312`.

The next useful target is the full Simple Web layout/paint stage split, not
another backend-only text-loop micro-change.

## Verification

- `SIMPLE_LIB=src bin/simple test test/03_system/check/cpu_simd_render_scale_contract_spec.spl --mode=interpreter --clean`
  passed: `2 examples, 0 failures`.
