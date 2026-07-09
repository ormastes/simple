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

## Layout/Paint Stage Split

An opt-in trace flag was added to
`src/app/wm_compare/backend_measurement_software_export.spl` so the same
generated benchmark HTML can run through
`simple_web_layout_render_html_software_pixels_traced` without changing the
normal render-loop measurement.

4K trace:

- `parse_html_ms=1`, `extract_css_ms=0`, `compute_styles_ms=1`,
  `layout_ms=0`, `paint_ms=201`.
- Total: `204480us`.
- Checksum: `sum32:32105444634193792`.

8K trace:

- `parse_html_ms=1`, `extract_css_ms=0`, `compute_styles_ms=1`,
  `layout_ms=0`, `paint_ms=776`.
- Total: `779724us`.
- Checksum: `sum32:135445232233405312`.
- Box trace after adding trace-only layout diagnostics showed:
  `html x=0 y=0 w=7680 h=282 bg=0`,
  `body x=8 y=8 w=7664 h=266 bg=270544896`, and
  `main x=8 y=8 w=7664 h=266 bg=0`.

The retained 8K bottleneck is therefore paint/fill bandwidth over the full
framebuffer, not parse, CSS, style, or layout.

Native SIMD framebuffer initialization was tested and reverted:

- `simd_fill_row` over a zero-initialized framebuffer logged
  `unknown extern function: rt_engine2d_simd_fill_u32`, changed the checksum,
  and slowed 4K trace to `878028us`.
- `engine2d_simd_fill_row_u32` over the full framebuffer segfaulted at 4K.

The next optimization should stay inside the Engine2D-owned SIMD fill path or
register a safe browser-layout framebuffer fill facade before using native SIMD
from `simple_web_html_layout_renderer.spl`.

Follow-up trace instrumentation now splits the opt-in paint line into
`framebuffer_init_ms`, `trace_setup_ms`, `paint_draw_ms`, and aggregate
`paint_ms`. This does not change normal rendering; it only makes the next
retained 4K/8K trace distinguish full-frame framebuffer initialization,
trace-only setup, and subsequent draw work.

Follow-up split traces:

- 4K: `framebuffer_init_ms=188`, `trace_setup_ms=0`, `paint_draw_ms=15`,
  `paint_ms=204`, total `208234us`, checksum `sum32:32105444634193792`,
  `nonzero_pixels:8294400`.
- 8K: `framebuffer_init_ms=1503`, `trace_setup_ms=0`, `paint_draw_ms=32`,
  `paint_ms=1535`, total `1539281us`, checksum
  `sum32:135445232233405312`, `nonzero_pixels:33177600`.

Both split traces kept `dpi=300`, `density_profile=retina`, full physical
size, and `screen_size_reduced=false`. The split-trace run is retained as
bottleneck evidence, not as a speed improvement: it shows the dominant cost is
full-frame framebuffer initialization/fill before draw work, which reinforces
that the remaining optimization belongs at the browser-layout framebuffer owner
boundary.

Native array-repeat fill was then aligned with the existing Simple core
runtime implementation so `[base; width * height]` sets the array length once
and fills the backing words directly instead of calling `rt_array_push` once
per pixel. The Rust runtime mirror uses the same no-push fill shape. Sequential
trace evidence after the C native runtime change:

- 4K: `framebuffer_init_ms=183`, `trace_setup_ms=0`, `paint_draw_ms=15`,
  `paint_ms=199`, total `202984us`, checksum `sum32:32105444634193792`,
  `nonzero_pixels:8294400`.
- 8K: `framebuffer_init_ms=732`, `trace_setup_ms=0`, `paint_draw_ms=32`,
  `paint_ms=765`, total `768514us`, checksum
  `sum32:135445232233405312`, `nonzero_pixels:33177600`.

This keeps 300 DPI retina metadata, full physical size, and
`screen_size_reduced=false`. It is a native array-repeat optimization, not a
browser-only fill facade; the unsafe mutable Engine2D fill extern remains
blocked.

Tracked blocker:
`doc/08_tracking/bug/browser_layout_large_simd_fill_facade_unsafe_2026-07-09.md`.

## Verification

- `SIMPLE_LIB=src bin/simple test test/03_system/check/cpu_simd_render_scale_contract_spec.spl --mode=interpreter --clean`
  passed after the native/Rust array-repeat source contract: `4 examples, 0
  failures`.
- `cargo test -p simple-runtime test_array_repeat` passed: `1 passed`.
- `SIMPLE_LIB=src bin/simple test test/03_system/gui/wm_compare/backend_measurement_capture_spec.spl --mode=interpreter --clean`
  passed after the trace split: `25 examples, 0 failures`.
- Normal retained 8K CPU-SIMD row after adding the opt-in trace flag:
  `943683us`, checksum `sum32:135445232233405312`, full `7680x4320`,
  `gui_perf_benchmark_screen_size_reduced=false`.
- `sh scripts/audit/direct-env-runtime-guard.shs --working` and `--staged`
  passed.
- `find doc/06_spec -name '*_spec.spl' | wc -l` returned `0`.
