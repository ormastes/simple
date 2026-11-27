# Interpreted Engine2D: cold glyph, image-scale and blend costs left after the full-res render fix

- **ID:** engine2d_interp_cold_glyph_and_image_scale_cost_2026-11-13
- **Status:** open
- **Severity:** P3 (interpreter-lane throughput; pixels are correct)
- **Found by:** follow-up profiling for
  `interpreted_engine2d_full_res_render_slow_2026-07-02`
- **Area:** `src/lib/common/encoding/sfnt_cmap.spl`,
  `src/lib/common/encoding/sfnt_glyf.spl`,
  `src/lib/gc_async_mut/gpu/engine2d/backend_emu_adv.spl`,
  `src/lib/gc_async_mut/gpu/engine2d/backend_software.spl`

## Measurements

Seed sha256 `af717f53d6bce3e511bfe81c5978b227976afd310d8a552bc8a7e88befb9ba4d`,
aarch64 DGX Spark, interpreter lane, 640x480 `cpu` backend, after the
2026-11-13 fix. Bench:
`E2D_RENDERS=6 bin/simple run test/05_perf/gui/bench_ui_draw_ir_pipeline_render.spl`
(10.0 s wall, compose 3.83 s for render 0 and 0.62 s for each later render).
Shares are from `SIMPLE_INTERP_SAMPLE=1`.

| cost | size | where |
|------|------|-------|
| glyph outline coverage | ~2.0 s once per process for 24 glyphs at 12 px | `_glyf_edge_coverage`, called per pixel per glyph from `sfnt_render_glyph_into` |
| cmap re-parse | ~21 ms per call, 2 calls per cold glyph (~1.0 s) | `sfnt_cmap_glyph_id` -> `parse_cmap_format12` materializes and validates every group on every lookup; reached through `has_glyph` and the codepoint measure pass in `FontRenderer.get_glyph` |
| image scale | ~150 ms per frame for one 638x60 destination | `_emu_scale_image_pixels`, per-pixel nearest-neighbour loop, no row reuse when consecutive rows share a source row |
| `draw_rect_blend` | ~29 s for one 640x480 call | `SoftwareBackend.draw_rect_blend` via `Engine2D.draw_rect_blend`; not on the widget pipeline's path |

## Also found

- `[u32].sum()` returns `0` under `SIMPLE_EXECUTION_MODE=interpret` and the
  correct sum under the JIT (307,201-element array, sum 1,315,452,251,706,038).
  This is why the readback checksum could not use it.

## Constraints for a fix

- Glyph bitmaps and frames must stay byte-identical; the bench prints a frame
  hash and writes a PPM (`E2D_PPM=<path>`) for `cmp`.
- `parse_cmap_format12` rejects the whole subtable when any group is out of
  order or out of range, and the caller then falls back to format 4. A lookup
  that skips that validation changes behaviour for malformed fonts.
- No cheap blob identity exists at the `sfnt_cmap` level; the callers in
  `font_renderer.spl` do have one (the rasterizer cache identity).

## Lane hazard: this pipeline is one import away from the JIT, where the bench crashes

The widget -> Draw-IR -> `cpu` Engine2D pipeline runs interpreted only because
the JIT refuses the module: `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl`
calls `env_get` (lines 2401, 3398, 3544, 3580, 3602, 3620) with no import, and
three definitions are co-compiled. Same class as
`sffi_vulkan_env_get_unimported_jit_demotion_2026-11-13`, which was fixed for
its own file on 2026-11-13.

With `use std.nogc_sync_mut.io.env_ops.{env_get}` added to `backend_vulkan.spl`
locally (not landed), the bench with `E2D_RENDERS=1`:

- JIT-compiles: 36.2 s wall against 6.8 s interpreted, 1,108,272 kB peak RSS
  against 660,064 kB;
- renders in 434 ms (compose 410 ms) against 4,967 ms;
- then exits with SIGSEGV (rc 139) before the frame-hash line prints.

The phase line printed, so the render loop itself completed; the fault is
between it and the frame-hash line, i.e. in the bench's own `frame_fnv` loop
over the result pixels or in formatting its value. Not narrowed further, nor
was it checked that the frame is pixel-identical on that lane. Until it is, adding
that import moves this pipeline and
`test/05_perf/gui/engine2d_interp_full_res_render_budget_spec.spl` onto an
unverified lane.

## Related

- `interp_indexed_array_store_regression_2026-11-11` (open): interpreted
  `[u32]` indexed stores are 75-130x slower than on the 2026-08-14 seed. The
  per-pixel store loops above (`_emu_scale_image_pixels`, the clipped/blend
  paths under `draw_rect_blend`) sit on that path, so part of their cost is
  that regression rather than the loop shape. Not separated here.

## Unexplained: warm compose 610 ms -> 880-1015 ms for four consecutive runs

Right after merging `release/1.0.0` into the fix branch (no change to any file
on this pipeline's path except eight `command.? == false` -> `== None` edits in
`draw_ir_adv.spl`), four consecutive 6-render bench runs measured warm compose
at 1015 / 922 / 876 / 966 ms instead of 610-622 ms, with cold compose and
readback unchanged. The sampler put the extra time in `load_selected_font_file`
(125 samples against 10; it wraps two `rt_file_hash_sha256` calls and one
read of the 1.7 MB NotoSansMono face per load). A back-to-back run of the
pre-merge commit in the same worktree measured 619 ms.

Reverting any one of the eight edits, appending a comment to the file, or
simply re-checking the file out brought it back to 607-627 ms, and the merged
tree as committed has measured 609-619 ms in every run since (six runs). So
the slow state was tied to that worktree state rather than to the source text.
Cause not found; recorded because it is a 50 % swing in the metric this bench
reports, and because a single post-merge run would have read as a regression.
