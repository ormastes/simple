# REFUTED: the Vulkan web lane does NOT run per-document software-oracle sampling (macOS M4, 2026-09-12)

Status: **REFUTED BY MEASUREMENT.** The premise this record was opened to fix —
that a cold single render on the Vulkan lane pays an A/B sampling pass that
rasterizes the software oracle alongside the GPU route — is false as the lane is
actually configured. No probe-authorization mechanism was built, because there is
no per-document sampling to replace.

## The measurement

Level-gated stage counters were added to
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_layout_engine2d_fast.spl`
(`SIMPLE_WEB_ROUTE_STAGES=1`, read-only — they never change which route is
taken) and surfaced by `examples/06_io/ui/web_render_page_ppm.spl`:
oracle-raster ms/n, present+upload ms/n, GPU-route ms/n, consults, canonical
submissions, cached reuses.

Cold single render, `examples/06_io/ui/web_catalog/css-layout.html` at 300x253,
`SIMPLE_2D_BACKEND=vulkan SIMPLE_VK_READBACK=native SIMPLE_VK_IMAGE_UPLOAD=u32
SIMPLE_2D_BACKEND_STRICT=1 SIMPLE_EXECUTION_MODE=interpreter`, binary
`/Users/ormastes/simple/build/cargo-r2/release/simple`
(`backend_requested=vulkan backend_reported=vulkan`, so the native lane really
ran):

```
route_stages oracle_raster_ms=0 oracle_n=0 present_upload_ms=0 present_n=0 \
  gpu_route_ms=0 gpu_n=0 consults=0 canonical_submissions=0 cached_reuses=0
```

**`consults=0`.** `_web_draw_ir_choose_route` — the function that owns the
sampling A/B, `_web_draw_ir_upload_route` (software oracle + upload) and
`_web_draw_ir_oracle_route` — is never entered on this lane.

## Why, statically

Every call site of `_web_draw_ir_choose_route` is inside
`simple_web_layout_engine2d_fast.spl` and every one is guarded by
`web_gpu_paint_enabled()`; `grep -rn "web_draw_ir_gpu_route_sample\|_web_draw_ir_choose_route" src/lib src/app`
outside that file returns **zero** hits. And
`web_gpu_paint_enabled()`
(`simple_web_html_engine2d_presenter.spl:20-22`) is true only for
`SIMPLE_WEB_GPU_PAINT` in `{1,true,on}` — an env var this lane has never set,
in any run recorded by F19 or here. The route, its sampler, and its software
oracle are therefore dead code for every measurement in
`doc/10_metrics/ui/web_catalog_vulkan_per_op_attribution_macos_2026-09-12.md`.

Note `web_gpu_paint_mode()` returns `"gpu-first"` when the var is UNSET (only
an explicit `1`/`true`/`on` selects the `"measured"` sampling lane) — so the
default is the non-sampling mode, not the sampling one. That asymmetry is what
makes the premise easy to get wrong from reading the presenter alone.

## Where the cold-render floor actually is — bounded, NOT located

At 900x760 (control run, `SIMPLE_VK_TIMING=1`) the whole frame is **336 s** wall
and the Vulkan backend's own buckets sum to roughly **59 s**:

| bucket | n | total ms |
|---|---|---|
| font_composite | 23 | 54,103 |
| — of which font_atlas_pack_u32_to_u8 | 21 | 53,221 |
| rect | 550 | 1,285 |
| image_composite | 264 | 1,056 |
| image_blend | 262 | 858 |
| readback | 2 | 1,540 |

So **~277 s — 82% of the cold render — is host work OUTSIDE the Vulkan backend
entirely**: parse, style, layout, Draw IR construction and whatever host raster
the present path performs. That is a BOUND, not an attribution: this lane did not
instrument those stages and does not own the files that would be changed.

**An earlier draft of this record named
`simple_web_html_engine2d_presenter.spl:~597`
(`present_layout_pixels_with_engine2d_readback`) as the floor and prescribed an
exact edit to it. That was WRONG and has been removed.** Reading the function
shows it is an upload-and-read-back present, and its call from
`_web_draw_ir_upload_route` is on the dead sampler path proven above. It has
other callers, and they are dead here too: the same 300x253 run reports
`presenter_engine_cache creates=0 reuses=0`
(`web_presenter_engine_cache_create_attempt_count` /
`..._reuse_count`), so `present_layout_pixels_with_engine2d_readback` never
acquired an engine at all. **The presenter's present path is PROVEN not to run
on this lane, the 277 s is therefore somewhere in parse/style/layout/Draw IR,
and no edit to the presenter is prescribed here.** The next step
is to instrument the pre-backend stages the same way the route stages were
instrumented — cheap, one 300x253 run per hypothesis — before anyone changes a
line of the presenter.

Because that term is unlocated and outside this lane's files, **the <=100 s
target at 900x760 is MISSED** and is reported as missed.

## Kept

The stage counters are kept (level-gated, default off). They are the only way to
answer "did the route run" without a 3-minute bisect, and they are what refuted
this record's premise in one 300x253 run.
