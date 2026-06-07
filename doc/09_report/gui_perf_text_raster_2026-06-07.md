 # GUI Text Raster Profile — 2026-06-07
  
  Focused Pure Simple text-raster smoke on host `dl`.
  
  Command shape:
  
  ```sh
  REPORT_PATH=build/gui_perf_bench/gui_perf_text_inline_128x96_<stamp>.md \
  BUILD_DIR=build/gui_perf_bench/text_inline_128x96 \
  SKIP_PROFILE_REPORT_CONTRACT=1 \
  tools/gui_perf_bench/run_all_benchmarks.shs --width 128 --height 96 --frames 3
  ```
  
  ## Result
  
  | Measurement | Before | After |
  |-------------|--------|-------|
  | `simple_web_software` p50 | 163856us | 127871us first post-fix run; 75097us in contract-backed report |
  | `simple_web_software` p95 | 164375us | 128289us first post-fix run; 75411us in contract-backed report |
  | checksum | `sum32:52601568094128` | `sum32:52601568094128` |
  | pixel proof | `nonzero_pixels:12288` | `nonzero_pixels:12288` |
  
  The improvement comes from mutating glyph pixels inside each text-line raster
  loop and returning the framebuffer once per line. The row still reports
  `runtime_execution_path: "engine2d-cpu_scalar"`, so this does not complete the
  larger bitmap/vector font GPU offload requirement.
  
  Follow-up native-first selection smoke on 2026-06-07 changed Simple Web
  render-safe auto from `cuda > vulkan > software > cpu_simd > cpu` to
  `metal > cuda > vulkan > software > cpu_simd > cpu`. On Linux host `dl`, Metal
  remained typed-unavailable and the latest rebased 128x96 / 3-frame profile
  still selected the explicit software text row with checksum
  `sum32:52601568094128`, pixel proof `nonzero_pixels:12288`,
  `p50_frame_us=80229`, and `p95_frame_us=80513`.
  This proves the native-first policy does not break the current fallback path;
  GPU font/vector offload is still open.
  
  2026-06-07 auto text-blit row: the GUI perf harness now also records
  `simple_web_auto`, which requests the Simple Web default backend instead of the
  explicit software baseline. On Linux host `dl`, auto selected CUDA and emitted
  generated-copy metadata (`generated_operation="simple_2d_copy_u32"`,
  `runtime_execution_path="generated_2d_kernel"`) with the same checksum and
  pixel proof as software. It was slower in the current stateless renderer shape:
  `p50_frame_us=3379248`, `p95_frame_us=3448332`, versus explicit software
  `p50_frame_us=86014`, `p95_frame_us=88266` in the same smoke. This is a real
  remaining blocker: text/glyph pixels are still CPU-prepared and the hardware
  path pays per-frame Engine2D/CUDA setup plus full-frame upload/readback instead
  of using a persistent GUI surface or generated glyph kernel.
  
  2026-06-07 static-frame cache follow-up: the render-loop exporters now reuse the
  existing `SimpleWebEngine2DStaticPixelCache` for repeated identical HTML frames.
  The first cache-aware profile recorded `simple_web_auto` as valid CUDA evidence
  with `static_pixel_cache_hits:3`, `p50_frame_us=11`, `p95_frame_us=19`, and a
  separate cold `artifact_build_us=3341716`, proving hardware setup/readback was
  the startup blocker.
  
  2026-06-07 stateless-auto follow-up: persistent GUI backend selection remains
  native-first, but stateless `render_html_to_pixels(..., "auto")` now uses the
  measured-fast software execution backend until Simple Web owns a persistent
  hardware surface. The canonical 128x96 / 3-frame profile records
  `simple_web_auto` as `backend_family="software"`, `cold_start_us=169477`,
  `p50_frame_us=14`, `p95_frame_us=26`, `static_pixel_cache_hits:3`,
  `static_pixel_cache_stores:1`, and unchanged checksum/proof. Explicit software
  recorded `cold_start_us=89537`, `p50_frame_us=7`, `p95_frame_us=16`. This fixes
  the stateless startup regression but does not complete bitmap/vector glyph
  offload for cold or dynamic text.
  
 2026-06-07 stylesheet startup follow-up: `compute_styles()` no longer reparses
 and rematches every `<style>` block once per node before applying the already
 extracted rule list. A focused 40-rule / 40-node Simple Web render at 96x96
 improved from `787368us` to `367032us`; checksum stayed
 `39568413652567`. This removes another pure-Simple O(nodes × stylesheet)
 startup cost, but it is not GPU font offload.
 
2026-06-07 child-link layout follow-up: recursive layout now builds
`first_child`/`next_sibling` arrays once after parsing instead of scanning the
full node arena for each container's children. A focused 180-sibling Simple Web
render at 96x96 improved from `494990us` to `472511us`; checksum stayed
`39574588256768`. This removes an O(containers × nodes) layout startup cost,
but cold/dynamic glyph pixels still need the generated GPU or compiled text
raster path.

2026-06-07 Draw IR text-contract follow-up: the HTML layout Draw IR path now
emits backend-consumable `text` commands for `#text` nodes with font metrics,
clip rect, parent id, and `font-rendering=bitmap-vector-backend-preferred`.
This is not a measured glyph-speedup yet; it is the pre-raster contract needed
for native/GPU bitmap or vector font backends to render text without changing
GUI or app code.

2026-06-07 Draw IR executor follow-up: `engine2d_draw_ir_adv_*` now consumes
that text contract by honoring command `font-size` instead of hardcoding 12px,
renders text through FontRenderer-backed blit buffers, and returns vector-font
offload status/reason plus explicit `font_gpu_glyph_returned` and
`font_production_ready` booleans. Current CPU evidence reports `cpu-fallback` /
`production-gpu-dispatch-not-wired`, so routing observes the rasterizer path but
production GPU glyph dispatch remains open.

2026-06-07 Draw IR text-cache follow-up: the text executor now keeps one
`TextBlitCache` per batch/composition and caches complete rendered text blit
buffers by text/color/background/font size. Repeated identical text commands now
avoid both new renderer construction and repeated glyph layout/blit preparation.
Focused unit evidence renders two repeated vector `A` text commands and asserts
one cache hit, one cache miss, and one vector-font accelerator attempt while both
commands render.

2026-06-07 Draw IR glyph-return evidence follow-up: the Draw IR result now
reports the positive backend-return state. A focused unit injects a validated
CUDA vector glyph through the existing glyph slot contract and asserts
`gpu-glyph-returned`, `font_gpu_glyph_returned=true`, and
`font_production_ready=true`. This proves the boundary can carry production
glyph-return evidence; real CUDA/HIP/Vulkan/Metal glyph kernels still need to
populate that contract in live GUI runs.

2026-06-07 bitmap fallback evidence follow-up: bitmap glyph fallback now routes
through an accelerated rasterizer contract and exposes bitmap accelerator stats.
A focused unit injects validated CUDA-returned bitmap glyph pixels and asserts
the returned alpha mask plus `cuda_hits=1`, `gpu_returned_glyphs=1`, and
`gpu_returned_glyph_pixels=1`. This proves bitmap glyphs can use the same
backend-return evidence shape; live production kernels still need to feed it.

2026-06-07 Draw IR bitmap-return follow-up: the Engine2D Draw IR executor now
resets and reads bitmap accelerator stats with vector stats. A focused unit
renders a non-vector `~` text command, injects validated CUDA bitmap glyph
pixels, and asserts `gpu-glyph-returned`,
`font_gpu_glyph_returned=true`, and `font_production_ready=true` from the Draw
IR result. This closes the bitmap visibility gap at the GUI text boundary; live
CUDA/HIP/Vulkan/Metal kernels still need to populate the contract.

Related tracked issue:
[`pure_simple_web_render_interpreter_bound_2026-06-06.md`](../08_tracking/bug/pure_simple_web_render_interpreter_bound_2026-06-06.md).
  
 Contract-backed full report:
 [`gui_perf_benchmark_2026-06-07.md`](gui_perf_benchmark_2026-06-07.md).
