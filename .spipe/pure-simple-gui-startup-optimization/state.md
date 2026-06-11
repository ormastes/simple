# Feature: pure-simple-gui-startup-optimization

## Raw Request
$sp_dev optimize but do not heart feature of simple gui. fix perf bug o(n^2). and finde problems.. why pure simple backed gui is slow. however default pure simple 2d to use gui lib, platform native first(like metal) and cuda/hip and then vulkan... so on. if possible make order document and update guide and add logic to choose profer graphical backends. and offload most font rendering include vector font, and bitmap font. optimize them with pure simple(gpu). do not break feature or structure or change app code. fix perf of gui startup rendering

## Task Type
bug

## Refined Goal
Improve pure-Simple GUI startup rendering performance by removing verified O(n^2) renderer hotspots and documenting/enforcing the preferred graphical backend order without changing public GUI behavior or app code.

## Acceptance Criteria
- AC-1: Simple Web layout avoids repeated full-node child discovery during recursive layout and intrinsic width measurement, with focused integration coverage proving sibling order and software render output size stay stable.
- AC-2: Simple Web CSS style computation avoids running every selector rule against every node when rightmost selector buckets can safely narrow candidates, while preserving source-order cascade behavior with focused coverage.
- AC-3: Engine2D backend selection documents and tests the preferred order: native platform backends first, then Metal, CUDA, ROCm/HIP, Qualcomm, Vulkan, OpenCL, OpenGL, Intel, WebGPU, software, CPU SIMD, and CPU fallback as applicable to host capability.
- AC-4: Bitmap and vector font rendering work is not silently claimed as GPU-offloaded unless executable evidence proves the offload; current CPU glyph-buffer plus GPU upload behavior must be documented as such.
- AC-5: Every touched `.spl` source or spec in this lane is checked, covered by focused tests, mirrored into `doc/06_spec` when it is an SSpec, and scanned with `bin/simple run src/app/optimize/main.spl <file> --full --level=O3`.
- AC-6: Remaining startup/rendering bottlenecks that cannot be safely fixed in this lane are recorded under `doc/08_tracking/bug/` with concrete evidence and follow-up commands.

## Scope Exclusions
- Do not rewrite GUI features in C or Rust to claim performance parity.
- Do not change app-facing GUI APIs, HTML/CSS semantics, or renderer fallback behavior for speed.
- Do not fold unrelated dirty work from other active lanes into this lane.

## Phase
dev-done

## Log
- dev: Created state file with 6 acceptance criteria (type: bug).
- impl: Added one-time Simple Web child indexing, CSS rule candidate buckets,
  and paint ancestor-clip caching with focused SSpec coverage and tracking-doc
  updates.
- impl: Replaced CSS candidate selection-sort dedup with source-order bucket
  merging and folded widget panel/text detection into one paint pre-pass.
- impl: Avoided widget ancestor scratch allocation on non-widget paint paths by
  adding a panel-only fast path to `compute_widget_paint_flags(...)`.
- impl: Made the paint clip cache lazy so unclipped pages reuse one default
  framebuffer clip instead of allocating a per-node `ClipRect` cache.
- impl: Shared the intrinsic-width memo through recursive layout results so
  nested flex startup rendering no longer allocates a fresh `[-1; nodes.len()]`
  memo per non-column flex container; focused SSpec now passes 6/6.
- impl: Collapsed `build_child_index(...)` to a single guarded
  parent-before-child pass and removed Spark-reviewed dead selector helpers
  from the Simple Web layout renderer; focused SSpec still passes 6/6.
- impl: Added offscreen early returns and right-edge stop conditions to the
  active text range paint helpers, then removed Spark-reviewed dead non-range
  text wrappers from the renderer; focused SSpec still passes 6/6.
- impl: Moved final-pass `paint_clip_at(...)` lookups into the image/icon/text
  branches that actually need clips and removed dead unclipped glyph wrappers;
  focused SSpec still passes 6/6.
- impl: Made `build_text_render_cache(...)` preserve node-indexed arrays while
  computing font metrics only for `#text` nodes; focused SSpec still passes 6/6.
- impl: Removed the unused `char_widths` field and per-node fill path from
  `TextRenderCache`; focused SSpec still passes 6/6.
- impl: Hoisted normal text `paint_clip_at(...)` lookup from per wrapped line to
  once per text node; focused SSpec still passes 6/6.
- impl: Removed the `TextRenderCache` staging pass and compute text metrics
  directly in the filtered text paint branch; focused SSpec still passes 6/6.
- impl: Skipped repeated class-bucket lookups for duplicate class tokens while
  keeping source-order merge and selector matching intact; focused SSpec still
  passes 6/6.
- impl: Added zero-list and one-list fast paths to selector candidate bucket
  merging; focused SSpec still passes 6/6.
- plan: Split the remaining renderer cleanup into small independent parts and
  assigned the easy mechanical loop-length-hoist patch to Spark for
  `simple_web_html_layout_renderer.spl`; Codex keeps plan/state updates and
  final review/integration ownership.
- impl: Spark could not run because the Spark quota was exhausted, so Codex
  completed and reviewed the same easy slice locally by hoisting stable loop
  lengths in selector/style hot paths; focused check and SSpec still pass 6/6.
- verify: Renderer optimizer scan now reports 734 remaining opportunities
  after the mechanical loop-length hoists, with no `doc/06_spec` executable
  spec layout violations and clean whitespace diff.
- impl: Hoisted remaining stable collection/text lengths in Simple Web parse,
  selector, layout, paint, clip-cache, text-line, and Draw IR loops while
  leaving mutating collection builders unchanged.
- verify: Focused Simple Web layout SSpec still passes 6/6, adjacent
  Web Engine2D Metal-offload SSpec still passes 11/11, and the renderer
  optimizer scan now reports 692 remaining opportunities.
- impl: Replaced `zero_i32_list(...)` and `neg_one_i32_list(...)` push loops
  with repeated-list initialization for startup layout arrays.
- verify: A no-id/no-class CSS candidate merge fast path was tried and removed
  because it worsened the optimizer signal; the retained repeated-list cleanup
  keeps focused SSpecs green and lowers the renderer optimizer scan to 688
  remaining opportunities.
- impl: Replaced positive z-index painting's repeated full-node scans per
  distinct z layer with a lazy sorted positive-z index pass. Pages without
  positive z-index skip the index buffer; pages with positive z-index preserve
  ascending z order and document order for equal z values.
- verify: Added a focused overlapping absolute-position z-index pixel oracle;
  Simple Web layout SSpec now passes 7/7 and the adjacent Web Engine2D
  Metal-offload SSpec still passes 11/11. The renderer optimizer scan reports
  695 remaining opportunities because the new index buffer exposes additional
  bounds-check opportunities, but it removes the previous O(node_count *
  distinct_positive_z) full-node paint scan.
- impl: Moved background, absolute, and positive-z decoration clip lookups into
  the actual background/border draw branches so undecorated nodes do not resolve
  a paint clip during decoration passes.
- verify: Focused Simple Web layout SSpec still passes 7/7, adjacent Web
  Engine2D Metal-offload SSpec still passes 11/11, and the renderer optimizer
  scan remains at 695 remaining opportunities after the lazy decoration-clip
  lookup.
- impl: Confirmed wrap ranges are already computed only for `#text` layout
  nodes, then replaced the per-node `empty_i32_lists(...)` push loop used to
  seed wrap start/end arrays with repeated empty-list initialization.
- verify: Focused Simple Web layout SSpec still passes 7/7, adjacent Web
  Engine2D Metal-offload SSpec still passes 11/11, the focused spec optimizer
  scan reports 3 opportunities, and the renderer optimizer scan drops to 692
  remaining opportunities.
- impl: Converted `build_child_index(...)` and overflow clip-cache construction
  from grow-by-push loops to fixed-size repeated initialization with index
  assignment, using the already-known node count.
- verify: Focused Simple Web layout SSpec still passes 7/7, adjacent Web
  Engine2D Metal-offload SSpec still passes 11/11, the focused spec optimizer
  scan remains at 3 opportunities, and the renderer optimizer scan drops to 690
  remaining opportunities.
- impl: Replaced parser close-tag parent-stack copy allocation with an in-place
  pop-based trim to the matched opening tag, preserving the existing tolerant
  close-tag behavior.
- verify: Focused Simple Web layout SSpec still passes 7/7, adjacent Web
  Engine2D Metal-offload SSpec still passes 11/11, and the renderer optimizer
  scan drops to 687 remaining opportunities.
- impl: Avoided `class_attr.split(" ")` for elements without a class attribute,
  leaving their `class_words` empty and preserving the existing non-empty class
  path.
- verify: Added an empty-class selector oracle; focused Simple Web layout SSpec
  now passes 8/8, adjacent Web Engine2D Metal-offload SSpec still passes 11/11,
  docgen refreshed the mirrored manual, and the renderer optimizer scan remains
  at 687 remaining opportunities.
- plan: Split the next easy parser cleanup to Spark: gate widget/focus class
  flag substring scans behind the existing non-empty class branch, then Codex
  reviews the patch and updates evidence.
- impl: Spark was unavailable due quota exhaustion, so Codex completed the same
  one-file parser slice locally. Unclassed elements now skip the six
  `class_contains(...)` scans and keep the default false flags from `mk_node`.
- verify: Focused check passes for the renderer and Simple Web layout SSpec,
  focused Simple Web layout SSpec still passes 8/8, adjacent Web Engine2D
  Metal-offload SSpec still passes 11/11, `doc/06_spec` executable spec count
  remains 0, SPipe dev-command wiring reports PASS, whitespace diff is clean,
  and the renderer optimizer scan remains at 687 opportunities.
- impl: Replaced the flex-wrap layout pass's grow-by-push `line_heights`
  builder with a fixed-size buffer bounded by the flex child count plus an
  explicit `line_count`. This removes dynamic line-height list growth while
  preserving wrap and wrap-reverse line lookup behavior.
- verify: Added a focused flex-wrap layout oracle for first-line and second-line
  child y positions. Focused Simple Web layout SSpec now passes 9/9, adjacent
  Web Engine2D Metal-offload SSpec still passes 11/11, docgen refreshed the
  mirrored manual, focused spec optimizer scan remains at 3 opportunities,
  `doc/06_spec` executable spec count remains 0, SPipe dev-command wiring
  reports PASS, and whitespace diff is clean. The renderer optimizer scan
  reports 688 opportunities: this is a static-count tradeoff from the fixed
  buffer's indexed assignments while removing the flex-wrap push-growth path.
- impl: Replaced two known-size startup builders with fixed-size arrays:
  selector group part lists are now assigned by group index, and computed style
  output is seeded to `node_count` then assigned by node index. Parent style
  inheritance still uses parser order, so behavior remains parent-before-child.
- verify: Focused renderer check passes, focused Simple Web layout SSpec still
  passes 9/9, adjacent Web Engine2D Metal-offload SSpec still passes 11/11,
  focused spec optimizer scan remains at 3 opportunities, `doc/06_spec`
  executable spec count remains 0, SPipe dev-command wiring reports PASS,
  whitespace diff is clean, and the renderer optimizer scan returns to 687
  opportunities after removing the selector/style push-growth warnings.
- impl: Replaced CSS rule candidate-list growth with a fixed buffer sized to
  fallback plus optional id, tag, and class buckets, then routed merging through
  a count-aware merge helper. Removed the now-dead append and wrapper merge
  helpers after reference checks.
- verify: Focused renderer check passes, focused Simple Web layout SSpec still
  passes 9/9, adjacent Web Engine2D Metal-offload SSpec still passes 11/11,
  focused spec optimizer scan remains at 3 opportunities, `doc/06_spec`
  executable spec count remains 0, SPipe dev-command wiring reports PASS,
  whitespace diff is clean, and the renderer optimizer scan remains at 687
  opportunities while the candidate-list push path is gone.
- impl: Tightened Engine2D backend priority numbering so it exactly matches the
  documented/default GUI order: metal, cuda, rocm/hip, qualcomm, vulkan,
  opencl, opengl, intel, webgpu, software, cpu_simd, cpu. The prior helper had
  an OpenCL/OpenGL tie and compressed lower-priority values even though the
  default order list was already correct.
- verify: Extended the backend-order unit spec to assert every adjacent
  priority edge, regenerated the mirrored manual, and verified backend-order
  spec 4/4, adjacent WebGPU unit spec 5/5, adjacent Web Engine2D Metal-offload
  spec 11/11, helper optimizer scan at 50 opportunities, backend-order spec
  optimizer scan at 12 opportunities, `doc/06_spec` executable spec count 0,
  SPipe dev-command wiring PASS, and whitespace diff clean.
- impl: Added typed bitmap-font offload evidence alongside the existing
  vector-font evidence. `BitmapFontOffloadEvidence` records generated copy
  readiness, CPU glyph preprocessing, GPU copy/upload readiness, and explicitly
  keeps `gpu_glyph_rasterized = false` until a real GPU bitmap glyph raster
  path exists.
- verify: Added and generated a focused bitmap-font offload SSpec manual.
  Bitmap-font offload spec passes 3/3, vector-font offload spec passes 4/4,
  generated-kernel dispatch spec passes 23/23, bitmap evidence module optimizer
  scan reports 7 opportunities, bitmap spec optimizer scan reports 0
  opportunities, `doc/06_spec` executable spec count remains 0, SPipe
  dev-command wiring reports PASS, and whitespace diff is clean.
- docs: Updated the Engine2D module overview, UI stack architecture, and pixel
  comparison guide so the typed vector-font and bitmap-font evidence surfaces
  are discoverable. The docs now state that bitmap-font evidence means CPU
  glyph preprocessing plus optional GPU copy/upload, not GPU-side bitmap glyph
  rasterization.
- verify: Engine2D module/bitmap evidence check passes, bitmap-font offload spec
  remains 3/3, vector-font offload spec remains 4/4, bitmap evidence module
  optimizer scan remains at 7 opportunities, `doc/06_spec` executable spec
  count remains 0, SPipe dev-command wiring reports PASS, and whitespace diff is
  clean.
- impl: Optimized OpenCL bitmap-text fallback paths. `OpenClBackend.draw_text`
  and `draw_text_bg` now route directly to the mirror renderer when device
  drawing is unavailable, avoiding temporary CPU glyph-buffer construction for a
  GPU copy/upload path that cannot run.
- verify: Added and generated a focused OpenCL text fallback SSpec. Backend
  OpenCL text fallback spec passes 2/2, helpers text spec passes 4/4,
  generated-kernel dispatch spec passes 23/23, OpenCL backend optimizer scan
  reports 74 opportunities, OpenCL text fallback spec optimizer scan reports 0
  opportunities, `doc/06_spec` executable spec count remains 0, SPipe
  dev-command wiring reports PASS, and whitespace diff is clean. The broader
  pre-existing `backend_opencl_facade_spec.spl` still reports 4 passed / 2
  failed even after removing speculative added assertions, so it was not used as
  acceptance evidence for this slice.
- impl: Optimized CUDA bitmap-text fallback paths. `CudaBackend.draw_text` and
  `CudaBackend.draw_text_bg` now route directly to the mirror renderer when the
  CUDA backend is uninitialized, avoiding temporary CPU glyph-buffer
  construction for a CUDA upload path that cannot run.
- verify: Added and generated a focused CUDA text fallback SSpec. Backend CUDA
  text fallback spec passes 2/2, helpers text spec passes 4/4, generated-kernel
  dispatch spec passes 23/23, CUDA backend optimizer scan reports 70
  opportunities, CUDA extension optimizer scan reports 7 opportunities, CUDA
  text fallback spec optimizer scan reports 0 opportunities. The broader
  pre-existing `backend_cuda_renderbackend_spec.spl` was not used as acceptance
  evidence because it currently reports 9 passed / 2 failed in this checkout and
  also imports `cuda_2d_ptx_source` through a non-exporting module during
  `check`.
- impl: Optimized ROCm/HIP bitmap-text fallback paths. `RocmBackend.draw_text`
  and `draw_text_bg` now return before constructing foreground/background text
  buffers when the ROCm backend is uninitialized, preserving the existing dirty
  attempted-draw state without staging glyphs for a HIP upload path that cannot
  run.
- verify: Added and generated a focused ROCm text fallback SSpec. Backend ROCm
  text fallback spec passes 2/2, helpers text spec passes 4/4, ROCm session
  contract spec passes 8/8, ROCm backend optimizer scan reports 53
  opportunities, and ROCm text fallback spec optimizer scan reports 0
  opportunities. `bin/simple check` passes for the touched ROCm source/spec and
  adjacent specs with the existing `gc_boundary_crossing` warning on
  `backend_rocm.spl`'s SFFI import.
- impl: Optimized Vulkan bitmap-text fallback paths. `VulkanBackend` now returns
  before foreground text CPU-render/upload work when uninitialized, and
  `draw_text_bg` returns before constructing a background text buffer when
  Vulkan cannot upload it. Both paths preserve the dirty attempted-draw state.
- verify: Added and generated a focused Vulkan text fallback SSpec. Backend
  Vulkan text fallback spec passes 2/2, helpers text spec passes 4/4, Vulkan
  backend optimizer scan reports 45 opportunities, Vulkan helper optimizer scan
  reports 63 opportunities, and Vulkan text fallback spec optimizer scan reports
  0 opportunities. `bin/simple check` passes for the touched Vulkan source/spec
  and adjacent specs with the existing `gc_boundary_crossing` warnings on the
  Vulkan SFFI imports.
- impl: Optimized OpenGL bitmap-text fallback paths. `OpenGLBackend.draw_text`
  and `draw_text_bg` now return before constructing foreground/background text
  buffers when the OpenGL backend is uninitialized, avoiding CPU glyph work for
  an upload path with no valid GL context.
- verify: Added and generated a focused OpenGL text fallback SSpec. Backend
  OpenGL text fallback spec passes 2/2, helpers text spec passes 4/4, OpenGL
  backend optimizer scan reports 22 opportunities, and OpenGL text fallback spec
  optimizer scan reports 0 opportunities. `bin/simple check` passes for the
  touched OpenGL source/spec and adjacent helper spec.
- impl: Optimized Intel oneAPI bitmap-text fallback paths. `IntelBackend` now
  returns before foreground CPU text render/upload work and background text
  buffer construction when uninitialized, preserving the dirty attempted-draw
  state. `draw_text_bg` also seeds its known-size background buffer directly
  instead of growing it with repeated `push`.
- verify: Added and generated a focused Intel text fallback SSpec. Backend
  Intel text fallback spec passes 2/2, helpers text spec passes 4/4, Intel
  backend optimizer scan reports 26 opportunities after removing the
  preallocation warning, Intel helper optimizer scan reports 34 opportunities,
  and Intel text fallback spec optimizer scan reports 0 opportunities.
  `bin/simple check` passes for the touched Intel source/spec and adjacent
  helper spec.
- impl: Optimized WebGPU pre-init bitmap-text paths. `WebGpuBackend.draw_text`
  and `draw_text_bg` now return before constructing foreground/background text
  buffers when the backend has not been initialized or has zero dimensions,
  while initialized CPU-parity drawing remains unchanged.
- verify: Added and generated a focused WebGPU text fallback SSpec. Backend
  WebGPU text fallback spec passes 2/2, existing WebGPU behavior spec remains
  5/5, helpers text spec passes 4/4, WebGPU backend optimizer scan reports 69
  opportunities, and WebGPU text fallback spec optimizer scan reports 0
  opportunities. `bin/simple check` passes for the touched WebGPU source/spec
  and adjacent specs with the existing `gc_boundary_crossing` warning on the
  WebGPU SFFI import.
- impl: Optimized the pure Simple software fallback path by hoisting repeated
  dirty-tile and `draw_text` length checks in `SoftwareBackend`, and by caching
  the AA text helper buffer length outside the innermost blend loop.
- verify: Focused software/text checks pass: helpers text spec 4/4, software
  primitive spec 6/6, software SIMD spec 7/7. `bin/simple check` passes for the
  touched software/text helper sources and focused specs. Software backend
  optimizer scan dropped from 90 to 87 opportunities after removing the three
  `hoist_len_call` warnings; helpers text optimizer scan remains at 37
  opportunities, and helpers text spec optimizer scan reports 10 opportunities.
  The broader pre-existing `draw_text_bg_spec.spl` currently reports 1 passed /
  2 failed and was not used as acceptance evidence for this loop-hoist slice.
- impl: Resolved the CPU `draw_text_bg` spec failure by replacing stale
  `to_be_true()` matcher calls with the supported `to_be(true)` matcher form.
  Diagnostic probes showed the renderer already preserved outside pixels,
  changed inside glyph-cell pixels, and produced intermediate AA red coverage;
  the failure was in the matcher path, not the pixel implementation.
- verify: CPU `draw_text_bg` spec now passes 3/3 and its mirrored manual was
  regenerated. Adjacent helpers text spec passes 4/4 and software primitive spec
  passes 6/6. Optimizer scans report: `draw_text_bg_spec.spl` 9 opportunities,
  software backend 87 opportunities, helpers text 37 opportunities.
- plan: Split the next Engine2D text-helper optimization into small owned
  packets in the shared UI/GPU rollout plan. Spark was assigned the easy
  documentation/evidence bookkeeping slice, but the Spark agent errored on quota
  before producing output, so there was no subagent patch to review. Codex
  completed the small plan-doc fallback locally and kept source edits separate.
- impl: Hoisted loop-invariant AA text helper work in `text_aa_blit_buffer(...)`:
  cached the float scale conversion, cached glyph pixel width, and moved row
  sample-y computation out of the inner pixel loop while preserving glyph
  sampling and blend behavior.
- verify: Focused helper/text checks pass. `bin/simple check` passes for
  `helpers_text.spl`, helpers text spec, CPU draw_text_bg spec, and software
  primitive spec. Focused SSpecs pass: helpers text 4/4, CPU draw_text_bg 3/3,
  software primitive 6/6. The helpers text optimizer scan remains at 37
  opportunities after this micro-hoist; the change removes repeated inner-loop
  float conversion/row math that the static opportunity count does not reduce.
- impl: Tightened the AA text helper padding path. `text_aa_blit_buffer(...)`
  still returns a payload as tall as the requested font size, but it now samples
  only the real glyph raster height and leaves any bottom padding rows at the
  prefilled background color instead of running bilinear glyph sampling over
  rows that can only produce zero coverage.
- verify: Added and regenerated a helpers-text SSpec scenario proving AA
  padding rows stay background-only for a 16px payload with a 14px scaled bitmap
  glyph raster. Focused checks pass for helpers text, software backend, helpers
  text spec, CPU draw_text_bg spec, and software primitive spec. Focused SSpecs
  pass: helpers text 5/5, CPU draw_text_bg 3/3, software primitive 6/6. The
  helpers text optimizer scan remains at 37 opportunities, and the helpers text
  spec optimizer scan reports 10 MIR-only opportunities with no general-pattern
  findings after hoisting the prior `.len()` loop conditions.
- impl: Optimized the pure Simple software fallback blit/readback loops.
  `SoftwareBackend.draw_image(...)` now caches the source pixel length once per
  image blit instead of recomputing it for every clipped row, and
  `read_pixels()` caches the framebuffer pixel count for allocation and copy
  loop bounds.
- verify: Focused software fallback checks pass after the blit/readback hoists:
  software primitive spec 6/6, software SIMD spec 7/7, helpers text spec 5/5,
  and CPU draw_text_bg spec 3/3. `bin/simple check` passes for the touched
  software backend, primitive spec, SIMD spec, helpers text spec, and CPU
  draw_text_bg spec. Software backend optimizer scan remains at 87
  opportunities, while the primitive spec optimizer scan drops from 10 to 9
  opportunities and has no general-pattern findings after hoisting its
  readback loop length; the mirrored primitive manual was regenerated.
- impl: Added a common-case direct framebuffer path to
  `SoftwareBackend.draw_text(...)`. When no clip and no mask are active, glyph
  pixels now use direct bounds-checked buffer writes and dirty-tile marking
  instead of routing every scaled glyph pixel through `sw_set_pixel(...)` and
  repeating clip/mask checks. The existing `sw_set_pixel(...)` path remains in
  use whenever clipping or masking is active.
- verify: Added and regenerated a software primitive SSpec scenario proving
  `draw_text(...)` still respects active clip bounds. Focused checks pass for
  the software backend, primitive spec, SIMD spec, helpers text spec, and CPU
  draw_text_bg spec. Focused SSpecs pass: software primitive 7/7, software SIMD
  7/7, and CPU draw_text_bg 3/3. The software backend optimizer scan reports 88
  MIR-only opportunities after this fast path because the direct branch exposes
  additional static bounds-check sites, but it removes per-glyph-pixel method
  dispatch and clip/mask checks from the no-clip/no-mask startup text path.
- impl: Tightened the same no-clip/no-mask `draw_text(...)` fast path so each
  scaled glyph bit writes a clipped horizontal run and calls
  `mark_span_dirty(...)` once per output row instead of calling
  `mark_pixel_dirty(...)` for every scaled pixel in that run. The clipped/masked
  path still routes through `sw_set_pixel(...)`.
- verify: Focused software/text checks still pass after run-level dirty marking:
  software primitive spec 7/7, software SIMD spec 7/7, and CPU draw_text_bg spec
  3/3. `bin/simple check` passes for the touched software backend and adjacent
  text/software specs. The software backend optimizer scan reports 89 MIR-only
  opportunities because the direct branch exposes additional static
  bounds-check sites, but the runtime path now avoids repeated per-pixel dirty
  tile division/marking for no-clip/no-mask scaled text.
- impl: Hoisted no-clip/no-mask `draw_text(...)` glyph-run coordinates that are
  invariant across scaled rows. `run_x` and the glyph row base are computed once
  per source glyph bit instead of for every scaled output row.
- verify: Focused software/text checks still pass after the coordinate hoist:
  software primitive spec 7/7, software SIMD spec 7/7, and CPU draw_text_bg spec
  3/3. `bin/simple check` passes for the touched software backend and adjacent
  text/software specs. The software backend optimizer summary remains at 89
  MIR-only opportunities.
- impl: Moved the no-clip/no-mask `draw_text(...)` fast-path branch outside the
  scaled-row loop. The direct framebuffer path and clipped/masked fallback now
  each own their row loop, so startup text rendering does not retest
  `fast_direct` for every scaled output row.
- verify: Focused software/text checks still pass after the branch split:
  software primitive spec 7/7, software SIMD spec 7/7, and CPU draw_text_bg spec
  3/3. `bin/simple check` passes for the touched software backend and adjacent
  text/software specs. The software backend optimizer summary reports 90
  MIR-only opportunities because the split exposes additional static branch and
  bounds-check sites, but it removes a repeated branch from the hot no-clip/no-mask
  glyph-row loop.
- impl: Hoisted the mask-active check in `sw_hline(...)` and
  `sw_hline_blend(...)` so common span drawing computes `self.mask_buf.len() >
  0` once per span before choosing the masked fallback or direct SIMD-friendly
  fill/blend path.
- verify: Focused software span checks still pass: software primitive spec 7/7
  and software SIMD spec 7/7. `bin/simple check` passes for the touched software
  backend and adjacent software specs. The software backend optimizer summary
  remains at 90 MIR-only opportunities.
- impl: Hoisted stable values in `SoftwareBackend.draw_rect_filled(...)` for
  the opaque common path: row end, clip bounds, mask-active state, and row base
  are now computed outside the per-pixel fill loop where possible while keeping
  alpha fills routed through `sw_hline_blend(...)`.
- verify: Focused software/rectangle checks still pass after the rectangle-fill
  hoists: software primitive spec 7/7, software SIMD spec 7/7, and CPU
  draw_text_bg spec 3/3. `bin/simple check` passes for the touched software
  backend and adjacent text/software specs. The software backend optimizer
  summary remains at 90 MIR-only opportunities.
- impl: Split `SoftwareBackend.draw_rect_filled(...)` into separate alpha and
  opaque loops. Alpha rectangles still delegate to `sw_hline_blend(...)`, while
  the opaque startup fill path no longer checks `has_alpha` on every row.
- verify: Focused software/rectangle checks still pass after the alpha/opaque
  loop split: software primitive spec 7/7, software SIMD spec 7/7, and CPU
  draw_text_bg spec 3/3. `bin/simple check` passes for the touched software
  backend and adjacent text/software specs. The software backend optimizer
  summary reports 92 MIR-only opportunities because the loop split exposes
  additional static branch/bounds-check sites, but it removes the repeated
  per-row alpha branch from the opaque rectangle fill path.
- impl: Pre-clipped the opaque `draw_rect_filled(...)` rectangle once per call.
  The opaque path now computes x/y framebuffer and active-clip bounds before
  the row loop, then iterates only drawable rows and columns. Masked opaque
  fills still route each pixel through `sw_set_pixel(...)`; alpha fills still
  route through `sw_hline_blend(...)`.
- verify: Added and regenerated a focused software primitive SSpec proving
  `draw_rect_filled(...)` respects active clip bounds. Focused checks pass:
  software primitive spec 8/8, software SIMD spec 7/7, and CPU draw_text_bg spec
  3/3. `bin/simple check` passes for the touched software backend and adjacent
  text/software specs. The software backend optimizer summary reports 93
  MIR-only opportunities and the primitive spec optimizer summary reports 13
  opportunities after adding the clip regression scenario.
- impl: Optimized software backend startup initialization by replacing the
  per-pixel `rgb(0, 0, 0)` call in `SoftwareBackend.init(...)` with a single
  precomputed `0xff000000u32` opaque-black value used by the framebuffer fill
  loop.
- verify: Focused startup/fill checks still pass after the init-fill constant:
  software primitive spec 8/8, software SIMD spec 7/7, and CPU draw_text_bg spec
  3/3. `bin/simple check` passes for the touched software backend and adjacent
  text/software specs. The software backend optimizer summary remains at 93
  MIR-only opportunities.
- impl: Removed the now-unused `rgb` import from `backend_software.spl` after
  the startup framebuffer fill switched to a precomputed opaque-black constant.
- verify: Focused software checks still pass after the import cleanup:
  software primitive spec 8/8 and software SIMD spec 7/7. `bin/simple check`
  passes for the touched software backend and adjacent text/software specs. The
  software backend optimizer summary remains at 93 MIR-only opportunities.
- impl: Removed now-unused `glyph_height` and `glyph_advance` imports from
  `backend_software.spl`; `draw_text(...)` uses `text_metrics(...)` for those
  values and imports only `glyph_data` directly.
- verify: Focused software checks still pass after the glyph import cleanup:
  software primitive spec 8/8 and software SIMD spec 7/7. `bin/simple check`
  passes for the touched software backend and adjacent text/software specs. The
  software backend optimizer summary remains at 93 MIR-only opportunities.
- review: Split the latest risky backend edits into a small read-only explorer
  task. Spark was requested first for the easy review but hit its model usage
  limit, so the same bounded review was rerun with the default explorer. The
  explorer found no behavior bug in the no-clip `draw_text(...)` fast path or
  opaque `draw_rect_filled(...)` preclip/split, and identified one residual
  coverage gap: offscreen clipping on the no-clip text fast path.
- test: Added `draw_text clips offscreen spans on the fast path` to the
  software primitive spec. It compares fully in-bounds text with left-edge and
  right-edge partially offscreen draws, proving the direct framebuffer path
  writes visible glyph pixels while trimming clipped spans.
- verify: Regenerated the primitive spec manual under `doc/06_spec`; docgen
  completed with the pre-existing export/generic warnings and generated-stub
  summary. Focused primitive spec now passes 9/9 with the offscreen text
  fast-path coverage.
- impl: Optimized the shared text payload raster path in `helpers_text.spl`.
  `text_render_metrics_to_buf(...)` now relies on metrics-derived buffer
  dimensions and hoists the glyph destination row base instead of recomputing
  `px`, `py`, and defensive index checks for every scaled glyph pixel.
  `text_aa_blit_buffer(...)` similarly avoids the redundant per-pixel buffer
  length guard after deriving `dst_x` from the same bounded glyph loop and text
  width.
- verify: Baseline `helpers_text_spec.spl` passed 5/5 before the edit and
  remains 5/5 after the edit. `bin/simple check` passes for
  `helpers_text.spl` and its spec. The optimizer scanner reports 37 static
  opportunities before and after; runtime work is still reduced by removing
  repeated hot-loop branches and unused `buf_len` locals.
- impl: Fixed the pure-Simple Simple Web child-index startup O(n^2) shape in
  `simple_web_html_layout_renderer.spl`. `build_child_index(...)` no longer
  copies and reassigns a growing `children[parent]` array for every sibling.
  It now builds `first_child`, `next_sibling`, and `child_count` arrays in one
  pass, preserving source-order traversal through `HtmlChildIndex.children_of`.
- verify: Baseline `simple_web_layout_child_index_spec.spl` passed 9/9 before
  the edit and remains 9/9 after the linked child-index change. `bin/simple
  check` passes for the renderer and its integration spec. The optimizer
  scanner reports 699 static opportunities after the edit; the count rises
  because `children_of(...)` materializes a requested child list with push, but
  the startup index builder is now linear instead of copying every sibling list
  append.
- impl: Removed the remaining Simple Web child-list materialization from hot
  layout traversal. `layout(...)` and `intrinsic_text_width(...)` now walk
  `HtmlChildIndex.first_child` / `next_sibling` directly for block, contents,
  row-flex, wrap-flex, column-flex, baseline, and intrinsic-width passes. The
  unused `children_of(...)` materializer was deleted, so sibling-heavy startup
  layout no longer allocates per-parent child arrays after building the linked
  index.
- verify: `simple_web_layout_child_index_spec.spl` still passes 9/9 and
  `bin/simple check` passes for the renderer plus integration spec. The
  optimizer scanner reports 700 static opportunities after deleting the
  materializer; remaining preallocate-collection notices are unrelated
  wrap/command buffers, not child-index construction or traversal.
- impl: Optimized text-wrap range construction in
  `simple_web_html_layout_renderer.spl`. `compute_wrap_ranges(...)` now counts
  wrapped lines first, allocates fixed-size `starts` and `ends` arrays, and
  fills them by index instead of dynamically pushing both arrays during text
  node layout. Empty text still returns a single `[0]` start/end range.
- verify: `simple_web_layout_child_index_spec.spl` remains 9/9 and
  `bin/simple check` passes for the renderer plus integration spec. The
  optimizer scanner now reports the next remaining preallocate notices in CSS
  bucket and Draw IR command collection; the text-wrap range push warnings are
  removed from the scanner tail.
- test: Added Simple Web Draw IR coverage to
  `simple_web_layout_child_index_spec.spl` through the public
  `simple_web_layout_render_html_draw_ir(...)` entrypoint. The scenario asserts
  that visible HTML boxes produce one batch with nonzero commands.
- impl: Optimized `_html_draw_ir_commands(...)` in
  `simple_web_html_layout_renderer.spl`. The command builder now counts visible
  boxes first, creates a fixed-size `[DrawIrCommand]`, and fills commands by
  index instead of growing the command list with `push` for every visible node.
- verify: `simple_web_layout_child_index_spec.spl` now passes 10/10, and
  `bin/simple check` passes for the renderer plus integration spec. The
  renderer optimizer tail no longer reports the Draw IR command collection
  push; remaining preallocate notices are in CSS rule bucket construction.
- impl: Optimized CSS rule bucket construction in
  `simple_web_html_layout_renderer.spl`. `build_rule_buckets(...)` now counts
  selector keys and bucket sizes first, allocates exact-size id/class/tag and
  fallback rule arrays, and fills them by index instead of growing rule buckets
  with repeated `push` calls during startup style setup.
- verify: `simple_web_layout_child_index_spec.spl` remains 10/10, and
  `bin/simple check` passes for the renderer plus integration spec. The
  renderer optimizer tail moved past `build_rule_buckets(...)`; remaining
  preallocate notices are earlier generic helper/list construction sites. The
  total static count is 735 because the fixed-size helper passes expose extra
  bounds-check/MIR opportunities while removing the dynamic CSS bucket growth
  path.
- impl: Removed the remaining dynamic growth in CSS candidate merge and
  selector group splitting. `merge_sorted_rule_lists_unique_count(...)` now
  counts unique source-order candidates first and fills a fixed result array;
  `split_selector_groups(...)` counts top-level comma groups first and fills a
  fixed text array while preserving the previous empty-before-comma and
  no-trailing-empty behavior.
- verify: Docker-isolated focused renderer check passes, and
  `simple_web_layout_child_index_spec.spl` remains 10/10. The renderer
  optimizer tail no longer reports CSS bucket, selector-group, or candidate
  merge collection growth; the only remaining `preallocate_collection` tail
  warning is the parser arena at `parse_html(...)`. That parser path was left
  unchanged because replacing `nodes.push(...)` safely would require a
  pre-count pass over the HTML or a reserve-capacity API, and a second full
  parse pass could hurt startup more than the static warning helps.
- verify: Re-ran focused backend-order and font/offload evidence in Docker.
  `bin/simple check` passes for helpers availability, bitmap-font offload,
  Intel backend/kernel, WebGPU backend, backend-order spec, bitmap-font spec,
  Intel text fallback spec, and WebGPU text fallback spec; the only warning is
  the existing WebGPU SFFI `gc_boundary_crossing`. Specs pass: backend-order
  4/4, bitmap-font offload 3/3, Intel text fallback 2/2, and WebGPU text
  fallback 2/2. Optimizer scans report helpers availability 50, bitmap-font
  offload 7, Intel backend 26, Intel kernels 34, WebGPU backend 69,
  backend-order spec 12, and zero opportunities for bitmap-font, Intel text
  fallback, and WebGPU text fallback specs.
- impl: Added a first-class generated Engine2D bitmap glyph raster operation.
  `generated_kernel_dispatch.spl` now exposes `bitmap_glyph_raster` with the
  `simple_2d_bitmap_glyph_raster_u32` entry and a glyph-oriented args layout.
  `bitmap_font_offload.spl` keeps the existing CPU glyph + GPU copy evidence
  but also records whether a GPU bitmap glyph raster launch plan is available.
  The evidence still refuses to mark bitmap font production-ready until real
  device execution/readback proves glyph pixels came from the GPU.
- verify: Focused generated-dispatch and bitmap-font checks pass, and specs
  pass: generated-kernel dispatch 23/23 and bitmap-font offload 3/3. Generated
  manuals were refreshed under `doc/06_spec`. This moves bitmap-font offload
  beyond copy/upload provenance without pretending that readback-verified
  GPU-side glyph rasterization exists yet.
- impl: Added generated bitmap glyph raster source/export contracts to the
  portable compute emitter and Engine2D OpenCL/HIP source strings. The compiler
  required-symbol gate now rejects generated 2D artifacts that omit
  `simple_2d_bitmap_glyph_raster_u32`, and bitmap glyph operations no longer
  report CPU preprocessing as required at the operation-metadata layer.
- verify: Focused checks pass for the compiler emitter, OpenCL/HIP backend
  source strings, and updated contract specs. Specs pass: portable compute
  24/24, generated 2D contract 2/2, HIP contract 5/5, OpenCL contract 19/19,
  and ROCm session contract 8/8. `backend_opencl_facade_spec.spl` still has the
  same host-dependent pre-existing result as baseline, 4 passed / 2 failed, so
  it is not used as acceptance evidence for this slice.
- verify: Optimizer scans completed for all touched `.spl` files. Counts:
  portable compute 100, OpenCL backend 76, ROCm kernel source 21, portable
  compute spec 43, generated 2D contract spec 0, HIP contract spec 0, OpenCL
  contract spec 90, OpenCL facade spec 29, and ROCm session contract spec 2
  remaining static opportunities.
- impl: Added OpenCL generated bitmap glyph raster launch binding.
  `OpenClSession.launch_generated_2d(...)` now routes
  `bitmap_glyph_raster` through a typed packed-args binder that reads
  glyph-bits, destination, width, height, glyph count, font size, and color,
  validates dimensions, binds all seven OpenCL kernel args, and submits through
  the generated launch plan. `generated_kernel_dispatch.spl` also lists
  `simple_2d_bitmap_glyph_raster_u32` in module-wide required entries.
- verify: Focused generated-dispatch and OpenCL session checks pass. Specs
  pass: generated-kernel dispatch 23/23 and OpenCL session contract 9/9.
  Generated manuals were refreshed under `doc/06_spec`. This proves OpenCL
  argument binding and fail-closed validation, not readback-verified GPU glyph
  pixels.
- verify: Optimizer scans completed for this slice. Counts: generated kernel
  dispatch 105, OpenCL session 152, generated dispatch spec 0, and OpenCL
  session contract spec 0 remaining static opportunities.
- impl: Added HIP/ROCm generated bitmap glyph raster launch preflight.
  `RocmSession.launch_generated_2d(...)` now validates the same packed
  glyph-bits, destination, width, height, glyph count, and font size fields
  before HIP kernel lookup/submission for `bitmap_glyph_raster`, and exposes a
  matching `bitmap_glyph_raster_kernel(...)` convenience route.
- verify: Focused ROCm session check passes and ROCm session contract spec now
  passes 9/9. Generated manual was refreshed under `doc/06_spec`. This proves
  HIP launch preflight and fail-closed validation, not readback-verified GPU
  glyph pixels.
- verify: Optimizer scans completed for this slice. Counts: ROCm session 38
  and ROCm session contract spec 2 remaining static opportunities.
- impl: Added bitmap glyph raster readback evidence.
  `bitmap_glyph_raster_readback_evidence(...)` composes the generated
  `bitmap_glyph_raster` execution request, submit result, and checksum readback
  evidence. It marks bitmap glyph rasterization production-ready only when the
  generated kernel submitted and returned a checksum matching the expected
  glyph pixels.
- verify: Focused bitmap-font offload check passes and bitmap-font offload spec
  now passes 5/5. Generated manual was refreshed under `doc/06_spec`. This adds
  a strict proof boundary for real device runs; it does not by itself provide a
  hardware readback sample on this host.
- verify: Optimizer scans completed for this slice. Counts: bitmap-font offload
  14 and bitmap-font offload spec 0 remaining static opportunities.
- impl: Added deterministic bitmap glyph raster expected-output oracle.
  `bitmap_glyph_raster_expected_pixels(...)` maps glyph mask bits to
  color/zero pixels and `bitmap_glyph_raster_checksum(...)` computes the
  expected checksum used by `bitmap_glyph_raster_readback_evidence(...)`.
- verify: Focused bitmap-font offload check passes and bitmap-font offload spec
  now passes 7/7, including closed-failure provenance and invalid dimensions.
  Generated manual was refreshed under `doc/06_spec`. This removes the magic
  expected checksum from readback proof but still is not a hardware sample.
- verify: Optimizer scans completed for this slice in Docker. Counts:
  bitmap-font offload 26 and bitmap-font offload spec 5 remaining static
  opportunities.
- impl: Added CUDA session routing for generated bitmap glyph raster.
  `CudaSession.bitmap_glyph_raster_kernel(...)` now mirrors the OpenCL/ROCm
  helper surface and routes `GENERATED_2D_BITMAP_GLYPH_RASTER` through the
  shared generated 2D launch gate.
- verify: Focused CUDA session check passes and CUDA session contract spec now
  passes 8/8. Generated manual was refreshed under `doc/06_spec`. This proves
  CUDA session routing/provenance for the bitmap glyph raster operation, not
  readback-verified GPU glyph pixels.
- verify: Optimizer scans completed for this slice in Docker. Counts: CUDA
  session 23 and CUDA session contract spec 0 remaining static opportunities.
- impl: Trimmed the anti-aliased Engine2D text fallback loop to real glyph
  coverage pixels. `text_aa_blit_buffer(...)` now precomputes the inverse scale
  and row base, increments `sample_x`, and relies on the prefilled background
  buffer for advance gaps instead of iterating those padding pixels per glyph
  row.
- verify: Focused helpers-text check passes and helpers-text spec now passes
  6/6, including Spark-suggested pixel-count coverage and a new assertion that
  anti-aliased advance gaps remain background. Generated manual refreshed under
  `doc/06_spec`. Optimizer scans completed in Docker: helpers text 37 and
  helpers-text spec 13 remaining static opportunities.
- impl: Hoisted additional Engine2D text fallback arithmetic. The bitmap text
  buffer path now computes the scaled glyph-row base once per source row/column
  bit and adds the scaled-row offset, and the anti-aliased path reuses a
  precomputed sample-x start plus inverse-scale multiplication for sample-y.
- verify: Focused helpers-text check still passes and helpers-text spec remains
  6/6. Docker optimizer scans completed for the final slice: helpers text 37
  and helpers-text spec 13 remaining static opportunities; the static count did
  not change, but the edit removes repeated arithmetic from hot inner loops.
- impl: Added a scale-1 bitmap text fallback fast path for the common 5x7
  glyph-buffer case. `text_render_metrics_to_buf(...)` now routes `scale == 1`
  to `text_render_metrics_to_buf_scale1(...)`, which writes one foreground
  pixel per set glyph bit and leaves the prefilled advance gap as background
  instead of entering the scaled `sy`/`sx` loops.
- verify: Focused helpers-text check passes and helpers-text spec now passes
  7/7, including a new scale-one advance-gap assertion. Generated manual
  refreshed under `doc/06_spec`. Docker optimizer scans completed: helpers text
  45 and helpers-text spec 16 remaining static opportunities; the static count
  rises because the common-path loop is split out, but runtime scale-one bitmap
  text avoids the nested scaled-pixel loops.
- impl: Added a positive z-index paint-order fast path in the Simple Web
  renderer. Already nondecreasing positive z-index nodes now append directly to
  the paint-order list, while out-of-order values still use the existing stable
  insertion path. This avoids the O(k^2) scan/shift shape for common sorted
  z-index startup fixtures without changing paint order.
- verify: Focused renderer check passes and
  `simple_web_layout_child_index_spec.spl` now passes 11/11, including both
  out-of-order and already sorted positive z-index paint oracles. Generated
  manual refreshed under `doc/06_spec`. Docker optimizer scans completed:
  renderer 748 and focused spec 4 remaining static opportunities.
- impl: Added checksum-gated vector font glyph readback evidence.
  `vector_font_glyph_readback_evidence(...)` now derives the expected checksum
  from returned vector glyph alpha pixels and requires both GPU-returned glyph
  counters and checksum-matched device readback before marking vector font
  readback production-ready.
- verify: Focused vector-font offload check passes and vector-font offload spec
  now passes 6/6. Generated manual refreshed under `doc/06_spec`. This creates
  a stronger proof wrapper for future device samples but does not provide a
  hardware readback sample on this host.
- verify: Optimizer scans completed for this slice in Docker. Counts:
  vector-font offload 20 and vector-font offload spec 2 remaining static
  opportunities.
- impl: Added explicit-native Engine2D preference helpers.
  `backend_explicit_native_priority_order()` and
  `backend_full_preference_order()` now put `baremetal` and `virtio_gpu` ahead
  of auto-probed GPU backends, while `backend_default_priority_order()` remains
  Metal-first for width/height-only startup probing. Native aliases normalize to
  those explicit backend names and diagnostics now describe the required
  caller-owned framebuffer surfaces.
- verify: Focused helper availability check passes and the new helper
  availability spec passes 3/3. Generated manual refreshed under
  `doc/06_spec`. This documents preference order and diagnostics only; it is
  not hardware readback evidence for GPU-rendered glyph pixels.
- verify: Optimizer scans completed for this slice in Docker. Counts:
  helpers availability 64, Engine2D engine 34, and helpers availability spec 6
  remaining static opportunities.
- impl: Added mask-derived bitmap glyph raster readback evidence.
  `bitmap_glyph_raster_mask_readback_evidence(...)` derives expected pixels and
  checksum from the glyph mask/color before comparing a device readback
  checksum, so future hardware samples do not pass a hand-written expected
  checksum.
- verify: Focused bitmap-font offload check passes and bitmap-font offload spec
  now passes 5/5. Generated manual was refreshed under `doc/06_spec`. This
  tightens the proof wrapper for future device samples but still is not a
  hardware readback sample.
- verify: Optimizer scans completed for this slice in Docker. Counts:
  bitmap-font offload 27 and bitmap-font offload spec 4 remaining static
  opportunities.
- impl: Removed an avoidable allocation from bitmap glyph readback proof.
  `bitmap_glyph_raster_mask_checksum(...)` computes the expected checksum
  directly from glyph mask bits and color, and
  `bitmap_glyph_raster_mask_readback_evidence(...)` now uses it instead of
  allocating expected pixels first.
- verify: Focused bitmap-font offload check passes and bitmap-font offload spec
  remains 5/5. Generated manual was refreshed under `doc/06_spec`.
- verify: Optimizer scans completed for this slice in Docker. Counts:
  bitmap-font offload 31 and bitmap-font offload spec 6 remaining static
  opportunities.
- impl: Added CUDA session readback evidence classification.
  `CudaSession.readback_evidence(...)` now uses the shared
  `gpu_session_readback_status(...)` classifier for readback unavailable,
  invalid checksum, checksum match, and checksum mismatch states.
- verify: Focused CUDA session check passes and CUDA session contract spec now
  passes 9/9. Generated manual was refreshed under `doc/06_spec`. This proves
  CUDA readback classification only; real device readback is still required
  before claiming GPU-rendered glyph pixels.
- verify: Optimizer scans completed for this slice in Docker. Counts: CUDA
  session 23 and CUDA session contract spec 0 remaining static opportunities.
- impl: Folded positive z-index paint-order collection into the existing
  absolute-position paint pass. Positive z nodes are collected while z<=0
  absolute decorations are painted, removing the extra node-wide scan that ran
  whenever positive z-index nodes existed while keeping the sorted append fast
  path and stable insertion fallback.
- verify: Focused renderer check passes and
  `simple_web_layout_child_index_spec.spl` remains 11/11. Generated manual
  refreshed under `doc/06_spec`. Docker optimizer scans completed: renderer
  747 and focused spec 4 remaining static opportunities.
- impl: Moved selector-token trimming into selector group preprocessing.
  `selector_group_parts(...)` now stores already-trimmed parts, and the
  selector bucket/rightmost and ancestor match paths reuse those tokens instead
  of trimming the same selector text during every node match.
- verify: Focused renderer check passes and
  `simple_web_layout_child_index_spec.spl` now passes 12/12, including a
  spaced descendant/child selector oracle. Generated manual refreshed under
  `doc/06_spec`. Docker optimizer scans completed: renderer 750 and focused
  spec 4 remaining static opportunities; the renderer count rises because the
  one-time preprocessing loop is explicit, while runtime matching avoids
  repeated trim work.
- impl: Moved class-token trimming into HTML parse. `parse_html(...)` now stores
  trimmed `class_words`, and style candidate lookup plus duplicate-class
  suppression reuse those tokens instead of trimming class words during every
  style pass.
- verify: Focused renderer check passes and
  `simple_web_layout_child_index_spec.spl` now passes 13/13, including a spaced
  duplicate class-token selector oracle. Generated manual refreshed under
  `doc/06_spec`. Docker optimizer scans completed: renderer 754 and focused
  spec 4 remaining static opportunities; the renderer count rises because the
  one-time parse loop is explicit, while style matching avoids repeated class
  token trim work.
- impl: Cached text-segment trim results during HTML parse. Non-tag text
  segments now trim once, use that value for the non-empty check, and store the
  same value in `text_trimmed` when a text node is emitted.
- verify: Focused renderer check passes and
  `simple_web_layout_child_index_spec.spl` now passes 14/14, including a
  whitespace-only text segment block-layout oracle. Generated manual refreshed
  under `doc/06_spec`. Docker optimizer scans completed: renderer 754 and
  focused spec 4 remaining static opportunities.
- impl: Removed the redundant `trim()` allocation from `parse_int(...)`. The
  digit scanner already skips leading non-digits and stops after the first
  digit run, so CSS values from declaration parsing keep the same behavior
  without an extra string allocation.
- verify: Focused renderer check passes and
  `simple_web_layout_child_index_spec.spl` now passes 15/15, including spaced
  numeric style parsing for width, height, and margin. Generated manual
  refreshed under `doc/06_spec`. Docker optimizer scans completed: renderer
  754 and focused spec 4 remaining static opportunities.
- impl: Removed the redundant selector-token `trim()` from `simple_match(...)`.
  Selector group preprocessing already stores trimmed parts, so node and
  ancestor selector matching now reuses those tokens directly.
- verify: Focused renderer check passes and
  `simple_web_layout_child_index_spec.spl` remains 15/15, including the
  existing spaced descendant/child selector oracle. Docker optimizer scan
  completed for the renderer with 754 remaining static opportunities.
- impl: Removed redundant trim work from compound class selector matching.
  `class_has_all(...)` now reuses class suffixes from pretrimmed selector parts
  instead of trimming each suffix during every selector match.
- verify: Focused renderer check passes and
  `simple_web_layout_child_index_spec.spl` remains 15/15, including existing
  compound class and spaced selector oracles. Docker optimizer scan completed
  for the renderer with 754 remaining static opportunities.
- impl: Removed the redundant initial trim from `selector_bucket_base(...)`.
  Rightmost selector parts are already trimmed by selector preprocessing, so
  bucket classification reuses that text directly while retaining the
  attribute-prefix trim.
- verify: Focused renderer check passes and
  `simple_web_layout_child_index_spec.spl` remains 15/15. Docker optimizer scan
  completed for the renderer with 754 remaining static opportunities.
- impl: Reused selector bucket base extraction during rule bucket construction.
  `build_rule_buckets(...)` now computes `selector_bucket_base(...)` once per
  rightmost selector and feeds base-aware kind/value helpers, avoiding duplicate
  pseudo/attribute scans and substring work in both bucket counting and fill
  passes.
- verify: Focused renderer check passes and
  `simple_web_layout_child_index_spec.spl` remains 15/15. Docker optimizer scan
  completed for the renderer with 754 remaining static opportunities.
- next: Spark identified `split_class_words_trimmed(...)` as the next bounded
  candidate: replace parse-time `class_attr.split(" ")` plus per-token trim
  with a single-pass tokenizer while preserving ASCII-space-only split
  semantics and repeated-space behavior.
