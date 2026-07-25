# GUI/Web/2D Render-Path Optimization Direction (2026-06-16)

Follow-up to [`gui_web_2d_path_assessment_2026-06-12.md`](gui_web_2d_path_assessment_2026-06-12.md).
Cross-refs: `doc/04_architecture/ui/simple_gui_stack.md`,
`doc/03_plan/ui/gpu_full_render_offload_mdsoc_plus_plan.md`,
`doc/04_architecture/compiler/graphics/gui_layer_contract.md`,
`doc/01_research/ui/wm/shared_wm_renderer_unification.md`.

## Main conclusion

The best optimization direction is **not** "move all GUI logic to GPU." The
repo's architecture is already close to the right model: keep semantic UI, event
routing, layout ownership, dirty-region truth, and CPU fallback in Simple, then
accelerate Draw IR batches, compositing, glyph/image/filter processing, and
large pixel operations through Engine2D/GPU backends. The stack already defines
this separation — WebRender IR carries style/surfaces/text/images/dirty regions,
Draw IR lowers that into primitive batches with CPU/GPU placement hints, and a
`RenderOptimizationPlugin` chooses/executes backend work without owning GUI
policy.

The highest-value **missing** feature is a retained scene/render graph with
visibility containment:

```sdn
GUI AST / Web AST / TUI model
  -> layout cache + visibility/containment cache
  -> WebRender IR / Draw IR diff
  -> dirty-region + occlusion + batch planner
  -> CPU SIMD / GPU Engine2D / WebGPU / Vulkan / Metal / CUDA / HIP / OpenCL
```

This directly solves the "not-yet-shown screen panel parts" issue: hidden tabs,
collapsed panes, offscreen scroll regions, inactive windows, and below-the-fold
panels should keep semantic state but skip layout/paint/draw until needed.

## What Simple already has (reuse, do not bypass)

Simple already documents the ownership boundary. **Simple owns** the widget tree,
GUI AST, event ids, focus, layout policy, accessibility, dirty-region truth,
cache invalidation, typed WebRender IR/Draw IR, CPU fallback, and conformance
tests. **The optimization plugin owns** capability probing, backend selection,
cost estimation, batch compilation, execution, sync, readback, and fallback
reporting.

Hot-path policy is already correct: avoid full-tree scans, repeated file reads,
subprocess retries, HTML/CSS string parsing when typed AST is available, CSS
re-resolution when `style_revision` is unchanged, per-frame device probing, and
wrapper-specific renderer forks. Plugin cache keys already need backend id,
device-capability version, kernel-artifact version, Draw IR schema version,
source kind/id, style/font/image cache versions, and fallback metadata.

Backend order is already GPU-first but fail-closed:
`metal > cuda > rocm/hip > qualcomm > vulkan > directx > opencl > opengl > intel
> webgpu > cpu_simd > software > cpu`, with baremetal and virtio_gpu as explicit
caller-owned surfaces. GUI/lib callers enter through the Engine2D backend-lane
planner, never the GPU APIs directly.

So the next step adds **better invalidation, visibility, batching, and cache
policy inside the typed IR + Engine2D lane** — it does not fork the architecture.

## Optimization methods to apply

### 1. Visibility containment / skip offscreen rendering
Mirror browser `content-visibility`: skip rendering offscreen content, render as
it approaches the viewport, preserve cached rendering state for hidden content
(virtual scrollers, inactive SPA views). Represent in GUI AST → WebRender IR →
Draw IR, not as a web-only feature.

```simple
enum UiVisibilityPolicy: visible, hidden_keep_cache, auto_viewport, virtualized

struct UiContainment:
    size_contained: bool
    layout_contained: bool
    style_contained: bool
    paint_contained: bool
    intrinsic_w: i64
    intrinsic_h: i64
    prefetch_margin_px: i64
```

| UI part | Policy |
|---|---|
| Hidden tab page | `hidden_keep_cache`: no layout/paint/draw, keep last cache |
| Below-fold scroll panel | `auto_viewport`: skip child layout/paint until near viewport |
| Huge list/table/tree | `virtualized`: realize only visible rows + overscan |
| Minimized/inactive window | skip draw, keep semantic state + event ids |
| Covered window area | occlusion-cull if fully covered by opaque front window |

### 2. Dirty-region propagation and Draw IR diff
Make the existing "changed GUI AST + dirty-region truth" structural:
`event/state change -> mark semantic node dirty -> recompute affected layout
ancestors only -> emit changed Render IR nodes only -> emit Draw IR diff only ->
repaint dirty rects only`. Track per-node revisions: `style_rev`, `layout_rev`,
`content_rev`, `image_rev`, `font_rev`, `children_rev`, `visibility_rev`. Skip a
subtree when layout input, `style_rev`, `content_rev`, font/image cache rev, and
viewport-visibility class are all unchanged. Draw IR metadata stays diagnostic;
primitive commands remain execution truth.

### 3. Retained display list / retained Draw IR
WebRender sends a display list, turns high-level instructions into batched GPU
draw calls, and early-culls offscreen items. Simple's Draw IR is already close.

```sdn
DrawIrRetainedCache:
  key = node_id + style_rev + layout_rev + content_rev + backend_target
  value = prepared primitive commands + batch metadata + bounding box
```

Frame generation becomes: `old Draw IR + dirty semantic nodes + viewport ->
update retained nodes -> cull invisible commands -> batch visible commands ->
execute changed batches` — instead of rebuild-HTML / parse-CSS / full-tree
layout / full-framebuffer raster every frame.

### 4. Occlusion culling and overdraw reduction
Stage 1 viewport culling (drop primitives outside viewport/clip). Stage 2
occlusion culling (front-to-back opaque rects build a covered-region set; drop
fully covered primitives behind them). Integrate into `window_scene_draw_ir.spl`,
which already projects chrome/taskbar/windows into ordered Draw IR batches.

### 5. Render graph for filters/shadows/blur/rounded/composition
Use a render task graph (à la Unreal RDG: record passes, compile, cull unused,
alias transient resources, manage barriers). Simple passes:
`glyph_atlas_upload -> image_decode_upload -> rounded_rect_mask -> window_shadow
-> offscreen_panel_cache -> compose_window -> final_present`. Auto-cull: skip
panel passes when invisible + cache valid; skip shadow outside dirty region;
reuse blur texture when source unchanged.

### 6. GPU batching and instancing
Cost is usually state changes / draw calls / uploads / syncs / readbacks, not the
fill. Batch by backend, surface, clip, blend mode, shader/pipeline, texture/image
atlas, font atlas, style, z/composition group. Instance rectangles, rounded
rects, borders, glyph quads, image quads, icons, selection highlights, terminal
cells. `prepare()` compiles and caches these. **Rule:** for small dirty updates
CPU SIMD often wins (GPU launch/sync overhead); CPU/SIMD stays the correctness
oracle.

### 7. 2D pixel ops — specialize five core ops first
`fill`, `copy`, `alpha_blend`, `blit_rect`, `scroll` (foundation for GUI/web/TUI
cell/terminal scroll/image blit/panel-cache copy/dirty repaint).

| Op | Optimization |
|---|---|
| fill | AVX2/NEON/RVV or GPU kernel for large spans |
| copy | SIMD row copy; GPU texture copy |
| alpha_blend | SIMD Porter-Duff; GPU fragment/compute for large regions |
| blit_rect | tile-aligned copy; texture blit |
| scroll | copy preserved region, repaint exposed strip only |

Full hardware-backed evidence (1920×1080 fill+blit+scroll across
CUDA/HIP/OpenCL/CPU-SIMD) is still incomplete per the existing 2D plan.

### 8. Text and glyph optimization
Cache layers: shaping cache (text+font+size+script+direction+features), glyph
bitmap/vector cache (glyph_id+font+size+hinting+AA), glyph atlas
(backend+atlas-rev), text-run layout cache (run_id+width+font_rev+style_rev).
Keep the existing strictness: do not call upload/copy/export "GPU glyph
rasterization" until generated-kernel submit + checksum-matched readback passes.

### 9. Layout optimization
Don't recompute layout for invisible/contained subtrees. Key:
`node_id + available_w/h + style_rev + content_rev + font_rev +
children_measure_rev + containment_flags`. If `size_contained`, parent uses
intrinsic size without descending; if `paint_contained` + offscreen, skip paint;
if `layout_contained` + child dirty, don't invalidate above the boundary; if only
transform/opacity changes, skip layout and update the compositor property.

### 10. Web renderer optimization
Route GUI AST redraw through typed IR before the HTML-parser path; avoid hot-path
HTML/CSS string parsing. Expand the current single static full-page cache to:
static full-page, per-component Render IR, per-style-revision CSS resolution,
image/font, viewport-visibility, and Draw IR prepared-batch caches. Address the
known pure-Simple traps (interpreted canvas-bound raster, O(n²) push-loop buffer
construction, full-framebuffer clone per pixel write) via retained IR, batch
writes, native/SIMD pixel kernels, and fewer full-frame writes.

### 11. TUI optimization
Share semantic model/focus/command-names/event-ids, but never depend on GUI
wrappers or GPU. Terminal-native: previous/current cell buffers, diff cells,
coalesce adjacent runs, emit minimum escape sequences, skip offscreen scrollback,
virtualize tables/lists/trees (cf. Ratatui's `Buffer` cell-grid diff). For
TUI-web, reuse the same semantic tree + visibility cache, then pick output:
native TUI → cell diff; TUI-web → HTML/Draw IR patch; GUI/web → WebRender/Draw IR.

## Concrete implementation order

1. Add visibility/containment fields to GUI AST, WebRender IR, Draw IR, and
   window-scene nodes.
2. Add subtree cache records:
   ```sdn
   SubtreeCache:
     semantic_key, layout_key, render_key, draw_key, bounds,
     visible_state, dirty_region, prepared_backend_batches
   ```
3. Implement viewport query + offscreen skip in GUI/window-scene → Draw IR.
4. **CPU oracle first**: dirty-region diff, viewport culling, occlusion culling,
   retained Draw IR, and TUI buffer diff must work without GPU.
5. **GPU plugin acceleration second**: batching, glyph/image upload,
   filter/render graph, large fill/copy/blend/scroll kernels.
6. Add evidence counters: `visited_nodes`, `skipped_invisible_nodes`,
   `layout_cache_hits`, `style_cache_hits`, `draw_ir_cache_hits`, `dirty_area_px`,
   `culled_primitives`, `draw_calls`, `gpu_batches`, `cpu_simd_ops`,
   `readback_source`, `fallback_reason`, `p50/p95` frame time. Benchmark reports
   must always include backend, fallback state, readback provenance, and frame
   timing (fallback-only/smoke-size runs are not GPU speedups).

## Recommended target architecture

```sdn
Simple semantic UI tree (state, a11y, event ids, visibility+containment policy)
  -> Incremental layout (layout cache, intrinsic-size placeholders, viewport/occlusion query)
  -> WebRender IR (surfaces, text runs, images, style refs, dirty regions)
  -> Retained Draw IR (primitive commands, z/composition groups, CPU/GPU hints, cache keys)
  -> RenderOptimizationPlugin (supports / estimate_cost / prepare / execute / readback)
  -> Engine2D lanes (drawing: framebuffer/present/readback; processing: glyph/filter/layout/image kernels)
  -> Backends (Metal/CUDA/ROCm-HIP/Vulkan/DirectX/OpenCL/WebGPU; CPU SIMD/software/CPU oracle)
```

Principle: **do not render what is invisible, do not recompute what is unchanged,
do not parse strings in hot redraw, do not issue GPU work without a cost model,
and do not lose the CPU oracle.**
