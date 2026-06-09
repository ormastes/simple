<!-- codex-architecture -->
# GPU Full Render Offload MDSOC+ Plan

Date: 2026-06-09
Status: proposed
Scope: Pure Simple GUI, Pure Simple Web renderer, Simple 2D, and later TUI

## Goal

Move as much GUI/Web/2D rendering work as practical from CPU to GPU without
moving host-owned UI semantics to GPU. The target is:

```
CPU host tree + events + authoritative layout
  -> boundary config + stable Draw IR / Graph IR
  -> GPU render graph expansion, raster, compositing, present, readback
```

This keeps MDSOC+ as the overall architecture:

- MDSOC outer capsules define stable ports, capabilities, visibility, backend
  contracts, and evidence.
- ECS-like or retained state may live inside long-running userland services:
  window tree, surfaces, dirty regions, cached GPU resources, frame receipts.
- Kernel, drivers, raw device queues, and SFFI runtime handles remain
  MDSOC-only, not ECS-owned.

External systems are references, not replacement architectures:

- Chromium: CPU/Blink owns DOM/layout/paint records; GPU process/compositor
  executes accelerated compositing.
- Qt Quick: retained scene graph rendered through graphics APIs via Qt RHI.
- Skia/Flutter: framework/layout stays CPU-side while GPU backends raster and
  composite.
- SYCL: reference for queue, command graph, device selection, memory, and async
  dependency design; not the first draw backend.

## Current Repo Anchors

- UI stack architecture:
  `doc/04_architecture/ui/simple_gui_stack.md`
- Draw IR contract:
  `src/lib/common/ui/draw_ir.spl`
- WM to Draw IR projection:
  `src/lib/common/ui/window_scene_draw_ir.spl`
- Window scene contract:
  `src/lib/common/ui/window_scene.spl`
- Existing 3D Graph IR reference:
  `src/lib/nogc_sync_mut/engine/render/graph_ir3d.spl`
- Web HTML layout to Draw IR:
  `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`
- Current Draw IR executor:
  `src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl`
- Engine2D facade:
  `src/lib/gc_async_mut/gpu/engine2d/engine.spl`
- Draw/processing lane sketch:
  `src/lib/gc_async_mut/gpu/engine2d/backend_lane.spl`
- Minimal draw core:
  `src/lib/gc_async_mut/gpu/engine2d/backend_core.spl`
- Compute session contract:
  `src/lib/gc_async_mut/gpu/engine2d/backend_session.spl`
- Vulkan backend/runtime:
  `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl`,
  `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_spirv.spl`,
  `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_spirv_raster_blobs.spl`,
  `src/compiler_rust/runtime/src/vulkan_graphics_runtime.rs`
- Metal backend/runtime:
  `src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl`,
  `src/lib/gc_async_mut/gpu/engine2d/backend_metal_helpers.spl`,
  `src/lib/gc_async_mut/gpu/engine2d/backend_metal_msl.spl`,
  `src/lib/gc_async_mut/gpu/engine2d/metal_session.spl`,
  `src/compiler_rust/runtime/src/metal_graphics_runtime.rs`
- Existing GPU design proposals:
  `doc/05_design/unified_wrapper_unwrap_proposal.md`,
  `doc/05_design/ml/simplified_gpu_types.md`

## MDSOC+ Layer Map

| Layer | MDSOC role | ECS/retained state role | GPU ownership |
| --- | --- | --- | --- |
| UI/API | Stable widget, event, style, accessibility contracts | UI session state | None |
| GUI/WM service | Window, MDI, focus, drag, z-order capsule | Window entities, dirty regions | None |
| Web compatibility | HTML/CSS input compatibility capsule | DOM/style/layout cache | None initially |
| Render boundary | Draw IR / Graph IR common contracts | Retained batches, cache keys | GPU-visible buffers |
| Engine2D | Draw and compute backend facades | Frame resources, receipts | Backend execution |
| Runtime/SFFI | Vulkan/Metal/D3D/WebGPU device ports | Device-local handles only | Queues, memory, pipelines |
| Evidence | Readback, checksum, timing, fallback records | Run ledger | Proof only |

Visibility rules:

- `common/ui` owns Draw IR, Graph IR, event ids, source provenance, and diff
  contracts.
- GUI/Web/TUI siblings may emit common IR but must not call each other's private
  renderer internals.
- Engine2D backends consume common IR through facades only.
- Runtime-specific Vulkan/Metal/D3D/WebGPU handles stay under backend/runtime
  private trees and are never public to GUI/Web/WM code.

## What Stays Host/CPU-Owned

These are not good `@gpu` candidates because they are branchy, semantic,
stateful, order-dependent, or host/device boundary work:

- UI tree ownership, widget identity, accessibility.
- MDI/window manager policy: focus, drag, resize, z-order, close/minimize,
  taskbar routing, tab/group state.
- Event interpretation and authoritative hit routing.
- HTML/CSS parsing, cascade, selector matching, layout tree traversal.
- Text shaping, font fallback, line breaking, IME, selection semantics.
- Host window creation, event pumps, resize callbacks, swapchain creation.
- Chrome/Simple parity oracle export.

CPU may still generate compact boundary config:

- surface id, frame id, viewport, scale, transform root;
- dirty regions and invalidation reason;
- callback ids and hit rectangles;
- style revision and resource revision;
- Draw IR / Graph IR source provenance.

## What Moves To GPU

Preferred `@gpu` or backend-kernel targets:

- Rect fill/stroke, rounded rects, borders, shadows, gradients.
- Image blit, scaling, clipping, opacity.
- Glyph atlas/SDF glyph quad blit; CPU still shapes text.
- Layer compositing, scroll/copy, damage repair.
- Tile binning and batch expansion from Draw IR to GPU command records.
- Pixel diff, checksum, optional readback probes.
- Optional ID buffer for fast hit-test cache; CPU remains authoritative.
- Later: TUI cell grid to glyph/background quads for graphical TUI surfaces.

The GPU should be allowed to generate a backend-local render graph from the
stable CPU-authored Draw IR / Graph IR boundary. It must not become the only
owner of semantic UI state.

## Phase 1: Vulkan-First Host + GPU Drawing

### Phase 1A: Boundary Freeze

1. Define the canonical render boundary:
   `WebRender/WindowScene -> DrawIrComposition -> DisplayGraphIR`.
2. Extend `src/lib/common/ui/draw_ir.spl` only for fields that are still
   missing from retained execution:
   - `dirty_rects`;
   - `resource_ids`;
   - `clip_stack_id`;
   - `z_order`;
   - `stable_command_id`;
   - `revision`.
3. Add a 2D display graph sibling to the existing 3D Graph IR:
   `src/lib/common/ui/display_graph_ir.spl`.
4. `DisplayGraphIR` is derived from `DrawIrComposition`, never from backend
   state. It should express:
   - surfaces/layers;
   - z ordering;
   - clips;
   - tile bins;
   - resources;
   - dirty regions;
   - command grouping;
   - readback/evidence regions.
5. GPU backends may optimize and reorder inside explicit pass boundaries, but
   cannot change hit rects, layout boxes, event ids, or scene keys.
6. Keep CPU layout/hit maps side-by-side with the GPU plan.
7. Require every emitted plan to carry:
   - source capsule (`gui_ast`, `html_ast`, `tui_grid`, `wm_scene`);
   - style revision;
   - scene key;
   - resource revision;
   - deterministic command order;
   - fallback policy.

Deliverables:

- Architecture doc in `doc/04_architecture/ui/`.
- Detail design in `doc/05_design/ui/`.
- SPipe spec under `test/03_system/gui/` proving a GUI, Web, and 2D surface
  produce equivalent Draw IR and DisplayGraphIR records.

### Phase 1B: Vulkan Process/Session

1. Make Vulkan the first production full-render backend.
2. Use a separate GPU process or isolated worker process where practical:
   - host process owns UI tree/events;
   - GPU process owns Vulkan instance/device/queues/swapchain/pipelines;
   - command transport is serialized GraphRenderPlan plus resource deltas;
   - GPU process crash returns explicit fallback reason, not silent success.
3. Keep an in-process debug mode for simple tests, but evidence must distinguish
   process-isolated and in-process runs.
4. Add resource lifetime rules:
   - CPU resource id -> GPU resource handle mapping;
   - generation counters;
   - explicit release;
   - swapchain recreation on resize;
   - no stale handle reuse after device loss.

Deliverables:

- Vulkan session adapter under `src/lib/gc_async_mut/gpu/engine2d/`.
- Runtime bridge under `src/compiler_rust/runtime/src/`.
- Process wrapper script under `scripts/check/`.
- Evidence report under `doc/09_report/`.

### Phase 1C: Vulkan Draw Kernels/Pipelines

Implement GPU drawing in increasing order of payoff:

1. Clear and opaque filled rects.
2. Clipped filled rects and layer ordering.
3. Opaque/alpha rect layer compositing.
4. Image blits and scaling.
5. Glyph atlas blits.
6. Borders, rounded rects, shadows, and gradients.
7. Scroll/copy dirty-region repair.
8. Optional ID-buffer hit cache.
9. Pixel diff/checksum readback.

Vulkan caveat:

- Current Vulkan advanced shader surfaces include placeholder/no-op SPIR-V
  paths. Phase 1 must not claim line, circle, path, gradient, image, or text
  parity until each command has strict CPU-oracle readback evidence.
- Start with the currently trustworthy `clear`/filled-rect capability, then
  widen one command family at a time.

Batching requirements:

- No one GPU dispatch per widget.
- Coalesce adjacent compatible commands.
- Use instance buffers for rects/glyphs/images.
- Keep per-frame uploads bounded by dirty/resource deltas.
- Record CPU time, GPU submit time, GPU wait time, readback time, and fallback
  count.

Evidence gates:

- CPU oracle checksum equals Vulkan checksum for fixed fixtures.
- Draw IR diff proves same component ids, geometry, style provenance.
- Vulkan strict mode fails when Vulkan is unavailable.
- No silent CPU fallback for requested `vulkan`.
- Resize, dirty region, MDI drag, titlebar button/input, and Web case 77
  continue to pass.

### Phase 1D: GUI/Web/2D Adoption

Adopt Vulkan through the shared boundary, not per-surface special cases:

- Pure Simple GUI: `window_scene_draw_ir -> DisplayGraphIR -> Vulkan`.
- Pure Simple Web: `simple_web_layout_render_html_draw_ir -> DisplayGraphIR
  -> Vulkan`.
- Simple 2D: direct `DrawIrComposition -> DisplayGraphIR -> Vulkan`.
- MDI compositor: GPU layer composition for windows; CPU keeps WM policy.
- TUI later: TUI grid to Draw IR/GraphRenderPlan for graphical terminal mode.

Performance targets:

- Large 2D/HTML/MDI scenes: 2x-20x over CPU raster/composite.
- Normal GUI dirty-region redraw: 1.2x-3x.
- Small one-widget updates: must not regress beyond a documented threshold.
- Readback-heavy tests: allowed slower, but must report readback cost.

## Phase 2: Metal Mirror, Then Other Backends

### Phase 2A: Metal Parity

Mirror Vulkan semantics on macOS:

- same DisplayGraphIR input;
- same command grouping;
- same fallback/error schema;
- same readback evidence fields;
- same checksum/pixel proof fixtures.

Metal-specific work:

- Metal device/queue/library/pipeline state lifecycle.
- MTLBuffer/MTLTexture allocation and generation counters.
- Separate framebuffer buffer, staging/readback buffer, and drawable texture.
- Command buffer completion and error reporting.
- Drawable resize/swapchain handling.
- CAMetalLayer/drawable present separated from framebuffer readback.
- `present()` cannot prove CPU mirror correctness; readback evidence must prove
  GPU-owned data.
- macOS host-native MDI evidence:
  titlebar button/input, CSS style geometry, resize, click/input routing,
  screenshot and proof JSON.

Evidence gates:

- Native macOS Metal strict smoke.
- CPU oracle equals Metal readback.
- No mirror tautology: Metal proof must use `read_pixels_gpu_only` or equivalent
  GPU-readback path, not the CPU mirror.
- Same GUI/Web/2D fixtures as Vulkan.
- `metal-unavailable` is explicit on non-macOS hosts.

### Phase 2B: Backend Matrix

After Vulkan and Metal converge, add or promote:

- D3D12/DX: Windows draw/present backend, not DXVK-only stubs.
- WebGPU: browser/native portable draw and compute.
- CUDA/HIP: compute-heavy processing lane, paired with Vulkan/D3D/Metal/WebGPU
  present or explicit readback.
- SYCL: compute lane and architecture reference for portable command queues,
  dependencies, memory models, and device selection.
- OpenCL: optional legacy compute fallback.

All backends must implement the same capability contract:

- `supports_draw_surface`
- `supports_compute_kernels`
- `supports_present`
- `supports_readback`
- `supports_process_isolation`
- `supports_required_fixture_set`

## TUI Offload Path

TUI should not be first, but it should fit the same plan:

1. CPU terminal semantics stay authoritative.
2. TUI screen/cell grid becomes `tui_grid` source Draw IR.
3. GPU renders background rects and glyph atlas quads for graphical terminal or
   TUI-web surfaces.
4. Real terminal output remains CPU/text-protocol.

This makes TUI GPU overhead similar to GUI/Web overhead only in graphical
surfaces. It does not make ANSI terminal control a GPU problem.

## Agent Work Plan

| Team | Scope | Output |
| --- | --- | --- |
| A: MDSOC+ contracts | Draw IR/GraphRenderPlan, visibility, fallback schema | Architecture + SPipe specs |
| B: Vulkan runtime | Process/session, memory, pipelines, present/readback | Vulkan strict backend + evidence |
| C: GPU draw kernels | Rects, borders, glyphs, images, clips, compositing | Batched kernels + CPU oracle parity |
| D: GUI/Web adoption | GUI, Web, Simple 2D route through common plan | Surface integration + no special forks |
| E: Metal mirror | macOS backend and native evidence | Metal strict proof + host MDI proof |
| F: Perf/evidence | Timing, RSS, fallback, readback, no-cheat gates | Reports + dashboards |
| G: Later backends | D3D12, WebGPU, CUDA/HIP/SYCL/OpenCL compute | Backend matrix expansion |

## Verification Matrix

| Requirement | Evidence |
| --- | --- |
| CPU remains semantic owner | SPipe tests prove event/hit maps independent of GPU backend |
| Vulkan draws GUI/Web/2D | Strict Vulkan reports for all three surfaces |
| No silent fallback | Requested GPU unavailable fails in strict mode |
| Pixel/geometry parity | CPU oracle checksum + Draw IR diff + selected readback regions |
| MDI events still route | Docker/Linux probes and later native macOS/Windows proofs |
| Resize safe | Swapchain recreation test with resource generation counters |
| Perf improves | CPU vs Vulkan vs Metal timing reports on large and small scenes |
| Process isolation works | GPU worker crash/fallback report |
| Docs stay current | `doc/04_architecture`, `doc/05_design`, `doc/07_guide`, `doc/09_report` |

## Risks

- GPU readback can erase performance gains.
- Too many small GPU submissions can be slower than CPU.
- Device loss/driver bugs can destabilize GUI unless process isolation is real.
- Text shaping on GPU would break correctness; keep shaping CPU-side.
- HTML/CSS layout on GPU is not justified until the CPU layout model is stable.
- D3D/DX should not be claimed through DXVK/VKD3D stubs as native Windows proof.

## References

- Chromium GPU accelerated compositing:
  https://www.chromium.org/developers/design-documents/gpu-accelerated-compositing-in-chrome/
- Qt Quick Scene Graph:
  https://doc.qt.io/qt-6/qtquick-visualcanvas-scenegraph.html
- Qt Quick Scene Graph renderer/RHI:
  https://doc.qt.io/qt-6/qtquick-visualcanvas-scenegraph-renderer.html
- Skia documentation:
  https://skia.org/docs/
- Khronos SYCL specification repository:
  https://github.com/KhronosGroup/SYCL-Docs
