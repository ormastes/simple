<!-- codex-architecture -->
# GPU Full Render Offload MDSOC+ Plan

Date: 2026-06-09
Status: active SPipe lane
Scope: Pure Simple GUI, Pure Simple Web renderer, Simple 2D, and later TUI

SPipe state:

- `.spipe/gpu-full-render-offload/state.md`

Current completion state (2026-06-22):

- This document is the controlling rollout plan for GPU full render offload.
- The lane is not complete until the artifact map below is filled with current
  docs/specs/evidence and the remaining blockers have explicit owner tasks.
- Verification must be crash-safe: do not run broad or repeated `bin/simple`
  checks while the 2026-06-22 runaway `bin/simple src/app/repl/main.spl`
  process tree is present. Use targeted file/layout guards and existing
  evidence first, then run one focused scenario per acceptance criterion.
- Windows host setup has Vulkan runtime/driver proof, Chrome, and Electron
  available, but Vulkan SDK developer tools are not yet installed on `PATH`.
  The `winget install --id KhronosGroup.VulkanSDK` attempt downloaded and
  verified the installer, then reached the elevated installer prompt and was
  canceled by the user. Do not claim SDK readiness until `glslangValidator`,
  `spirv-as`, and any required shader compiler are visible to the check shell.

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
  `src/lib/nogc_async_mut/gpu/engine2d/backend_core.spl`
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

## Artifact Map

| Artifact | Current path | State |
| --- | --- | --- |
| SPipe state | `.spipe/gpu-full-render-offload/state.md` | Active acceptance criteria |
| Windows setup guide | `doc/07_guide/app/ui/gui_web_2d_vulkan_setup.md` | Host setup commands, current Windows evidence, and browser Vulkan proof rules |
| Setup wrapper | `scripts/setup/setup-gui-web-2d-vulkan-env.shs` | Canonical readiness and focused browser-backing wrapper |
| Architecture anchor | `doc/04_architecture/ui/simple_gui_stack.md` | Existing stack anchor; needs GPU full-render delta |
| Drawing architecture | `doc/04_architecture/ui/drawing_stack.md`, `doc/04_architecture/ui/engine_2d.md` | Existing anchors; need DisplayGraphIR ownership alignment |
| Renderer parity architecture | `doc/04_architecture/ui/production_gui_web_renderer_parity_hardening.md` | Existing parity anchor |
| Detail design anchor | `doc/05_design/ui/renderer_unification_2026-06-15.md`, `doc/05_design/ui/graphics/engine_2d.md` | Existing design anchors; need full-render offload checklist |
| GUI/Web specs | `test/03_system/gui/simple_web_browser_production_hardening_spec.spl`, `test/03_system/gui/shared_wm_renderer_unification_evidence_spec.spl`, `test/03_system/gui/gui_entry_engine2d_wm_simple_web_spec.spl` | Existing related specs |
| GPU/evidence specs | `test/03_system/check/production_gui_web_renderer_parity_evidence_spec.spl`, `test/03_system/check/production_gui_web_host_gpu_aggregate_status_contract_spec.spl`, `test/03_system/check/electron_vulkan_web_parity_spec.spl`, `test/05_perf/graphics_2d/backend_probe_spec.spl` | Existing related specs; strict backend coverage must be reviewed before done |
| Generated manuals | `doc/06_spec/test/03_system/gui/`, `doc/06_spec/test/03_system/check/`, `doc/06_spec/test/05_perf/graphics_2d/` | Existing mirrors; layout guard must remain zero for `*_spec.spl` under `doc/06_spec` |
| Evidence reports | `doc/09_report/vulkan_engine2d_readback_2026-06-16.md`, `doc/09_report/production_gui_web_renderer_parity_evidence_2026-06-21.md`, `doc/09_report/electron_vulkan_web_parity.md` | Existing reports; must not be interpreted as full offload completion without command-family parity |
| Process guide | `doc/07_guide/infra/testing/benchmarking.md`, GPU/GUI/Web guide notes as updated by the touched wrapper | Needs review when wrappers change |

## Windows Setup Snapshot

Observed on 2026-06-22:

- `vulkaninfo --summary` passes with Vulkan Instance Version `1.3.301`.
- Physical devices report Intel UHD Graphics 770 through the Intel proprietary
  Windows driver, API version `1.3.284`.
- Chrome is installed at
  `C:\Program Files\Google\Chrome\Application\chrome.exe`, version
  `149.0.7827.155`.
- Global Electron is installed, version `v32.1.2`.
- DirectX tooling is present through Windows `dxdiag`; DirectX availability is
  not Vulkan proof and does not prove Electron/Chrome are Vulkan-backed.
- `glslangValidator`, `spirv-as`, and `dxc` were not found on `PATH`.
- `winget search --name Vulkan` lists `KhronosGroup.VulkanRT` and
  `KhronosGroup.VulkanSDK` version `1.4.350.0`.
- `winget install --id KhronosGroup.VulkanSDK --accept-source-agreements
  --accept-package-agreements --silent` downloaded and hash-verified the
  installer, then required an administrator prompt and was canceled. Treat this
  as `sdk-tools-missing`, not as installed.

## Crash-Safe Verification Rules

- Run each acceptance criterion check at most once per session.
- Do not start broad `bin/simple test`, full-tree status, or repeated process
  probes while the runaway REPL process tree remains.
- Never treat fallback screenshots, CPU mirror readback, or Chromium
  `angle=vulkan` unavailable logs as Vulkan-backed browser proof. DirectX
  availability is also not browser Vulkan proof.
- Strict backend requests must fail closed when the requested backend is
  unavailable; silent CPU fallback is a failing result.
- Generated spec layout guard must report zero executable specs under
  `doc/06_spec` before handoff.
- Dirty worktree sync must commit only the GPU full-render lane files after a
  scoped review; do not absorb unrelated crashed-session output.

## Current Evidence Gaps

- A dedicated architecture delta for `DisplayGraphIR` ownership under
  `doc/04_architecture/ui/` is still needed.
- Vulkan runtime is installed and discoverable on the current Windows host, but
  the Vulkan SDK developer tools still need an elevated install or PATH refresh.
- Chrome and Electron are installed, but neither has a passing browser-backing
  Vulkan proof yet; use `scripts/setup/setup-gui-web-2d-vulkan-env.shs
  --browser-backing` and read
  `gui_web_2d_vulkan_browser_backing_status`, reason, and mode.
- A detail design checklist tying `DrawIrComposition -> DisplayGraphIR ->
  backend` to GUI, Web, and Simple 2D is still needed.
- Existing specs cover related renderer parity and backend probe behavior, but
  the lane still needs an explicit review that maps each full-render acceptance
  criterion to a spec/manual/evidence report.
- Vulkan evidence exists for Engine2D readback and Electron/Web parity paths,
  but full command-family parity remains incomplete until strict CPU-oracle
  readback proves each promoted command family.
- Process-isolated GPU worker crash/fallback evidence remains required before
  claiming production process isolation.

## Plan Completion Contract

This SPipe plan is complete when the planning lane proves the following items.
It does not mean every backend implementation is complete.

| ID | Requirement | Authoritative evidence |
| --- | --- | --- |
| PLAN-1 | The lane has a SPipe state file with testable acceptance criteria. | `.spipe/gpu-full-render-offload/state.md` contains `## Acceptance Criteria` and `## Phase` is `dev-done`. |
| PLAN-2 | The plan is no longer a passive proposal. | This file has `Status: active SPipe lane` and a current completion state. |
| PLAN-3 | CPU semantic ownership is explicit. | `What Stays Host/CPU-Owned`, `MDSOC+ Layer Map`, and `Crash-Safe Verification Rules` keep UI tree, layout, events, hit maps, and text shaping outside GPU ownership. |
| PLAN-4 | GPU ownership is explicit. | `What Moves To GPU`, phase deliverables, and backend evidence gates restrict GPU work to render graph expansion, raster, compositing, present, readback, and backend-local resource caches. |
| PLAN-5 | Existing evidence is linked without overclaiming. | `Artifact Map` links current specs and reports, and `Current Evidence Gaps` lists missing full command-family parity and process-isolation proof. |
| PLAN-6 | Crash-safe handoff rules are recorded. | `Crash-Safe Verification Rules` forbids repeated broad checks, silent fallback evidence, and unscoped dirty-worktree sync. |
| PLAN-7 | Future implementation work is decomposed. | `Implementation Task Queue` below has concrete tasks, owners, prerequisites, and done evidence. |

## Implementation Task Queue

| Task | Owner lane | Prerequisites | Done evidence |
| --- | --- | --- | --- |
| T1: DisplayGraphIR architecture delta | A: MDSOC+ contracts | Current Draw IR and window scene anchors | `doc/04_architecture/ui/display_graph_ir.md` or equivalent section in `simple_gui_stack.md`, plus TLDR if a new long doc is created |
| T2: Detail design checklist | A: MDSOC+ contracts | T1 | `doc/05_design/ui/gpu_full_render_offload.md` maps GUI, Web, and Simple 2D through `DrawIrComposition -> DisplayGraphIR -> backend` |
| T3: Boundary SSpec/manual mapping | A/F: contracts and evidence | T1 and T2 | SSpec under `test/03_system/gui/` or `test/03_system/check/` plus generated Markdown under `doc/06_spec/...` |
| T4: Vulkan strict rect baseline | B/C: Vulkan runtime and draw kernels | Existing backend probe and Engine2D readback reports | CPU-oracle checksum equals Vulkan checksum for clear/fill/clipped rect fixtures; requested `vulkan` fails closed when unavailable |
| T5: GUI/Web/2D adoption proof | D: surface adoption | T3 and T4 | One GUI fixture, one Web fixture, and one Simple 2D fixture emit equivalent Draw IR and DisplayGraphIR records before backend execution |
| T6: Process-isolated GPU worker proof | B/F: process and evidence | T4 | Worker crash or device-loss scenario returns explicit fallback reason and does not report success |
| T7: Command-family promotion gates | C/F: kernels and evidence | T4 | Each promoted command family has CPU oracle, GPU readback checksum, Draw IR diff, timing fields, and fallback count |
| T8: Metal mirror proof | E: Metal mirror | T4 and macOS host | Native macOS Metal strict smoke uses GPU readback, not CPU mirror or present-only proof |
| T9: Documentation freshness | F: evidence/docs | Any wrapper or evidence change | Matching `doc/07_guide`, `doc/09_report`, generated manuals, and this plan cite the canonical wrapper and latest evidence |

## Done-Marking Rules

- Mark a task done only when its `Done evidence` path exists and has been read
  against the requirement it claims to prove.
- Do not promote a command family from planned to done because a neighboring
  command family passes.
- Do not treat CPU mirror, fallback bitmap, or present-only output as GPU
  readback proof.
- Do not mark `T5` done from a single surface; GUI, Web, and Simple 2D must each
  have boundary evidence.
- Do not mark `T6` done from an in-process debug run; process-isolated evidence
  must be distinguishable from debug mode.
- If the runaway REPL process tree is still present, record targeted evidence
  from existing files and defer broad runtime execution.

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

Current queue/readback baseline (2026-06-15):

- `scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs`
  is the fail-closed production gate for GUI/web queue and readback evidence.
- BrowserBackend currently proves `simple-draw-ir-v2` widget-semantic dispatch
  through the runtime queue, including widget rect/text commands, one image URI
  command, and event-target context resolution back to the queued GUI AST batch.
- This is command-payload evidence, not full decoded-image rendering. Image
  rendering remains blocked until an asset resolver plus PNG/JPEG/WebP decode
  path feeds Engine2D pixels. Until then, Engine2D must report image commands
  as skipped unsupported Draw IR commands rather than silently implying render
  support.
- Platform matrix remains partial: Vulkan/CUDA/OpenCL fixture evidence passes
  on the current Linux host, and WebGPU real device readback passes with a
  positive handle/checksum. Metal requires native Darwin Metal readback, ROCm
  requires AMD ROCm runtime/device/verified HSACO, and DirectX remains a
  structured readback contract until native Windows D3D11 staging readback
  proves `device_readback`.

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
