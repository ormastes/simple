<!-- codex-architecture -->
# Simple UI, GUI, Web, and 2D Stack Architecture

Status: draft-v3 (2026-06-05)
Owners: `src/app/ui.web`, `src/app/ui.electron`, `src/lib/common/ui`,
`src/lib/gc_async_mut/gpu/browser_engine`,
`src/lib/gc_async_mut/gpu/engine2d`, `src/lib/nogc_sync_mut/gpu/engine2d`

Related:
- `doc/04_architecture/ui/ui_web_protocol.md`
- `doc/04_architecture/ui/engine_2d.md`
- `doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md`
- `doc/04_architecture/compiler/graphics/gui_layer_contract.md`
- `doc/05_design/compiler/graphics/accelerated_shared_ui_backend_architecture.md`

## Purpose

This document is the canonical stack-level architecture for Simple UI surfaces:
TUI, GUI, web, host wrappers, render IR, Engine2D, and accelerated draw
execution. It records the next refactoring direction from the current renderer
shape: keep UI semantics and event ownership in Simple, introduce a typed
render/draw IR boundary, and allow a render optimization plugin to accelerate
draw batches without taking over GUI policy.

## Target Stack

The stack is not a strict "Electron/Tauri under Simple" chain. Tauri,
Electron, Chrome, browser windows, and native host windows are shells. They
transport pixels, patches, input, and host commands around a Simple-owned UI
and renderer contract.

```
Simple code
  |
  v
Simple UI API
  |-------------------------------|
  v                               v
Simple TUI                    Simple GUI API
                                  |
                                  v
                         Pure Simple GUI event handler
                         event callback ids, focus,
                         command routing, async dispatch
                                  |
                                  v
                         Pure Simple GUI AST layer
                         widgets, layout intent,
                         style intent, accessibility
                                  |
                                  v
                         Simple Web API / adapter
                         snapshots, patches, commands,
                         host-safe transport
                                  |
             -------------------------------------------
             |                                         |
             v                                         v
      Optional HTML text/parser path             Direct typed render path
      html-text -> html parser -> html-ast       GUI AST -> WebRender IR
      source=html_ast, css identity             source=gui_ast, style rev
             |                                         |
             --------------------+--------------------|
                                  v
                         Render IR transfer
                         style, surfaces, text runs,
                         images, dirty regions,
                         screen config, callback ids
                                  |
                                  v
                              Draw IR
                         single/composed batches,
                         window/pane composition,
                         callback id locality,
                         source/style provenance
                                  |
                                  v
                           Simple 2D API
                                  |
                                  v
                    Render Optimization Plugin
                    capability probe, cost model,
                    batch selection, cache keys,
                    fallback reason reporting
                                  |
             ----------------------------------------------
             |                                            |
             v                                            v
      Drawing backend lane                      Processing backend lane
      primitive draw, framebuffer,              compute kernels, generated
      present, readback                         artifacts, filters, SIMD/GPU
      CPU/SIMD oracle, Vulkan/Metal             offload, sync evidence
             |                                            |
             ---------------- shared Engine2D API ---------|
                                  |
                                  v
                         Draw processing
                         raster, glyph masks,
                         gradients, alpha blend,
                         compositing, scroll/copy
                                  |
                                  v
                         Primitive draw layer
                         rects, images, text,
                         paths, framebuffer writes
                                  |
                                  v
                         Framebuffer / texture
                                  |
                                  v
                         Present to host window
```

Event and redraw flow:

```
Host window / input
  |
  v
event callback id
  |
  v
Pure Simple GUI event dispatcher
  |
  v
Simple CPU / async task state update
  |
  v
changed GUI AST + dirty region truth
  |
  v
WebRender IR / Draw IR batch
  |
  v
Render Optimization Plugin
  |
  v
CPU or GPU draw execution
```

## Ownership Rules

Simple owns:

- widget tree and GUI AST;
- event callback ids, focus, command routing, and state transitions;
- layout policy and accessibility state;
- dirty-region truth and cache invalidation decisions;
- typed `WebRender IR` and `Draw IR` contracts;
- CPU fallback behavior and conformance tests.

The render optimization plugin owns:

- capability probing and backend selection;
- cost estimation for CPU versus GPU execution;
- draw-batch compilation or kernel selection;
- execution, synchronization, and readback;
- explicit fallback reports when a preferred backend cannot run.

Shell wrappers own:

- process launch, window creation, webview/browser embedding, and host IPC;
- forwarding input to Simple callback ids;
- presenting textures, framebuffers, or browser patches supplied by Simple;
- host-native commands only through the Simple UI protocol.

## Boundaries

### Simple UI and TUI

`Simple UI API` is the common entry point. The TUI path may render directly to
terminal surfaces, but it should share command names, focus semantics, and event
ids with GUI where practical. TUI code must not depend on GUI wrappers or GPU
availability.

The low-dependency UI/dynSMF lane makes this boundary executable:
`app.ui.tui` and the TUI compatibility renderer must stay free of GUI, web,
TUI-web, browser, HTML renderer, and CSS implementation imports. The exact
module-prefix dependency gate in `src/app/ui/dependency_closure_gate.spl`
checks that `app.ui.tui` does not accidentally match similarly named modules
such as `app.ui.tui_web`.

### Renderer Capability Boundary

Renderer implementation capabilities live outside the base UI/TUI closure.
`src/app/ui.render/capability.spl` declares implementation-free metadata for
`html_renderer`, `css_provider`, and `tui_renderer`. HTML-capable widgets and
host web adapters import `app.ui.render.html_widgets` directly; the legacy
`app.ui.render.widgets` module remains a TUI-only compatibility wrapper.

CSS is component-scoped at the adapter edge. Web-capable adapters call
`css_for_components([...])` from `app.ui.render.css` to request only the style
payloads their surface uses, instead of importing a monolithic CSS bundle or
hand-concatenating direct style functions. Non-HTML lanes prove they do not
request the HTML/CSS capability closure through
`test/01_unit/app/ui/render_capability_spec.spl` and
`test/03_system/app/ui/feature/low_dependency_ui_dynsmf_dependency_gate_spec.spl`.

### Simple GUI API

The GUI API expresses UI intent. It should not call Electron, Tauri, Chrome,
CUDA, Metal, Vulkan, or OpenCL APIs directly. GUI logic remains pure Simple
unless an optimization plugin is invoked through a typed backend contract.

### Simple Web API

`src/app/ui.web` is the host-safe transport and web adapter boundary. It owns
snapshots, patches, commands, taskbar/window messages, and session envelopes.
It may accept HTML text for compatibility, but the preferred future path is a
typed GUI AST to WebRender IR transfer that avoids string parsing on hot redraw
paths.

### Render IR and Draw IR

`WebRender IR` records renderable UI facts: style items, surfaces, text runs,
images, dirty regions, screen config, and event callback ids. `Draw IR` lowers
that into execution batches: primitive operations, composition grouping,
callback locality, source/style provenance, and CPU/GPU placement hints.

Draw IR consumers must not infer layout or style from raw HTML/CSS. Conversion
layers resolve GUI AST style intent or HTML AST/CSS information before emitting
Draw IR commands. The batch keeps the source identity (`manual`, `gui_ast`,
`html_ast`, or `wm_scene`), HTML tag/node identity when present, CSS selector or
class when present, and a style revision. That metadata is for diagnostics,
cache invalidation, replay, and GPU batch grouping; primitive commands remain
the execution truth.

The canonical Draw IR schema is `simple-draw-ir-v2`. The typed model includes
box geometry/style metadata plus edge/path/image/group/port command kinds; SDN
inspection uses `src/lib/common/ui/draw_ir_sdn.spl` as an interchange skin over
the same `DrawIrComposition`, not a second model.

UI test helpers consume Draw IR through the shared test contract, not through
renderer-private files or backend handles. Protocol v1 `/api/test/*` endpoints
remain stable; Protocol v2 Draw IR endpoints are optional and capability-gated:
`/api/test/draw-ir`, `/api/test/draw-ir?id=...`,
`/api/test/draw-ir/diff`, and `/api/test/draw-ir/layout?id=...`. SPipe remains
the test harness: new UI/Draw IR specs import `use std.spec`, and `std.spipe`
remains an alias for existing specs.

This boundary is the best next refactoring target because it reduces coupling
between `src/app/ui.web`, `src/lib/common/ui/web_render_api.spl`, and
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer.spl`.

The current bootstrap contract lives in `src/lib/common/ui/draw_ir.spl`. It
defines `DrawIrEmbeddingConfig`, `DrawIrCommand`, `DrawIrBatch`,
`DrawIrSourceInfo`, `DrawIrComposition`, `DrawIrEventTargetContext`,
`Simple2dDrawIrPlan`, and `Simple2dDrawIrCompositionPlan` so the Simple 2D
advanced boundary can accept explicit size, location, layer, transparency,
surface/component identity, source/style provenance, event target context,
backend target, and fallback metadata before GPU execution exists.

Window-manager composition is projected by
`src/lib/common/ui/window_scene_draw_ir.spl`. It converts `SharedWmScene`
chrome, taskbar, and visible windows into ordered Draw IR batches keyed by
`shared_wm_scene_layout_key(scene)`. The first Engine2D-facing acceptor lives in
`src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl`; it executes supported
`rect` and `text` Draw IR commands through the existing Engine2D facade and
returns readback pixels plus CPU/GPU fallback metadata. Real GPU Draw IR
execution remains a later plugin/backend job.

### Render Optimization Plugin

The plugin is an acceleration boundary, not a GUI ownership boundary. It may be
implemented by optimized Simple backends, host GPU libraries, or compiled
kernel artifacts, but the input and output remain Simple-owned contracts.

Required interface shape:

```
RenderOptimizationPlugin
  supports(capabilities, draw_ir) -> SupportReport
  estimate_cost(draw_ir, dirty_regions) -> CostReport
  prepare(draw_ir, cache_key) -> PreparedBatch
  execute(prepared_batch, target_surface) -> ExecuteReport
  readback(surface, region) -> PixelEvidence
```

Fallback to the CPU/SIMD backend is mandatory. The CPU path is the correctness
oracle for tests, screenshots, capture hashes, and unsupported GPU devices.

Backend selection is split into two explicit lanes. The drawing lane owns
framebuffer-visible primitive rendering, present, and readback. The processing
lane owns generated kernels, filter/layout compute, vector/font offload, and
SIMD/GPU preparation work. A backend may implement both lanes on one device, but
that is a `combined` lane plan rather than an implicit assumption. The current
contract is in `src/lib/gc_async_mut/gpu/engine2d/backend_lane.spl`.

### Event Target Translation

Window-level event targeting is resolved through
`src/lib/common/ui/window_scene.spl`. Pointer translation returns a component
kind, local event coordinates, target id, callback/window identity, backend
target metadata, and cache status. The cache key includes the scene layout key
and pointer/backend input key; window movement, resize, layer, or composition
changes must produce a new scene key so stale target translations are rejected.
That same scene key is embedded in WM Draw IR composition so event targeting and
draw processing invalidate together. The event-to-draw-processing handoff is
represented by `DrawIrEventTargetContext`: it maps the translated event target
and local coordinates onto a Draw IR batch, surface/component id, source kind,
and backend target, while rejecting stale scene keys before the renderer or
future GPU plugin receives the event context.

### Engine2D and Primitive Draw

Engine2D remains the shared drawing and processing execution layer. It should
expose stable primitive operations and backend sessions while hiding
backend-specific device details from UI and wrapper code. Drawing backends
handle primitive draw, framebuffer ownership, present, and readback. Processing
backends handle compute kernels, generated artifacts, filters, and offload.
Draw processing may use CPU scalar, CPU SIMD, OpenCL, CUDA, HIP, Vulkan, Metal,
or WebGPU, but GUI code sees only the typed Simple 2D and plugin contracts.

### Startup dynSMF Libraries

The low-dependency lane treats standard library-like capabilities as
precompiled dynSMF entries: `file_io`, `net_io`, `render2d`, `web_renderer`,
`gui_renderer`, and `tui_renderer`. Startup constructs a session through
`src/app/startup/dynsmf_autoload.spl`, applies `--no-dynsmf`,
`--disable-dynsmf=<ids>`, `SIMPLE_DYNSMF=0`, and
`SIMPLE_DYNSMF_DISABLE=<ids>`, validates generated `build/dynsmf/*.smf`
artifacts, and then loads enabled entries through `smf_dlopen`.

The session owns handles and generation metadata so interpreter-mode tests can
unload a library, observe stale symbol evidence, and reload without retaining
process-global state.

## Hot-Path Policy

Hot redraw paths must avoid:

- repeated full-tree scans;
- repeated file reads;
- subprocess retries;
- HTML/CSS string parsing when a typed GUI AST or already-resolved HTML AST is
  available;
- re-resolving CSS for Draw IR batches whose `style_revision` has not changed;
- linear glyph-cache scans for each character in repeated menu/list/status text;
- linear text-buffer cache scans for non-adjacent repeated Draw IR labels;
- device probing per frame;
- hidden wrapper-specific renderer forks.

Capability probes run at startup or explicit re-probe time. Plugin cache keys
must include backend id, device capability version, shader/kernel artifact
version, Draw IR schema version, source kind/id, style revision,
style/font/image cache versions, and fallback reason metadata.
Font cache keys must include at least codepoint and font size; hot-entry and
bucket-index lookups are preferred before any fallback scan or rasterizer
attempt.
Draw IR text-buffer cache keys must include the text payload, foreground,
background, and font size so recurring labels can reuse prepared blit buffers
before a cache scan or glyph raster attempt.
Generated glyph raster kernel callers must use the shared argument packer for
`glyph_plan`, `dst`, `width`, `height`, and `font_size` so generated
Metal/CUDA/HIP/Vulkan/OpenCL launch paths validate the same pointer layout before
backend-specific launch/readback code consumes it.
Native session launch evidence must gate generated glyph kernels on that shared
layout, not merely on `args_ptr != 0`; CUDA, ROCm/HIP, and OpenCL use
backend-prefixed invalid-args reasons for missing glyph plans, missing
destinations, dimension mismatches, and invalid font sizes.
Draw IR text execution must use the shared generated glyph staging helper when
it allocates temporary glyph-plan and destination buffers to prove generated
launch-argument readiness, but production readiness requires backend readback to
populate the vector or bitmap returned-glyph contract before
`font_production_ready` can be true.
Concrete backends must not pass host staging pointers to APIs that require
device buffers. The OpenCL facade owns an explicit generated-glyph smoke path
that allocates device `glyph_plan` and `dst` buffers, packs those device handles
with the shared glyph argument layout, launches `simple_2d_glyph_raster_u32`,
and reports typed launch/readback evidence. That evidence proves the backend
handoff and readback gate, but it intentionally keeps production font readiness
false until real glyph-plan data is connected to the vector and bitmap
returned-glyph contract.
Returned-glyph readback probes for both vector and bitmap fonts must support a
bounded multi-slot batch (`0..7`) so backend launches can return more than one
glyph without falling back to CPU for every character after slot 0.

## Migration Order

1. Extract typed `WebRender IR` and `Draw IR` contracts under `src/lib/common/ui`.
2. Split the large web-to-Engine2D renderer into parser/scan helpers, IR
   extraction, and draw execution modules.
3. Route GUI AST redraw through the typed IR path before the HTML parser path.
4. Add the render optimization plugin interface with CPU fallback first.
5. Split concrete backend implementations into drawing-lane and
   processing-lane capabilities before adding direct GPU Draw IR execution.
6. Add GPU backend implementations behind capability probes and evidence
   reports.
7. Keep Tauri, Electron, Chrome, and browser wrappers thin; they should not own
   renderer policy.

### WM Runtime Dispatch

`src/lib/common/ui/wm_runtime_dispatch.spl` converts backend-neutral
`SharedWmDispatchResult` values into stable `WmRuntimeDispatchCommand` structs
with kind, target_id, app_id, window_id, payload, and handled flag. This
adapter lets host WM runtimes (web bridge, SimpleOS WM, native host) consume
WM commands without depending on the internal window-scene dispatch model.
`WmRuntimeShellState` tracks launched apps, focused window, drag surface, and
last command for shell-side bookkeeping.

The web host bridge in `src/app/ui.web/wm_runtime_bridge.spl` consumes these
dispatch commands and forwards them to the web adapter protocol.

## Source File Map

| Layer | File | Purpose |
|---|---|---|
| Draw IR contract | `src/lib/common/ui/draw_ir.spl` | `DrawIrCommand`, `DrawIrBatch`, `DrawIrComposition`, `DrawIrSourceInfo`, `DrawIrEmbeddingConfig`, `DrawIrEventTargetContext`, `Simple2dDrawIrPlan` |
| Draw IR SDN skin | `src/lib/common/ui/draw_ir_sdn.spl` | Deterministic tab-indented SDN import/export over `DrawIrComposition` |
| Draw IR Draw.io skin | `src/lib/common/ui/draw_ir_drawio.spl` | Draw.io mxGraph import/export over the same `DrawIrComposition` model |
| WM scene | `src/lib/common/ui/window_scene.spl` | `SharedWmScene`, `SharedWmWindow`, event target translation, scene layout keys, cache-safe pointer targeting |
| WM → Draw IR | `src/lib/common/ui/window_scene_draw_ir.spl` | WM scene composition into ordered Draw IR batches (desktop, chrome, windows by z-order) |
| WM dispatch | `src/lib/common/ui/wm_runtime_dispatch.spl` | `WmRuntimeDispatchCommand`, `WmRuntimeShellState`, backend-neutral WM command adapter |
| Engine2D Draw IR | `src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl` | `Engine2dDrawIrAdvResult`, first Simple2D-facing Draw IR executor (rect/text, CPU fallback, pixel readback) |
| Backend lane | `src/lib/gc_async_mut/gpu/engine2d/backend_lane.spl` | Drawing vs processing lane split contract |
| Renderer capability | `src/app/ui.render/capability.spl` | Implementation-free HTML/CSS/TUI renderer capability metadata |
| TUI widget shim | `src/app/ui.render/widgets.spl` | TUI-only compatibility wrapper that avoids HTML/CSS implementation imports |
| HTML widgets | `src/app/ui.render/html_widgets.spl` | HTML-capable widget renderer implementation |
| Component CSS | `src/app/ui.render/css.spl` | Component-scoped CSS payload selector through `css_for_components` |
| UI dependency gate | `src/app/ui/dependency_closure_gate.spl` | Exact-prefix dependency closure verifier for TUI and adapter boundaries |
| dynSMF session | `src/os/smf/dynsmf_session.spl` | Precompiled dynSMF manifest, checked load/autoload, unload/reload evidence |
| dynSMF startup | `src/app/startup/dynsmf_autoload.spl` | CLI/env policy adapter for checked default dynSMF autoload |
| Web render API | `src/lib/common/ui/web_render_api.spl` | WebRender IR transport |
| Web bridge | `src/app/ui.web/wm_bridge.spl` | Web host WM adapter |
| Web WM bridge | `src/app/ui.web/wm_runtime_bridge.spl` | Web host WM runtime dispatch consumer |

## Host Shell Targets

| Shell | App path | Notes |
|---|---|---|
| Web | `src/app/ui.web` | Primary host; web adapter protocol |
| TUI | `src/app/ui.tui` | Terminal surfaces |
| TUI+Web | `src/app/ui.tui_web` | TUI over web transport |
| Standalone | `src/app/ui.standalone` | Native window, no wrapper |
| Tauri | `src/app/ui.tauri` | Tauri webview shell |
| Electron | `src/app/ui.electron` | Electron shell |
| Chromium | `src/app/ui.chromium` | Chromium embedding |
| Browser | `src/app/ui.browser` | Browser-only target |
| VS Code | `src/app/ui.vscode` | VS Code webview extension |
| CLI | `src/app/ui.cli` | CLI-mode UI |
| IPC | `src/app/ui.ipc` | IPC bridge |
| MCP | `src/app/ui.mcp` | MCP UI integration |
| Render | `src/app/ui.render` | Headless render target |
| Test API | `src/app/ui.test_api` | Test harness |

All shells are thin — they forward input and present frames. GUI policy,
state, layout, event routing, and Draw IR remain Simple-owned.

## Verification Requirements

Every implementation of this architecture needs evidence for:

- semantic equivalence across TUI, GUI, web, and wrapper paths where the command
  model overlaps;
- TUI and renderer dependency closure gates proving HTML/CSS/GUI/web
  implementations stay outside non-capable lanes;
- component-scoped CSS selector evidence proving adapters request only the
  style payloads they use;
- checked dynSMF artifact, startup policy, unload, stale symbol, and reload
  evidence for stdlib-like renderer/runtime capabilities;
- CPU fallback rendering for every Draw IR feature;
- plugin fallback reason reporting;
- pixel/capture/hash evidence for GPU execution claims;
- warm redraw latency, input-to-paint latency, max RSS, cache-hit behavior, and
  startup probe cost;
- WM dispatch command parity: `wm_runtime_dispatch_command` output must match
  across web bridge, SimpleOS WM, and standalone hosts;
- `doc/06_spec` layout safety: executable specs stay under `test/**`, not
  under generated/manual spec docs.

## UI Test Architecture

The canonical test-access architecture for TUI, GUI, web, and 2D lives in
`doc/04_architecture/ui/ui_test_architecture.md` and its TLDR companion
`doc/04_architecture/ui/ui_test_architecture_tldr.md`. Two layers are unified
behind one configurable interface (`tui` | `gui` | `both`):

- **HTTP protocol path** - `UITestClient` over `/api/test/*` for S4 surfaces
  (web, tui-web); returns `ElementInfo`.
- **SGTTI in-process path** - `common.ui.win_text_access` +
  `os.compositor.gtti` give GUI/web/2D a headless semantic tree through the
  compositor source in `WM_MODE_HIDDEN`, over canonical `UiAccessNode` values.
  TUI joins through the `UIState -> win_text_simple_ui_snapshot` lift.

New UI specs import `use std.spec`; `std.spipe` remains a compatibility alias.
Helpers such as SGTTI checks and future `expect_draw` run inside SPipe
scenarios and do not replace `expect` or the canonical matcher set.

Semantic SGTTI evidence and pixel evidence run together. SGTTI proves
identity/state/text/structure; existing bitmap gates and Engine2D readback stay
the pixel oracle. Draw IR batches/compositions can be lifted with
`sgtti_snapshot_from_draw_ir_batch` and
`sgtti_snapshot_from_draw_ir_composition`, letting Engine2D specs assert the
pre-raster node tree before pixel readback. Draw IR Protocol v2 inspection
depends on SGTTI. Improvement plan:
`doc/03_plan/ui/ui_test/ui_test_sgtti_plan.md`.

## GUI Sanity Apps (pure-Simple lane, macOS)

Three small on-screen apps exercise the pure-Simple drawing lane (on macOS that
is the Engine2D **CPU/aarch64-NEON** and **Metal** backends). They are the quick
"does the GUI still render" sanity set after any GUI/engine2d/web change:

| Lane | App | What it proves |
|------|-----|----------------|
| 2D rendering | `examples/06_io/ui/engine2d_cpu_simd_gui.spl` (CPU) / `engine2d_metal_gui.spl` (Metal) | Engine2D primitives: text, rect, circle, line, gradient, rounded-rect |
| GUI widgets | `examples/06_io/ui/widget_showcase_gui.spl` | Widget chrome drawn on the CPU lane: button, checkbox, text field, progress bar, list, with legible labels |
| HTML rendering | `examples/06_io/ui/web_text_gui.spl` (text page) / `web_render_file_gui.spl <file.html>` | Web layout → Engine2D CPU: real laid-out, legible glyph text |

Those three apps render **static, non-interactive** scenes — they sanity-check
the drawing surfaces, not the interactive GUI (the HTML one uses the real web
renderer; the 2D/widget ones draw primitives directly, which is fine for a demo
but not a template for an app). The **interactive WM/MDI app** is the real
pipeline and must not be re-implemented by hand-drawing engine2d primitives:

| Lane | App | What it proves |
|------|-----|----------------|
| Interactive WM/MDI | `src/os/hosted/hosted_entry.spl` | `HostCompositor` + `seed_host_compositor_shared_mdi` rendering Simple Web MDI app content through `HostedWinitBufferBackend`, with real event routing (`comp.pointer_move`, `comp.handle_left_button` — click-focus, titlebar drag, close-X; keyboard Tab/W/M/R/Esc). Widget→pixels uses the real `common.ui.builder` → `init_state` → `app.ui.render.html_widgets.render_html_tree` → `simple_web_render_html_to_pixels_with_engine2d_backend` path; hit-testing via `shared_wm_translate_pointer_event` (`src/lib/common/ui/window_scene.spl`). |

Verify the interactive WM with the framebuffer/logic gate (not a screenshot):
`scripts/check/check-shared-wm-renderer-unification-evidence.shs` expects
`shared_wm_renderer_unification_status=pass` and `logic_passed >= 4`. macOS
caveat: the hosted winit window can present blank — the documented winit bug
`doc/08_tracking/bug/macos_winit_window_not_displayed_2026-05-28.md` — so trust
the gate, not the live window. Pure-Simple web render is real but
interpreter-bound (~minutes/frame); the fast live path is Draw IR
(`engine2d_draw_ir_adv_batch` in
`src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl`), whose widget-tree→Draw IR
converter is the not-yet-built "preferred next refactor".

Launch on macOS (registers the process with the window server via a throwaway
`.app` bundle, then nudges the window on-screen):

```sh
scripts/gui/macos-gui-run.shs examples/06_io/ui/engine2d_cpu_simd_gui.spl
scripts/gui/macos-gui-run.shs examples/06_io/ui/widget_showcase_gui.spl
scripts/gui/macos-gui-run.shs examples/06_io/ui/web_text_gui.spl
```

Verification approach (avoid screen-capture flakiness): the **framebuffer is the
ground truth**. Run an app headless and dump `read_pixels()` to a P3 PPM via
`rt_file_write_text`, then inspect/convert it — this proves the lane renders
independent of window-server/compositor state. The live `.app` launch is the
secondary, human-in-the-loop check. (See
`scripts/check/check-macos-gui-live-window-evidence.shs` for the capture gate.)

Caveats:
- The **2D lane is fast**; the **web-layout lane is interpreter-bound (~1.5 ms/px)**,
  so keep web/widget-via-web surfaces small (≤ ~160×120) for one-shot renders.
- The launcher and capture gate compute repo-root from their own location; scripts
  living under `scripts/gui/` and `scripts/check/` must use `dirname/../..` (two
  levels), not `dirname/..` — getting this wrong silently resolves repo-root to
  `scripts/` and breaks every GUI launch.
