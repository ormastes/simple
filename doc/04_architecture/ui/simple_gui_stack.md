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
             -------------------------------------------
             |                    |                    |
             v                    v                    v
      CPU/SIMD backend     GPU backend plugin      Host wrapper surface
      mandatory oracle     OpenCL/CUDA/HIP/        Tauri/Electron/
                           Vulkan/Metal/WebGPU     Chrome/browser/native
             |                    |                    |
             ---------------- shared Engine2D API -----|
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

Engine2D remains the shared drawing execution layer. It should expose stable
primitive operations and backend sessions while hiding backend-specific device
details from UI and wrapper code. Draw processing may use CPU scalar, CPU SIMD,
OpenCL, CUDA, HIP, Vulkan, Metal, or WebGPU, but GUI code sees only the typed
Simple 2D and plugin contracts.

## Hot-Path Policy

Hot redraw paths must avoid:

- repeated full-tree scans;
- repeated file reads;
- subprocess retries;
- HTML/CSS string parsing when a typed GUI AST or already-resolved HTML AST is
  available;
- re-resolving CSS for Draw IR batches whose `style_revision` has not changed;
- device probing per frame;
- hidden wrapper-specific renderer forks.

Capability probes run at startup or explicit re-probe time. Plugin cache keys
must include backend id, device capability version, shader/kernel artifact
version, Draw IR schema version, source kind/id, style revision,
style/font/image cache versions, and fallback reason metadata.

## Migration Order

1. Extract typed `WebRender IR` and `Draw IR` contracts under `src/lib/common/ui`.
2. Split the large web-to-Engine2D renderer into parser/scan helpers, IR
   extraction, and draw execution modules.
3. Route GUI AST redraw through the typed IR path before the HTML parser path.
4. Add the render optimization plugin interface with CPU fallback first.
5. Add GPU backend implementations behind capability probes and evidence
   reports.
6. Keep Tauri, Electron, Chrome, and browser wrappers thin; they should not own
   renderer policy.

## Verification Requirements

Every implementation of this architecture needs evidence for:

- semantic equivalence across TUI, GUI, web, and wrapper paths where the command
  model overlaps;
- CPU fallback rendering for every Draw IR feature;
- plugin fallback reason reporting;
- pixel/capture/hash evidence for GPU execution claims;
- warm redraw latency, input-to-paint latency, max RSS, cache-hit behavior, and
  startup probe cost;
- `doc/06_spec` layout safety: executable specs stay under `test/**`, not
  under generated/manual spec docs.
