<!-- codex-architecture -->
# Simple UI, GUI, Web, and 2D Stack Architecture - TLDR

This is the short version of
`doc/04_architecture/ui/simple_gui_stack.md`. The key decision is to keep GUI
semantics, event routing, layout policy, dirty-region truth, and typed IR in
Simple, while allowing a render optimization plugin to accelerate Draw IR
batches through CPU/GPU backends.

## Core Shape

```
Simple code
  -> Simple UI API
     -> Simple TUI
     -> Simple GUI API
        -> Pure Simple GUI event handler
        -> Pure Simple GUI AST layer
        -> Simple Web API / adapter
        -> WebRender IR
        -> Draw IR
           (commands + source/style provenance)
        -> Simple 2D API
        -> Render Optimization Plugin
           -> CPU/SIMD fallback
           -> GPU plugin: OpenCL/CUDA/HIP/Vulkan/Metal/WebGPU
        -> Engine2D draw processing
        -> primitive draw
        -> framebuffer / texture
        -> host window

Host shells: Tauri, Electron, Chrome, browser, and native host windows stay thin.
They forward input and present frames; they do not own GUI policy.
```

Event flow:

```
Host input
  -> event callback id
  -> Pure Simple GUI dispatcher
  -> Simple state update
  -> dirty region + changed Draw IR
  -> Render Optimization Plugin
  -> CPU or GPU draw execution
```

## Rules

- Simple owns: GUI AST, state, layout policy, event ids, dirty regions, IR
  schemas, cache invalidation, and CPU oracle behavior.
- Plugin owns: capability probe, cost model, batch preparation, GPU/CPU
  execution, readback, and fallback reports.
- Wrappers own: host process/window/webview integration and input/present IPC.
- Preferred next refactor: typed GUI AST -> WebRender IR -> Draw IR; resolve
  GUI/HTML AST and CSS before Draw IR, then keep source kind/id and style
  revision on the batch for cache/debug/GPU grouping.
- Current bootstrap files: `src/lib/common/ui/draw_ir.spl` for Draw IR,
  `src/lib/common/ui/window_scene_draw_ir.spl` for WM composition, and
  `src/lib/common/ui/window_scene.spl` for cache-safe event target translation.
- Event-to-draw-processing handoff: `DrawIrEventTargetContext` maps translated
  input location/component data to a Draw IR batch and rejects stale scene keys.
- Simple2D hook: `src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl` accepts
  Draw IR through Engine2D with CPU fallback metadata and pixel readback.

## Operational Notes

- startup: probe plugin/backend capabilities once, cache the result, and report
  unavailable states explicitly.
- hot path: no full-tree scans, repeated file reads, subprocess retry loops, or
  per-frame device probing.
- cache/index: cache keys include backend id, device capability version, Draw IR
  schema version, source kind/id, artifact version, style/font/image versions,
  style revision, and fallback reason metadata.
- evidence: CPU fallback is mandatory and acts as the rendering test oracle.
- event cache: stale translations are rejected when scene layout keys change;
  WM Draw IR uses the same scene key.

## Open Next

- [source](simple_gui_stack.md)
- [UI web protocol](ui_web_protocol.md)
- [Engine2D architecture](engine_2d.md)
- [accelerated backend architecture](../compiler/graphics/accelerated_shared_ui_backend_architecture.md)
