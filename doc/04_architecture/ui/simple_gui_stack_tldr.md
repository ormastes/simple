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
           -> drawing backend lane
              primitive draw, framebuffer, present, readback
           -> processing backend lane
              generated kernels, filters, SIMD/GPU offload
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
- Backend lane split: drawing backends own framebuffer-visible draw/present/
  readback; processing backends own compute kernels, generated artifacts,
  filters, and offload. Combined backends are explicit lane plans.
- Wrappers own: host process/window/webview integration and input/present IPC.
- TUI boundary: `app.ui.tui` and the TUI widget shim must not import GUI, web,
  TUI-web, browser, HTML renderer, or CSS implementations.
- Renderer capabilities: `app.ui.render.capability` declares HTML/CSS/TUI
  capability metadata without importing implementations; HTML-capable adapters
  import `app.ui.render.html_widgets` directly.
- CSS is component-scoped: adapters call `css_for_components([...])` for only
  the style payloads their surface needs.
- Startup dynSMF: file IO, net IO, render2d, web renderer, GUI renderer, and
  TUI renderer use checked `build/dynsmf/*.smf` autoload with arg/env opt-outs
  and session unload/reload evidence.
- Preferred next refactor: typed GUI AST -> WebRender IR -> Draw IR; resolve
  GUI/HTML AST and CSS before Draw IR, then keep source kind/id and style
  revision on the batch for cache/debug/GPU grouping.
- UI test helpers: Protocol v1 `/api/test/*` stays stable; Protocol v2 Draw IR
  is optional and capability-gated at `/api/test/draw-ir`,
  `/api/test/draw-ir?id=...`, `/api/test/draw-ir/diff`, and
  `/api/test/draw-ir/layout?id=...`. New UI/Draw IR/SGTTI specs use
  `std.spec`; `std.spipe` remains an alias for existing specs.
- Current bootstrap files: `src/lib/common/ui/draw_ir.spl` for Draw IR,
  `src/lib/common/ui/draw_ir_sdn.spl` for SDN interchange,
  `src/lib/common/ui/draw_ir_drawio.spl` for Draw.io mxGraph interchange,
  `src/lib/common/ui/window_scene_draw_ir.spl` for WM composition, and
  `src/lib/common/ui/window_scene.spl` for cache-safe event target translation.
- Event-to-draw-processing handoff: `DrawIrEventTargetContext` maps translated
  input location/component data to a Draw IR batch and rejects stale scene keys.
- Simple2D hook: `src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl` accepts
  Draw IR through Engine2D with CPU fallback metadata and pixel readback.
- Engine2D split contract: `src/lib/gc_async_mut/gpu/engine2d/backend_lane.spl`.
- WM dispatch adapter: `src/lib/common/ui/wm_runtime_dispatch.spl` converts
  `SharedWmDispatchResult` to stable `WmRuntimeDispatchCommand` for host shells.
- Web WM bridge: `src/app/ui.web/wm_runtime_bridge.spl` consumes dispatch
  commands for the web host.

## Source Files

| File | What |
|---|---|
| `src/lib/common/ui/draw_ir.spl` | Draw IR contract (commands, batches, composition, event context) |
| `src/lib/common/ui/draw_ir_sdn.spl` | SDN interchange skin over Draw IR |
| `src/lib/common/ui/draw_ir_drawio.spl` | Draw.io mxGraph interchange skin over Draw IR |
| `src/lib/common/ui/window_scene.spl` | WM scene, event target translation, scene layout keys |
| `src/lib/common/ui/window_scene_draw_ir.spl` | WM scene → Draw IR composition |
| `src/lib/common/ui/wm_runtime_dispatch.spl` | WM dispatch command adapter for host shells |
| `src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl` | Engine2D Draw IR executor (rect/text, CPU fallback) |
| `src/lib/gc_async_mut/gpu/engine2d/backend_lane.spl` | Drawing vs processing lane split |
| `src/app/ui.render/capability.spl` | Implementation-free renderer capabilities |
| `src/app/ui.render/widgets.spl` | TUI-only compatibility renderer shim |
| `src/app/ui.render/html_widgets.spl` | HTML-capable widget renderer |
| `src/app/ui.render/css.spl` | Component-scoped CSS selector |
| `src/app/ui/dependency_closure_gate.spl` | Exact-prefix UI dependency closure gate |
| `src/os/smf/dynsmf_session.spl` | checked dynSMF manifest/session/unload |
| `src/app/startup/dynsmf_autoload.spl` | CLI/env dynSMF startup policy |
| `src/app/ui.web/wm_runtime_bridge.spl` | Web host WM runtime bridge |

## Host Shells

Web, TUI, Standalone, Tauri, Electron, Chromium, Browser, VS Code, CLI, IPC,
MCP, Render, Test API — all thin. GUI policy stays in Simple.

## Operational Notes

- startup: probe plugin/backend capabilities once, cache the result, and report
  unavailable states explicitly.
- hot path: no full-tree scans, repeated file reads, subprocess retry loops,
  per-character glyph-cache scans, non-adjacent text-buffer cache scans, or
  per-frame device probing.
- dependency gates: non-capable lanes prove no HTML/CSS/GUI/web closure.
- dynSMF startup: enabled artifacts must exist and start with `SMF\0` before
  `smf_dlopen`.
- cache/index: cache keys include backend id, device capability version, Draw IR
  schema version, source kind/id, artifact version, style/font/image versions,
  style revision, fallback reason metadata, and glyph identity
  `(codepoint,font_size)` plus text-buffer identity `(text,fg,bg,font_size)` for
  font caches.
- evidence: CPU fallback is mandatory and acts as the rendering test oracle.
- event cache: stale translations are rejected when scene layout keys change;
  WM Draw IR uses the same scene key.
- UI tests: `doc/04_architecture/ui/ui_test_architecture.md` defines the
  `tui` | `gui` | `both` interface. HTTP `UITestClient` stays for S4 surfaces;
  SGTTI (`common.ui.win_text_access` + `os.compositor.gtti`) gives headless
  GUI/web/2D semantic assertions over `UiAccessNode`; Draw IR batches and
  compositions lift through `sgtti_snapshot_from_draw_ir_batch` /
  `sgtti_snapshot_from_draw_ir_composition` before Engine2D pixel readback.
  New specs use `std.spec`; `std.spipe` is compatibility only.

## GUI Sanity Apps

Three on-screen apps sanity-check the pure-Simple drawing lane (macOS = Engine2D
CPU/NEON + Metal); launch with `scripts/gui/macos-gui-run.shs <app>`:

- **2D**: `engine2d_cpu_simd_gui.spl` / `engine2d_metal_gui.spl`
- **widgets**: `widget_showcase_gui.spl`
- **HTML**: `web_text_gui.spl` (or `web_render_file_gui.spl <file.html>`)

The above are **static**. The **interactive** GUI is the real pipeline — do NOT
hand-draw one with engine2d primitives:

- **interactive WM/MDI**: `src/os/hosted/hosted_entry.spl` (HostCompositor +
  `seed_host_compositor_shared_mdi`, real `builder`→`render_html_tree`→web-render,
  real event routing). Gate: `check-shared-wm-renderer-unification-evidence.shs`
  (`logic_passed >= 4`).

Verify the framebuffer (`read_pixels` → PPM), not the screenshot. Details +
caveats in [source](simple_gui_stack.md) → "GUI Sanity Apps".

## Open Next

- [source](simple_gui_stack.md)
- [UI web protocol](ui_web_protocol.md)
- [Engine2D architecture](engine_2d.md)
- [accelerated backend architecture](../compiler/graphics/accelerated_shared_ui_backend_architecture.md)
