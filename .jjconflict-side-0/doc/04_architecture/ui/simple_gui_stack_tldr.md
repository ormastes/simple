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
- Startup dynSMF: file IO, net IO, render2d, web renderer, GUI renderer,
  TUI renderer, and UI HTML use checked `build/dynsmf/*.smf` autoload with
  arg/env opt-outs
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
  URI-only image commands fail closed until resolved-image input is supplied;
  the advanced path renders caller-provided resolved ARGB buffers, including
  Vulkan nearest-neighbor COPY and checked transparent src-over after opaque
  initialization, but does not decode PNG, JPEG, or WebP bytes.
- Engine2D split contract: `src/lib/nogc_async_mut/gpu/engine2d/backend_lane.spl`.
- No-GC Draw IR runtime queue owner:
  `src/lib/nogc_async_mut/gpu/engine2d/draw_ir_runtime_queue.spl`.
- Host/GPU event-flow evidence uses
  `src/lib/nogc_async_mut/gpu/engine2d/host_gpu_event_queue.spl` for event
  decision/submit/receipt evidence plus Pure Simple queue lifecycle state and
  `src/lib/nogc_async_mut/gpu/engine2d/host_gpu_draw_ir_event_flow.spl` for Draw
  IR routing with explicit forward/backward phase evidence. Unresolved targets,
  stale target-cache events, and host-semantic mutation stay on host; coarse
  render/effect batches may queue to GPU and report a backward completion
  receipt.
- Web-render artifact diagnostics now carry queue submit/drain status, packet
  id, drained count, backend handle, payload size/hash/text, and reason through
  `WebRenderArtifact.queue_*`, plus readback backend/source/pixel-count/checksum/reason
  metadata; browser frames mirror those fields as `BrowserBackend.last_artifact_queue_*` and
  `BrowserBackend.last_artifact_gpu_readback_*`.
- Production status is evidence-gated: adapter evidence proves routing
  decisions, runtime queue emission proves packets/counters/drain status plus
  bounded payload text receipts, backend readback proves backend-specific
  submit/sync/readback, and
  `scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs`
  proves the joined GUI/web frame path. Focused BrowserBackend specs now prove
  host event ingress/dispatch/render telemetry, queue metadata/payload propagation,
  conservative first-frame and cached-frame render timing budgets, a
  positive BrowserBackend backend handle propagated from
  `Engine2DReadback.backend_handle`, Engine2D readback
  source/pixel-count/checksum/reason metadata, and cache-hit reset.
  CUDA/OpenCL/Metal/OpenGL/ROCM/Vulkan
  device-readback branches preserve concrete handles when initialized; WebGPU
  preserves `surface_upload` handles for upload provenance, not device-readback
  proof; DirectX preserves `swapchain_present` handles for presentation
  provenance, not device-readback proof; CPU, cache, and not-requested fallbacks
  stay handle `0`. Synthetic Vulkan handle `7` remains isolated runtime queue
  roundtrip evidence.
- Current standalone backend readback reports: CUDA generated 2D and OpenCL
  generated 2D pass with `submit_attempted=true` and
  `readback_available=true`; Linux Metal and ROCm/HIP generated 2D are typed
  unavailable with submit/readback false. Standalone backend fixtures are not by themselves proof that
  `src/app/ui.browser/backend.spl` drains GUI/web frames through the host/GPU
  runtime queue. The joined GUI/web proof is the separate Vulkan BrowserBackend
  production wrapper lane.
- Production GUI/web GPU rendering is evidence-gated: the canonical wrapper is
  the source of truth for whether the joined event queue -> runtime packet ->
  positive backend-handle receipt -> backend device readback path currently passes.
  Its Readback Matrix exposes submit/readback columns, and its Spark/normal-LLM
  table exposes a compact `linux_gui_web` event id / queue packet / readback
  source / checksum row plus DirectX native verdict and gate fields.
  Linux Metal and ROCm/HIP remain typed unavailable without matching host
  runtimes.
- SimpleOS RV64 desktop uses the same backend-readback bar:
  `simpleos_engine2d_vulkan_required_evidence_keys()` requires Vulkan backend,
  `vulkan-engine2d` scene, Simple2D command status, Vulkan device name,
  viewport, checksum, nonblank readback, and QEMU GPU readback before the QEMU
  Simple2D/Engine2D path can pass.
- `qemu_riscv64_engine2d_vulkan_bridge_plan()` is the SimpleOS bridge target:
  QEMU `virtio_gpu` drawing, Vulkan Engine2D processing, `draw_ir-to-engine2d`
  Simple2D commands, device readback, QMP screendump readback,
  `capture-simple`, and the shared WM comparison scene are all required.
- Windows artifact normalization uses
  `scripts/check/check-simpleos-engine2d-renderdoc-evidence.ps1` to emit
  Engine2D Vulkan, SimpleOS RenderDoc, and bridge rows for the aggregate
  checker. `simpleos_engine2d_vulkan_bridge_status` is diagnostic; live
  completion still depends on the Engine2D Vulkan/readback gate.
- Add `-ProbeHostVulkan` to that normalizer or to the combined SimpleOS wrapper
  for Windows host readiness rows. Passing `vulkaninfo` and installed browsers
  are diagnostics only; SDK tools, focused browser backing, SimpleOS readback,
  and RenderDoc capture still gate Vulkan claims.
- Current runtime gaps: compiler/interpreter GPU packets consume the active
  backend handle, submit at lane begin, and complete after lane end, but still
  complete as typed `UNAVAILABLE` when none is registered; `SUBMITTED` is
  observable through the runtime submit/complete path; Pure Simple MIR
  HostGpuLane cleanup now covers body early returns, and the interpreter pops
  block scopes on statement/value errors, while arbitrary MIR runtime
  instruction traps still need cleanup-frame or unwind support; Rust/C capacity
  is `1024` with
  overflow coverage; the Draw IR runtime bridge now carries a deterministic
  payload descriptor plus one-batch serialized SDN payload, and low-level
  runtime packets preserve payload byte size/hash/text through completion/drain
  receipts; broader backend/session command-buffer receipts remain follow-up
  production work.
- Pure Simple GUI/default Simple2D rendering enters through the shared Engine2D
  backend lane planner. GUI code should not bypass the lane planner with direct
  GPU calls. Engine2D env overrides and the Vulkan GLSL opt-in gate use the
  stdlib I/O facade rather than local runtime env declarations.
- Engine2D backend preference: `backend_full_preference_order()` puts explicit
  native surfaces (`baremetal`, `virtio_gpu`) before Metal/CUDA/ROCm,
  Qualcomm, Vulkan, DirectX, and portable fallback lanes; the automatic probe
  order starts at Metal because native surfaces need a preinitialized
  framebuffer.
- SimpleOS x86_64, AArch64, and RV64 production desktops all lower the shared
  WM scene through Draw IR and `Engine2dWmFrameExecutor`. RV64 VirtIO mode
  discovery/present is an architecture transport facade, not a private render
  path.
- Font offload uses `engine2d_font_offload_backend_order()` for vector and
  bitmap glyph preparation, with readback/checksum parity against the CPU
  reference path before a backend is treated as valid.
- Web semantic/layout preserves inherited/cascaded `font-family` in existing
  Draw IR computed-style metadata. Draw IR owns no font bytes or atlas material.
  Execution stays on the bitmap default until web layout and Engine2D paint
  share one resolved provider/metric identity; paint-only TTF selection is an
  invalid shortcut. Production web pixels and SimpleOS image packaging remain
  open; SimpleOS needs one hash-pinned immutable-data manifest shared by its
  image builders.
- Resolved-font target: `FontRenderer.resolve_font_metrics` supplies one stable
  manifest identity plus exact advances to Web layout; Draw IR carries only
  `font-family`/`font-identity`/`font-advance-widths`, and Engine2D verifies the
  same identity before paint. Legacy commands without identity remain bitmap.
- Opt-in `Engine2D.load_font` is separate: CPU `spl_fonts` raster/layout,
  per-engine glyph cache, then one tight payload blended by the drawing backend.
  UTF-8 local paths are supported; the face/layout is a serialized
  process-global singleton. The unspecified default remains bitmap text.
- Text fallback hot path: AA glyph loops touch only glyph coverage pixels; the
  prefilled buffer owns advance gaps and font-size padding rows as background.
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
| `src/lib/common/ui/window_scene_draw_ir.spl` | WM scene → ordered Draw IR composition with top-level content IMAGE projection |
| `src/lib/common/ui/wm_runtime_dispatch.spl` | WM dispatch command adapter for host shells |
| `src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl` | Engine2D Draw IR executor (rect/text/resolved image, present, CPU fallback) |
| `src/lib/gc_async_mut/gpu/engine2d/draw_ir_runtime_adv.spl` | Optional host runtime-queue adapter, separate from the baremetal core closure |
| `src/os/compositor/engine2d_wm_frame_executor.spl` | Shared x86_64 production/AArch64 boot-desktop WM DrawIR/Engine2D frame owner; invalid or nested-unresolved content fails closed |
| `src/lib/nogc_async_mut/gpu/engine2d/backend_lane.spl` | Drawing vs processing lane split |
| `src/app/ui.render/capability.spl` | Implementation-free renderer capabilities |
| `src/app/ui.render/widgets.spl` | TUI-only compatibility renderer shim |
| `src/app/ui.render/html_widgets.spl` | HTML-capable widget renderer |
| `src/app/ui.render/css.spl` | Component-scoped CSS selector |
| `src/app/ui/dependency_closure_gate.spl` | Exact-prefix UI dependency closure gate |
| `src/os/smf/dynsmf_session.spl` | checked dynSMF manifest/session/unload |
| `src/app/startup/dynsmf_autoload.spl` | CLI/env dynSMF startup policy |
| `src/app/ui.web/wm_runtime_bridge.spl` | Web host WM runtime bridge |
| `src/app/ui_shared_mdi/main.spl` | backend-neutral MDI IPC demo with env toggles through `app.io.env_ops.env_get` |

## Host Shells

Web, TUI, Standalone, Tauri, Electron, Chromium, Browser, VS Code, CLI, IPC,
MCP, Render, Test API — all thin. GUI policy stays in Simple.

## Operational Notes

- startup: probe plugin/backend capabilities once, cache the result, and report
  unavailable states explicitly.
- hot path: no full-tree scans, repeated file reads, subprocess retry loops, or
  per-frame device probing.
- dependency gates: non-capable lanes prove no HTML/CSS/GUI/web closure.
- dynSMF startup: enabled artifacts must exist and start with `SMF\0` before
  `smf_dlopen`.
- cache/index: cache keys include backend id, device capability version, Draw IR
  schema version, source kind/id, artifact version, style/font/image versions,
  style revision, and fallback reason metadata.
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
