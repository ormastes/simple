# UI Architecture

This is the entrypoint for Simple UI, GUI, web-connected UI, rendering, and UI
test architecture.

## Scope

The UI architecture owns semantic UI state, widget identity, layout intent,
event routing, accessibility state, render IR, Draw IR, shell adapters, and UI
test access. Web framework routes and persistence are separate app concerns, but
the web framework connects to UI through the `ui.web` protocol and shared UI
access snapshots.

## Stack

```text
Simple app state
  -> UI semantics: widget id, text, role, state, action names
  -> layout/style intent
  -> UI access snapshot
  -> WebRender IR / Draw IR
  -> Engine2D / backend plugin / CPU oracle
  -> shell adapter: TUI, browser, Electron, Tauri, SimpleOS WM
```

## Target Layer Hierarchy (2026-07-05)

The stack diagram above describes data flow. This tree describes containment
and default/non-default backend selection — the maintainer-authoritative
to-be shape every other UI/GUI architecture doc must agree with:

```text
ui
├── tui
└── gui
    ├── electron wrapper + electron        # non-default backend; MUST support internal windows
    ├── core                               # simple gui core: internal window rendering (WM uses this)
    └── web server ui                      # DEFAULT backend
        └── web
            ├── chrome wrapper + chrome    # web renderer delegating to Chrome (comparison/capture today)
            └── core                       # CORE simple web renderer (HTML/CSS parse -> layout -> paint)
                └── simple 2d renderer     # engine2d
                    ├── cpu simd (x86, riscv, arm/aarch64)
                    ├── directx
                    ├── vulkan
                    └── metal
```

WM renders through `gui/core` (internal window rendering); GUI itself
expresses widgets as HTML/CSS elements that flow down through `web server
ui -> web -> core` to Engine2D. Web (`web server ui`) is the default GUI
backend; Electron is a non-default, thicker host wrapper. The web renderer
is designed to switch between the `chrome` backend and the `simple 2d
renderer` (`core`) backend; Chrome, Electron, and the simple-2d backend must
all support Metal render-log capture so their output is comparable.

| Node | Status | Primary source path(s) |
|---|---|---|
| `ui` (root) | Implemented | `src/app/ui.*` (14 shell targets, see Host Shell Targets in `simple_gui_stack.md`) |
| `tui` | Implemented | `src/app/ui.tui/{app,async_app,standalone,backend,input,screen}.spl` |
| `gui` (widget tree, event routing, layout intent) | Partial — no single `ui.gui` module; the GUI AST/event layer is composed from several files | `src/lib/common/ui/{draw_ir,window_scene,patch,access}.spl`, `src/app/ui.render/{html_widgets,capability}.spl`, `src/app/ui.standalone` |
| `gui/electron wrapper + electron` | Partial — single-`BrowserWindow` host wrapper; no internal-window (MDI-in-one-window) rendering yet; `notify()`/`open_file_dialog()` are dev-preview stubs that print and return `true` instead of calling Electron's `Notification`/`dialog` API | `src/app/ui.electron/main.spl:135-149` (`# TODO(v4-dev-preview)`), `src/app/ui.electron/bridge.js:943` (`mainWindow = new BrowserWindow(...)`, one window) |
| `gui/core` (internal window rendering, WM) | Implemented | `src/lib/common/ui/window_scene.spl`, `window_scene_draw_ir.spl`; `src/os/compositor/wm_scene.spl`; `src/os/hosted/hosted_entry.spl`; gate `scripts/check/check-shared-wm-renderer-unification-evidence.shs` |
| `gui/web server ui` (default) | Implemented | `src/app/ui.web/{server,ui_routes,wm_bridge,taskbar_runtime,session_token}.spl` per `ui_web_protocol.md` |
| `web` | Implemented | `src/lib/gc_async_mut/gpu/browser_engine/*` |
| `web/chrome wrapper + chrome` | Partial — real Chrome capture/compare tooling exists, but no production path where the web renderer delegates *live* rendering to Chrome; `app.ui.chromium` is Simple's own canonical engine wearing Chromium naming (ADR-002), not a real-Chrome backend | `tools/chrome-live-bitmap/capture_html_argb.js`; `scripts/check/check-macos-metal-render-log-compare.shs`, `check-electron-generated-gui-web-parity-matrix-evidence.shs`; `doc/04_architecture/adr/ADR-002-canonical-browser-engine.md` |
| `web/core` (CORE simple web renderer) | Implemented, with a known gap: fixture-detection/faking branches remain in the Engine2D-facing wrapper (being removed) | `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl` (real, ~8.7k lines); `simple_web_engine2d_renderer.spl:401,860,912` (`"deterministic compatibility fixture"`, fixture/heuristic discriminator) |
| `web/core/simple 2d renderer` (engine2d) | Implemented | `src/lib/gc_async_mut/gpu/engine2d/*` |
| `... cpu simd (x86, riscv, arm/aarch64)` | Partial — real NEON + SSE2 row kernels exist for arm64/x86_64; RISC-V (RVV) and AVX2/AVX512 are not implemented; the Simple-level `backend_cpu_simd_opt.spl` (`SimdCapability`/`CpuSimdRenderer`) is an orphaned label-only simulator (no callers) whose `detect()` hardcodes `for_arch("x86_64")` regardless of host arch | `src/compiler_rust/runtime/src/value/engine2d_simd_ops.rs` (real NEON/SSE2); `src/lib/gc_async_mut/gpu/engine2d/backend_cpu_simd_opt.spl` (unwired simulator) |
| `... directx` | Partial — native D3D11 on Windows; DXVK/vkd3d-over-Vulkan on Linux; no macOS path | `src/lib/gc_async_mut/gpu/engine2d/backend_directx.spl` |
| `... vulkan` | Implemented | `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan*.spl`; canonical Linux gate `scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs` |
| `... metal` | Implemented | `src/lib/gc_async_mut/gpu/engine2d/backend_metal*.spl`, `metal_session.spl`; `scripts/check/check-macos-metal-render-log-compare.shs` |

Marker key: **Implemented** = the described behavior runs and has evidence;
**Partial** = real code exists but does not yet meet the target claim in
full; **Missing** = target node has no corresponding implementation. Every
"Partial"/"Missing" row above is a current gap versus the target, not an
implemented capability — see `simple_gui_stack.md` for the electron/chrome
detail and `engine_2d.md` for why a second, unrelated "Engine2D" document
exists for the baremetal/QEMU lane.

## Test And Location Model

UI tests assert both semantic state and positional/location data:

| Data | Source |
|------|--------|
| Stable identity | `canonical_id`, `surface_id`, `widget_id` |
| State | visible, focused, enabled, selected, text value |
| Position | geometry props such as `x`, `y`, `width`, `height` |
| Source/test location | SPipe spec path, generated spec doc path, scenario name |
| Pixel location | bitmap/readback coordinates and dirty regions |

Semantic assertions should use SGTTI or the shared `/api/test/*` vocabulary.
Pixel assertions should use bitmap/readback evidence. A UI test that depends on
layout must name both the semantic node and the positional property it checks.

## Ownership

| Area | Owner docs |
|------|------------|
| Stack and rendering | `simple_gui_stack.md`, `engine_2d.md`, `drawing_stack.md` |
| Semantic contract | `shared_ui_contract.md`, `ui_access_protocol.md` |
| Web transport | `ui_web_protocol.md`, `web/00_web_framework_architecture.md` |
| UI tests | `ui_test_architecture.md`, `ui_test_architecture_tldr.md` |
| dynSMF UI dependencies | `low_dependency_ui_dynsmf.md` |
| Graphics and 3D | `graphics/simple_3d_graph_ir.md`, `graphics/graphical_icon_system.md` |

## Invariants

- Simple owns UI state, event routing, layout policy, accessibility, and dirty
  region truth.
- Shells render or transport patches/input; they do not own app state.
- UI test helpers must not fork a third element model. Use `UiAccessNode`,
  `SemanticElementInfo`, or the existing `/api/test/*` element vocabulary.
- Web UI remains connected through shared UI snapshots and patch streams, not
  parallel DOM-only state.

