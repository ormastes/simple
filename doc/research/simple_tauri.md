# SimpleTauri — Research

**Feature:** Tauri-like Desktop Application Framework in Simple
**Date:** 2026-03-28
**Related:** `doc/plan/requirement/simple_tauri.md`

## 1. Tauri Architecture Analysis

### Core Components

| Tauri Component | Role |
|----------------|------|
| **tauri** (crate) | Main framework: config, runtime, API host, script injection |
| **WRY** | Cross-platform webview wrapper (WebKitGTK/WebView2/WKWebView) |
| **TAO** | Cross-platform window management (fork of winit) |
| **tauri-bundler** | Packaging (.deb, .msi, .app, .AppImage) |

### Process Model

- **Core Process** (Rust): Full OS access, manages windows/tray/menus, hosts commands, routes IPC
- **WebView Process(es)**: One per window, renders HTML/CSS/JS, sandboxed, IPC-only communication

### IPC: Commands & Events

- **Commands** (request/response RPC): Frontend `invoke('name', {args})` → Backend `#[tauri::command] fn name(args) -> Result<T,E>`. JSON serialization.
- **Events** (pub/sub fire-and-forget): `emit('event', payload)` / `listen('event', callback)`. Global or window-scoped.

### Security Model

- **Capabilities**: JSON files declaring which commands each window can invoke
- **Scopes**: Fine-grained restrictions (e.g., allowed file paths, HTTP URLs)
- **Runtime Authority**: Core process checks capabilities before dispatching IPC
- **Isolation Pattern**: Optional iframe sandbox with SubtleCrypto-encrypted IPC

### Plugin System

Official plugins: File System, Store, SQL, Dialog, Clipboard, Notifications, Shell, HTTP, WebSocket, Updater, Logging, etc. Each defines permissions, commands, and lifecycle hooks.

## 2. Existing Simple Building Blocks

### 2.1 Browser Engine (`examples/browser/`)

**170 .spl files, ~48K lines.** MDSOC 3-dimension architecture (entity/feature/transform).

**11-layer render pipeline:**
0. Network (DNS, TLS, HTTP/1.1+2, WebSocket, Fetch, Cache, Cookies, CORS)
1. Parser (HTML5 tokenizer ~30 states, tree builder 22 insertion modes, CSS Syntax L3)
2. DOM (W3C Level 2 Core, querySelector, tree manipulation, traversal)
3. Style (Cascade, computed values, inheritance, CSS variables, animations)
4. Layout (Block CSS 2.1, Flexbox, Grid, Table, Float, Inline, Scroll, Text shaping)
5. Paint (Display list, z-index, stacking contexts, clip, opacity)
6. Composite (Layer tree, tile manager, damage tracking, scroll compositor)
7. GPU (Software rasterizer, surface pool, swapchain, command buffer, texture cache)
8. Script (Full JS engine: lexer, parser, interpreter, bytecode VM, GC, Web API bindings)
9. Browser (Tab manager, navigation, history, bookmarks, downloads, DevTools)
10. Sandbox (Process manager, capability broker, site isolation, CSP)

**Key for SimpleTauri:** Layers 1-8 form a complete HTML-to-pixels pipeline. The `RenderPipeline` class (`transform/pipeline.spl`) orchestrates: parse → style → layout → paint end-to-end.

### 2.2 SDL2 Windowing (`src/lib/nogc_sync_mut/io/window_ffi.spl`)

- Window create/destroy/resize/fullscreen, event polling (keyboard, mouse, touch)
- Framebuffer present via `window_present_rgba` (packed RGBA pixel array)
- `WindowConfig`, `EventLoop`, `EventBatch` structs
- C runtime: `src/runtime/runtime_sdl2.c`

### 2.3 UI Framework (`src/lib/common/ui/` — 37 files)

- **Widgets:** 20+ widget types including panels, buttons, tables, tabs, trees, dialogs, tooltips
- **Builder API:** Declarative `column()`, `row()`, `button()`, `dialog()`, etc.
- **Reactive state:** `ReactiveValue`, `ReactiveStore` with observer pattern
- **Tree diffing:** `diff_trees` → `UIPatch` list
- **Lifecycle:** Mount/unmount/update events with registry
- **Surface manager:** Multi-window/panel abstraction with handle validation
- **UISession:** Central shared-state container unifying CLI/TUI/GUI
- **Async event loop:** Channel-based UI event bus
- **RenderBackend trait:** `init/shutdown/render/poll_event/viewport` — only `NoneBackend` implemented

### 2.4 Compositor (`src/lib/nogc_sync_mut/compositor/` — 10 files)

- Layer tree, GPU surfaces with pixel buffers, surface pool, swapchain
- Software rasterizer (fill rect, text blocks, lines, borders, alpha blending)
- Damage tracking, tile management, frame scheduling, stacking contexts
- **Explicitly "no browser-specific dependencies"** — designed for reuse

### 2.5 2D Engine (`src/lib/nogc_sync_mut/engine/` — ~55 files)

- Engine2D with game loop (Input → Update → Physics → Late Update → Render)
- Software and GPU renderer modes, SDL2 window integration
- Already presents framebuffer via `window_present_rgba`

### 2.6 Other Relevant Modules

| Module | Path | Notes |
|--------|------|-------|
| HTTP client | `src/lib/nogc_sync_mut/http/` | Request/response, headers, cookies |
| File system | `src/lib/nogc_sync_mut/fs/` | FS operations with file watching |
| Shell | `src/lib/nogc_sync_mut/shell/` | Command execution |
| Networking | `src/lib/nogc_sync_mut/net/` | TCP, UDP, TLS, DNS, WebSocket |
| SDN parser | `src/lib/sdn/` | Config format (replaces JSON/YAML) |
| GPU module | `src/lib/gc_async_mut/gpu/` | Backend-agnostic GPU (CUDA, Vulkan, etc.) |
| Event loop | `src/lib/nogc_async_mut/io/event_loop.spl` | epoll/kqueue abstraction |
| Clipboard | `src/lib/common/office/clipboard.spl` | In-process only (not OS clipboard) |
| MDSOC | `src/compiler/85.mdsoc/` | Compile-time capsule isolation |

## 3. Architectural Advantages Over Tauri

### 3.1 No Language Boundary in IPC

Tauri serializes everything to JSON to cross the Rust↔JS boundary. In SimpleTauri, both backend and rendering are Simple code. The "IPC" can be:
- **Direct function dispatch** for same-process mode (zero overhead)
- **Typed enum messages** for multi-process mode (type-safe, no JSON)

### 3.2 No System Webview Dependency

Tauri depends on OS having an up-to-date webview (problematic on Linux with older WebKitGTK). SimpleTauri bundles its own renderer — consistent behavior across platforms.

### 3.3 Unified Security Model

The browser engine's MDSOC capsule system + capability broker provides **compile-time** module isolation, stronger than Tauri's runtime-only capability checks.

### 3.4 Single Binary

Like Tauri (unlike Electron), the result is a single compiled binary. Unlike Tauri, there's no webview DLL/dylib dependency either.

### 3.5 Dual Frontend Mode

Unique to SimpleTauri — developers can choose:
- **HTML mode**: Familiar web tech, rendered by browser engine
- **Native UI mode**: Simple's reactive UI framework with SDN widget definitions
- **Hybrid**: Mix both in the same app

## 4. Gaps and Risks

### 4.1 Critical Gap: Browser-to-SDL2 Bridge

The browser engine writes to in-memory pixel buffers (`List<i64>`) but has **no platform window integration**. The Engine2D already does `window_present_rgba` for its game loop. The bridge needs to:
1. Create an SDL2 window
2. Run the browser's `RenderPipeline` to produce pixels
3. Call `window_present_rgba` to present the framebuffer
4. Route SDL2 input events back through the browser's UI-to-DOM bridge

This is the **most critical integration piece** (~400 lines, difficulty 4/5).

### 4.2 Font Rendering

Both the compositor and browser rasterizers use **block-based character drawing** (8px rectangles). Real font rendering needs a glyph atlas (FreeType/stb_truetype). This is out of scope for v1 but will limit visual quality.

### 4.3 Performance

Software rasterization will be slower than hardware-accelerated rendering. For v1 this is acceptable for typical app UIs. The architecture has clear extension points for GPU acceleration later (the code notes "Future: std.gpu + Vulkan FFI").

### 4.4 Browser Engine Maturity

The browser engine is architecturally complete but some subsystems operate on simulated data:
- `BrowserProcess.sample_document_for()` returns hardcoded HTML
- `setTimeout` returns immediately, `Math.random` returns 0.5
- Promise is stubbed, JIT is a placeholder

For SimpleTauri v1, the core pipeline (parse → DOM → style → layout → paint → composite → rasterize) works. The JS engine handles basic interactivity.

### 4.5 RenderBackend Gap

The UI framework defines a `RenderBackend` trait but only `NoneBackend` exists. SimpleTauri's native UI mode needs a real backend that renders widgets to SDL2 surfaces via the compositor.

## 5. Recommendations

### 5.1 Library Location

Place in `src/lib/nogc_sync_mut/tauri/` as a stdlib module (`use std.tauri.*`).

### 5.2 Architecture

```
std.tauri
  app.spl          — SimpleApp, AppConfig, lifecycle
  window.spl       — WindowManager, WindowHandle, WindowConfig
  command.spl      — CommandRegistry, CommandHandler, invoke dispatch
  event.spl        — EventBus, listen/emit/unlisten
  capability.spl   — CapabilityChecker, Permission, Scope
  plugin.spl       — PluginTrait, PluginRegistry, lifecycle hooks
  config.spl       — SDN config loader (app.sdn parsing)
  bridge/
    webview.spl    — Browser engine → SDL2 surface bridge
    native_ui.spl  — UI framework → SDL2 surface bridge (RenderBackend impl)
    input.spl      — SDL2 events → browser/UI event dispatch
  plugin/
    fs.spl         — File system plugin
    http.spl       — HTTP client plugin
    clipboard.spl  — Clipboard plugin (in-process + OS via SDL2)
  capsule.sdn      — MDSOC capsule config for module isolation
```

### 5.3 Phased Delivery

| Phase | Components | Milestone |
|-------|-----------|-----------|
| **v0.1** | App shell + SDL2 window + browser bridge + basic render | "Hello World" HTML in SDL2 window |
| **v0.2** | Command system + event bus + input handling | Interactive apps with backend logic |
| **v0.3** | Multi-window + capabilities + SDN config | Secure multi-window apps |
| **v0.4** | Plugin system + built-in plugins (fs, http, clipboard) | Full plugin ecosystem |
| **v0.5** | Native UI backend + hybrid mode | Non-HTML app development |

### 5.4 Key Design Decision: Same-Process vs Multi-Process

Tauri uses multi-process (core + webview). SimpleTauri should support **both**:
- **Same-process** (default): Simpler, direct function calls, good for trusted apps
- **Multi-process** (opt-in): Use browser's existing `ProcessManager` + IPC for untrusted content

## 6. Related Work in This Codebase

- Browser MDSOC config: `examples/browser/capsule.sdn`
- Browser render pipeline: `examples/browser/transform/pipeline.spl`
- Browser IPC types: `examples/browser/entity/ipc/`
- Browser capability broker: `examples/browser/feature/sandbox/capability_broker.spl`
- Engine2D game loop (SDL2 present pattern): `src/lib/nogc_sync_mut/engine/core/game_loop.spl`
- UI framework app: `src/lib/common/ui/app.spl`
- UI backend trait: `src/lib/common/ui/backend.spl`
