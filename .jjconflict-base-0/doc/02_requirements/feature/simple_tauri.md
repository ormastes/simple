# web_ui — Requirements

**Feature:** Tauri-like Desktop Application Framework in Simple (`std.web_ui`)
**Date:** 2026-03-28
**Status:** Implemented (Phase 8)

## Motivation

Build a **pure-Simple desktop application framework** inspired by Tauri, using the existing browser engine (`examples/browser/`) as the webview backend. Unlike Tauri (Rust + system webview) or Electron (Node + Chromium), SimpleTauri is a **single-language stack** where both the backend logic and the rendering engine are Simple code.

### Why Not Just Use Tauri?

- Tauri depends on system webviews (WebKitGTK, WebView2, WKWebView) — inconsistent behavior across platforms
- Tauri requires Rust for the backend — SimpleTauri uses Simple everywhere
- IPC in Tauri is JSON serialization across a language boundary — SimpleTauri can use **direct typed dispatch** since both sides are Simple

## Scope

### In Scope

1. **App Shell** — `SimpleApp` class: lifecycle (init, run, quit), window management, event loop
2. **Window Management** — Create/destroy/resize/fullscreen windows backed by SDL2, multi-window support
3. **Webview Backend** — Integrate browser engine's render pipeline (HTML parse → DOM → CSS → layout → paint → composite → GPU → present) into SDL2 windows
4. **Command System** — Register backend Simple functions callable from frontend JS/HTML via `invoke("cmd_name", args)`, returning typed results
5. **Event Bus** — Global `emit/listen/unlisten` pub/sub between backend and frontend (bidirectional)
6. **Capability/Permission System** — SDN config declaring which commands/APIs each window can access, enforced at runtime
7. **Plugin Architecture** — MDSOC capsule-based plugins (file system, HTTP, shell, clipboard, notifications) with capability-gated access
8. **Menu System** — Application menus rendered via the browser engine (custom-rendered, not native OS menus)
9. **Native UI Mode** — Alternative to HTML: use Simple's UI framework (`src/lib/common/ui/`) with SDN widget definitions for native-feeling apps
10. **Configuration** — SDN-based app config (window defaults, security policy, plugin config)

### Out of Scope (v1)

- System tray (requires platform-specific FFI beyond SDL2)
- Native OS file dialogs (use custom-rendered dialogs)
- OS notifications (use in-app notification widgets)
- Auto-updater
- App bundler/packager (.deb, .msi, .app)
- Mobile targets (iOS/Android)
- Hardware-accelerated GPU backend (keep software rasterizer for v1)
- Real font rendering (keep block-based for v1; font atlas is a follow-up)

## I/O Examples

### Example 1: Minimal App (HTML frontend)

```simple
use std.tauri.app

fn main():
    app := SimpleApp(
        title: "Hello SimpleTauri",
        width: 800,
        height: 600,
        html: "<h1>Hello from SimpleTauri!</h1><button onclick=\"invoke('greet', {name: 'World'})\">Greet</button>"
    )

    app.command("greet", \args:
        name := args.get("name") ?? "Unknown"
        "Hello, {name}!"
    )

    app.run()
```

### Example 2: Multi-window with Events

```simple
use std.tauri.app
use std.tauri.window

fn main():
    app := SimpleApp(title: "Multi-Window Demo")

    main_win := app.create_window(
        label: "main",
        title: "Main Window",
        width: 1024,
        height: 768,
        url: "app://index.html"
    )

    app.command("open_settings", \args:
        settings_win := app.create_window(
            label: "settings",
            title: "Settings",
            width: 400,
            height: 300,
            html: "<h2>Settings</h2>"
        )
        app.emit("settings_opened", nil)
        "ok"
    )

    app.listen("theme_changed", \event:
        app.emit_to("main", "refresh_theme", event.payload)
    )

    app.run()
```

### Example 3: Native UI Mode (no HTML)

```simple
use std.tauri.app
use std.tauri.native_ui

fn main():
    app := SimpleApp(title: "Native UI App", mode: AppMode.NativeUI)

    app.ui(\ctx:
        column():
            text("Counter App")
            count := ctx.state("count", 0)
            text("Count: {count.get()}")
            row():
                button("Increment", on_click: \: count.set(count.get() + 1))
                button("Reset", on_click: \: count.set(0))
    )

    app.run()
```

### Example 4: File Explorer Plugin

```simple
use std.tauri.app
use std.tauri.plugin.fs

fn main():
    app := SimpleApp(title: "File Explorer")
    app.plugin(FsPlugin(scope: ["/home/user/documents"]))

    app.command("list_files", \args:
        path := args.get("path") ?? "."
        fs.read_dir(path)
    )

    app.command("read_file", \args:
        path := args.get("path") ?? ""
        fs.read_text(path)
    )

    app.run()
```

### Example 5: Capability-Gated App

```
# app.sdn (config)
app:
    name: "Secure App"
    windows:
        main:
            title: "Main"
            url: "app://index.html"
            capabilities: [core, fs_read]
        sandbox:
            title: "Untrusted Content"
            url: "app://sandbox.html"
            capabilities: [core]

capabilities:
    core:
        commands: [greet, get_version]
    fs_read:
        commands: [list_files, read_file]
        scope:
            paths: ["/home/user/documents"]
```

## Acceptance Criteria

1. **AC-1:** `SimpleApp` can create an SDL2 window and render HTML content using the browser engine's pipeline
2. **AC-2:** `app.command()` registers a Simple function callable from frontend JS via `invoke()`
3. **AC-3:** `app.emit()` / `app.listen()` provide bidirectional event pub/sub
4. **AC-4:** Multi-window support with per-window capability restrictions
5. **AC-5:** SDN-based app configuration parsed at startup
6. **AC-6:** Plugin system using MDSOC capsules with capability-gated access
7. **AC-7:** Native UI mode works without HTML (using Simple UI framework)
8. **AC-8:** Event loop runs at stable frame rate with input handling
9. **AC-9:** App lifecycle (init → running → shutdown) with cleanup
10. **AC-10:** At least 3 built-in plugins: fs, http, clipboard

## Dependencies

### Existing Modules (reuse directly)

| Module | Path | Used For |
|--------|------|----------|
| SDL2 windowing | `src/lib/nogc_sync_mut/io/window_ffi.spl` | Window creation, events, framebuffer present |
| Browser engine | `examples/browser/` | HTML/CSS/DOM/JS render pipeline |
| UI framework | `src/lib/common/ui/` | Native UI mode widgets, reactive state, sessions |
| Compositor | `src/lib/nogc_sync_mut/compositor/` | Layer compositing, damage tracking |
| HTTP client | `src/lib/nogc_sync_mut/http/` | HTTP plugin |
| File system | `src/lib/nogc_sync_mut/fs/` | FS plugin |
| Shell | `src/lib/nogc_sync_mut/shell/` | Shell plugin |
| MDSOC capsules | `src/compiler/85.mdsoc/` | Plugin isolation |
| SDN parser | `src/lib/sdn/` | Config files |

### New Code Required

| Component | Estimated Size | Difficulty |
|-----------|---------------|------------|
| App shell + lifecycle | ~200 lines | 2/5 |
| Window manager | ~300 lines | 3/5 |
| Command registry + dispatch | ~200 lines | 2/5 |
| Event bus | ~150 lines | 2/5 |
| Browser-to-SDL2 bridge | ~400 lines | 4/5 |
| Capability enforcer | ~250 lines | 3/5 |
| Plugin trait + loader | ~200 lines | 3/5 |
| Native UI backend | ~300 lines | 3/5 |
| SDN config loader | ~150 lines | 2/5 |
| Built-in plugins (fs, http, clipboard) | ~400 lines | 2/5 |
| **Total** | **~2,550 lines** | |

## Related Documents

- Research: `doc/01_research/simple_tauri.md`
- Plan: `doc/03_plan/simple_tauri.md` (Phase 4)
- Design: `doc/05_design/simple_tauri.md` (Phase 4)
- Browser architecture: `examples/browser/capsule.sdn`
- UI framework: `src/lib/common/ui/`
