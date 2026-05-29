# UI Stack Guide — CLI, TUI, GUI on One Session

**Audience:** developers writing an app that targets SimpleOS *and/or*
host operating systems, and anyone picking between `ui.cli`, `ui.tui`,
`ui.render`, `ui.browser`, `ui.electron`, …

**TL;DR**

- One widget tree, one state machine, N backends.
- The shared entry point is `UISession` in `src/lib/common/ui/session.spl`.
- Every `src/app/ui.*` directory is a backend that consumes the same
  session and renders it somewhere (terminal, framebuffer, canvas, …).
- Apps import only `common.ui.*`. They do not know which backend is
  attached.

For the architecture diagram and the four drawing-layer variations
(SimpleOS / host OS / Chromium / Electron), see
[`doc/04_architecture/cross_platform_wm.md`](../04_architecture/cross_platform_wm.md).

## 1. The model: UISession

`UISession` is the single shared-state container. Its contract, from
`src/lib/common/ui/session.spl`:

```
class UISession:
    state: UIState                    # current tree + focus
    store: WidgetStore                # stable widget identities
    viewport: Viewport                # size, scale, dpi
    changelog: ChangeLog              # retained diff log
    lifecycle: LifecycleRegistry      # mount/unmount hooks
    surfaces: SurfaceManager          # named surfaces (main, popover, …)
    profile_resolver: ProfileResolver # layout profiles per device
    profile_sets: [ProfileSetEntry]
    capability_policy: CapabilityPolicy?
```

> *"All state transitions flow through the session, enabling shared
> state across CLI, TUI, and GUI backends."*

Apps never read or write the compositor, framebuffer, or terminal. They
build a `UITree` via `common.ui.builder`, hand it to a session, and
observe events. A backend picks up the session and projects it.

The **diff loop** is the same for every backend:

```
app state  ──update──▶  UITree ──diff──▶  Patch[] ──apply──▶  Backend
     ▲                                                            │
     └──────────────── UIEvent ◀──────────────────────────────────┘
```

`common.ui.diff.diff_trees_with` produces patches; `common.ui.patch`
turns patches into backend-agnostic operations; `common.ui.event`
turns backend-native input (keystrokes, pointer events, DOM events)
into the shared `UIEvent` enum.

## 2. Backend inventory

Everything under `src/app/ui.*` is a UISession backend. Pick by where
the pixels (or characters) go.

| App | Renders to | When to pick it | State |
|-----|-----------|-----------------|-------|
| `ui.none` | nothing (event queue only) | headless tests, pure logic runs | stable |
| `ui.test_api` | assertion API | unit tests that poke `UIEvent` | stable |
| `ui.render` | static PPM / text snapshot | golden-image tests, CI artifacts | stable |
| `ui.cli` | stdio + socket observer | scriptable CLI, MCP tools, shell output | stable |
| `ui.ipc` | unix socket / pipe | tool ↔ tool composition, JSON-RPC | stable |
| `ui.mcp` | MCP server | exposing the session to an LLM | stable |
| `ui.vscode` | LSP notifications | VS Code extension view | stable |
| `ui.tui` | termios + cells | interactive terminal UI | stable |
| `ui.tui_web` | browser-hosted TUI | debugging TUI over a webpage | experimental |
| `ui.browser` | HTMLCanvas in a browser | V3 drawing stack (pure Simple in browser) | experimental |
| `ui.web` | DOM via widget→HTML mapping | static-site export | experimental |
| `ui.electron` | Electron BrowserWindow | V4 drawing stack | advisory/dev-preview |
| `ui.tauri` | Tauri webview | alt-desktop shell | experimental |

Pure-Simple GUI — the V1 (SimpleOS baremetal) and V2 (hosted winit)
paths — do **not** live under `src/app/ui.*`. They go through the
compositor in `src/os/compositor/` and reuse the same session; see the
arch doc.

## 3. The backend contract

A backend implements the trait defined in `src/lib/common/ui/backend.spl`.
The mental model:

```
trait Backend:
    # Called once; backend binds to its host (stdio, terminal, surface, …)
    me start(session: UISession)

    # Apply a patch list to the backend's output
    me apply(patches: [Patch])

    # Non-blocking: return any input events the backend has queued
    me poll_events() -> [UIEvent]

    # Called once at shutdown
    me stop()
```

Concrete backends ship richer hooks (async event loops, capability
negotiation, DPI changes) — but any backend that honors `apply` +
`poll_events` participates in the diff loop.

`src/app/ui/main.spl` dispatches to the chosen `ui.<name>` backend.
In auto mode it calls `detect_gui_backend()`
(`src/app/ui/detect.spl`), which honors a `SIMPLE_GUI_BACKEND`
override and otherwise probes the platform and display. Apps should
not name a backend directly; they target the shared session and let
the entry point select the backend.

## 4. CLI / TUI / GUI — what actually differs

| Aspect | CLI (`ui.cli`) | TUI (`ui.tui`) | GUI (compositor or browser) |
|--------|----------------|----------------|-----------------------------|
| Output unit | lines | cells | pixels |
| Layout engine | `common.ui.layout` (text flow) | `common.ui.layout` (grid cells) | `common.ui.layout` (flex/px) |
| Patch renderer | `ui.render` text snapshot / stdio | `screen.spl` cell buffer | `os.compositor` or `browser_backend` |
| Input source | line reader / socket | termios raw | PS/2, winit, DOM, IPC |
| Event pump | blocking read loop | `async_input.spl` | compositor loop or event-loop callback |
| Capabilities | `TEXT_ONLY` | `TEXT_ONLY \| COLOR` | `GRAPHICS \| POINTER \| HIDPI \| …` |

The widget tree, `UIEvent`, lifecycle hooks, state updates, and change
logs are **identical**. The only axis of variation is the projection of
`Patch[]` to an output and the translation of input to `UIEvent`.

### JavaScript-disabled web behavior

`ui.web`, `ui.browser`, and `ui.electron` currently use JavaScript as host
bridge code for DOM rendering, WebSocket transport, and Electron preload
integration. With JavaScript disabled, treat web output as static snapshot or
exported HTML only. Live taskbar/window manipulation, input forwarding, native
window commands, and patch application require the host bridge until a
non-JavaScript transport lands.

### Common web render API

Web-facing GUI backends share the renderer-neutral contract in
`src/lib/common/ui/web_render_api.spl`. `WebRenderRequest` describes the HTML,
CSS, JS, target, surface, viewport, and pixel-output mode; `WebRenderArtifact`
records the resulting HTML, pixel payload, and optional binary artifact
metadata; snapshot, patch, and input envelopes define the transport payloads
used by Web, Electron, Tauri, and the pure Simple browser backend.

Backend adapters may still own their host transport: WebSockets, stdin/stdout
IPC, WebView messages, or framebuffer queues. They should not invent separate
render payload shapes. Electron and Tauri snapshot/patch helpers are regression
tested against the shared web backend helpers in
`test/unit/app/ui/web_render_backend_api_spec.spl`.

For host-bridge parity, `web_render_transport_bundle(req, ...)` builds the
render, input, snapshot, patch, and host-window command JSON from the common API
in one place. Electron and Tauri expose their adapter helpers against that
bundle so webview access through Chromium, Electron, and Tauri stays a transport
choice, not a separate GUI interface.

For static-shell and binary-cache planning, use
`web_render_optimization_profile(req)`. It reports the cache schema, cache key,
static-shell cacheability, dynamic-island count, and render plan. Dynamic
markers currently include `data-simple-dynamic`, `data-live`, `data-ui-patch`,
and WebSocket-backed JS. The first milestone is documented in
`doc/04_architecture/html_css_binary_caching.md` and
`doc/05_design/html_css_binary_caching.md`.

For renderer-owned static HTML reuse, use `src/app/ui.web/render_cache.spl`.
`web_render_cached_static_artifact(cache_dir, req)` stores cacheable static
shells by the shared cache-key digest and returns fresh artifacts for dynamic
island requests. `WebRenderStaticArtifactCache.artifact(req)` adds a hot
in-memory front layer for repeated static shells while preserving the same
request/artifact boundary used by Web, Electron, Tauri, and the pure Simple
browser path.

For static shell binary planning, `web_render_static_shell_binary_artifact(req)`
emits compact `SWBC1` plans with decoded layout payload estimates. Prepare them
with `WebRenderPreparedStaticShellArtifact.prepare(req, encoded)` to validate
once and reuse the generated artifact plus retained draw-command list on
frame-hot paths. Cache hits annotate `WebRenderArtifact.binary_schema`,
`binary_cache_key`, `binary_cache_path`, and size/count fields so host adapters
can transport or inspect the same artifact identity without depending on
`ui.web` internals.

### Practical consequences

- If a feature works in `ui.render`, it works in `ui.tui` and the
  compositor. If it breaks in only one, the bug is in the backend, not
  the widget code.
- Tests should prefer `ui.none` / `ui.test_api` / `ui.render`. They are
  pure, fast, and portable.
- A backend that needs custom behavior (e.g. `ui.tui` fast-path for
  color output) exposes it through `common.ui.capability.Capability`,
  not by bypassing the session.

## 5. Capabilities and layout profiles

Two knobs let one widget tree adapt to many backends without branching
in app code:

- **Capabilities** (`common.ui.capability`, `capability_policy`).
  Declarative: `require_capability(Capability.POINTER)` inside a widget.
  Backends advertise their capabilities at `start`; the policy rejects
  widgets that require something unsupported.
- **Layout profiles** (`common.ui.profile`). A profile is
  `{orientation, dpi, size-class}`. The widget tree picks a profile via
  `compute_profile`; the backend picks the current size-class on every
  viewport change. Apps usually don't interact with this — the builder
  DSL bakes profiles into style tokens (`common.ui.design_tokens`,
  `common.ui.glass.tokens`, `common.ui.ios.theme`, …).

## 6. Testing across backends

`src/app/wm_compare/` is the screenshot capture and compare harness for the WM
lanes, but its runtime CLI and source semantics have evolved beyond the old
single-example form. Use the dedicated guide for current commands, source labels,
and caveats:

- [tooling/wm_compare.md](tooling/wm_compare.md)

Every new widget or renderer that needs visual parity should still land with a
registered compare scene or an equivalent capture path.

UI-facing SSPEC tests should publish visible-state evidence into generated docs:
GUI captures under `doc/06_spec/image/<spec-relative-path>/`, and TUI text or
ANSI captures under `build/test-artifacts/<spec-relative-path>/`. Reference
those paths with `**Screenshots:**` or `**TUI Captures:**` metadata so
`spipe-docgen` embeds them in `doc/06_spec/...`.

## 7. Authoring checklist for a new backend

When a new renderer lands (e.g. a Fuchsia host, a terminal graphics
protocol, another webview), it needs:

1. `src/app/ui.<name>/backend.spl` — impl `Backend` trait.
2. `src/app/ui.<name>/__init__.spl` — module registration.
3. Input translation: map native events to `common.ui.event.UIEvent`.
4. Capability declaration: advertise at `start`.
5. A `wm_compare` scene registration that can run against this backend.
6. A row in the Platform Support Matrix
   ([arch doc](../04_architecture/cross_platform_wm.md#platform-support-matrix)).
7. A row in this guide's backend inventory (section 2 above).

If the new renderer is below the compositor (pure Simple on a novel
display), it's a `CompositorBackend` + `InputBackend` pair, not a
`ui.*` backend — see the arch doc.

## 8. What *not* to do

- **Don't** import `os.compositor.*`, `os.drivers.*`, or any `engine2d`
  module from app code. That ties an app to a specific drawing-layer
  variation and breaks wm_compare.
- **Don't** add a "cli mode" or "gui mode" flag that forks the widget
  tree. Use capabilities + profiles.
- **Don't** write to the terminal or framebuffer directly inside a
  widget. Emit patches; let the backend decide.
- **Don't** cache backend-specific state on `UISession`. Use
  `SurfaceManager` for per-surface state and `WidgetStore` for
  widget-local state.

## 9. Running an on-screen GUI window on macOS

The pure-Simple / hosted-winit GUI paths present pixels via
`rt_winit_window_present_rgba`. On macOS a GUI program launched as a bare CLI
process **will not show a window**: the process is never registered with the
window server (`lsappinfo` shows it unregistered) and the window is created but
never composites. Two things are required — both pure Simple / packaging, **no
Rust-seed change**:

1. **Poll the event loop continuously** in the app's frame loop — call
   `rt_winit_event_loop_poll_events(el, 1)` in a tight loop, never
   `rt_thread_sleep`. The interpreter owns the main thread, so a sleep leaves
   AppKit with no handler between frames and the window never composites.
   Present once, then re-present occasionally for static content. Examples:
   `examples/ui/web_engine2d_gui.spl`,
   `examples/simple_os/hosted/hosted_wm_software.spl`.

2. **Launch via a `.app` bundle** so LaunchServices registers the process in the
   Aqua session. Use the helper:

   ```bash
   scripts/macos-gui-run.shs examples/ui/web_engine2d_gui.spl
   ```

   It builds a throwaway `.app` around the gui driver (binary copied in — it is
   self-contained), supplies env via `Info.plist` `LSEnvironment`, `open`s it,
   and nudges the window on-screen (winit may place small windows off-screen).
   An `exec`-wrapper bundle does **not** work (exec to an out-of-bundle binary
   de-registers). Needs a gui-feature driver:
   `cd src/compiler_rust && CARGO_TARGET_DIR=target/gui cargo build -p simple-driver --features gui`.

Notes:
- Linux/Windows run a continuous `event_loop.run()` on a dedicated thread and do
  not need the `.app` bundle.
- The per-pixel software render (e.g. the host WM at 1024×768) is slow in the
  interpreter; verify at small resolution or use the compiled path.
- Full root cause + recipe:
  [`doc/09_bugs/macos_winit_window_not_displayed_2026-05-28.md`](../09_bugs/macos_winit_window_not_displayed_2026-05-28.md).

## 10. Pointers

- Session impl: `src/lib/common/ui/session.spl`
- Backend trait: `src/lib/common/ui/backend.spl`
- Backend selection + dispatch: `src/app/ui/detect.spl`
  (`detect_gui_backend`), `src/app/ui/main.spl`
- Event enum: `src/lib/common/ui/event.spl`
- Diff + patch: `src/lib/common/ui/diff.spl`, `patch.spl`
- Layout: `src/lib/common/ui/layout.spl`
- Capabilities: `src/lib/common/ui/capability.spl`,
  `capability_policy.spl`
- Profiles + viewport: `src/lib/common/ui/profile.spl`, `viewport.spl`
- Architecture: [`doc/04_architecture/cross_platform_wm.md`](../04_architecture/cross_platform_wm.md)
- GUI/WM restart plan: [`doc/03_plan/simple_gui_wm_restart_2026-05-28.md`](../03_plan/simple_gui_wm_restart_2026-05-28.md)
- Cross-backend parity harness: `src/app/wm_compare/`
- Semantic UI access surface: [tooling/ui_access.md](tooling/ui_access.md)
- macOS on-screen GUI launcher: `scripts/macos-gui-run.shs` (see §9)
