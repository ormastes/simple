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
[`doc/04_architecture/cross_platform_wm.md`](../04_architecture/cross_platform_wm.md)
and [`doc/03_plan/gui_drawing_layer_variations.md`](../03_plan/gui_drawing_layer_variations.md).

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
| `ui.electron` | Electron BrowserWindow | V4 drawing stack | experimental |
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

`backend_factory.spl` chooses a backend at runtime based on
`SIMPLE_UI_BACKEND` / CLI flags. Apps should not name a backend
directly; they should accept whatever the factory returns.

## 4. CLI / TUI / GUI — what actually differs

| Aspect | CLI (`ui.cli`) | TUI (`ui.tui`) | GUI (compositor or browser) |
|--------|----------------|----------------|-----------------------------|
| Output unit | lines | cells | pixels |
| Layout engine | `common.ui.layout` (text flow) | `common.ui.layout_engine` (grid cells) | `common.ui.layout_engine` (flex/px) |
| Patch renderer | `ui.render` text snapshot / stdio | `screen.spl` cell buffer | `os.compositor` or `browser_backend` |
| Input source | line reader / socket | termios raw | PS/2, winit, DOM, IPC |
| Event pump | blocking read loop | `async_input.spl` | compositor loop or event-loop callback |
| Capabilities | `TEXT_ONLY` | `TEXT_ONLY \| COLOR` | `GRAPHICS \| POINTER \| HIDPI \| …` |

The widget tree, `UIEvent`, lifecycle hooks, state updates, and change
logs are **identical**. The only axis of variation is the projection of
`Patch[]` to an output and the translation of input to `UIEvent`.

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
  `common.ui.glass_tokens`, `ios_theme`, …).

## 6. Testing across backends

`src/app/wm_compare/` is the parity harness. It takes a scene from
`scene_registry.spl` and renders it through N backends, producing
screenshots / text snapshots it can diff:

```
wm_compare scene=calculator backends=cli,tui,render,browser,fb
```

Every new widget should land with a `wm_compare` scene if it has
meaningful rendering. The golden-image gate in
`doc/06_spec/app/compiler/feature/windows_spec.md` enforces that all
four drawing-layer variations produce visually identical output (≤1%
perceptual diff).

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

## 9. Pointers

- Session impl: `src/lib/common/ui/session.spl`
- Backend trait + factory: `src/lib/common/ui/backend.spl`,
  `backend_factory.spl`
- Event enum: `src/lib/common/ui/event.spl`
- Diff + patch: `src/lib/common/ui/diff.spl`, `patch.spl`
- Layout: `src/lib/common/ui/layout.spl`, `layout_engine.spl`
- Capabilities: `src/lib/common/ui/capability.spl`,
  `capability_policy.spl`
- Profiles + viewport: `src/lib/common/ui/profile.spl`, `viewport.spl`
- Architecture: [`doc/04_architecture/cross_platform_wm.md`](../04_architecture/cross_platform_wm.md)
- Work plan: [`doc/03_plan/gui_drawing_layer_variations.md`](../03_plan/gui_drawing_layer_variations.md)
- Cross-backend parity harness: `src/app/wm_compare/`
