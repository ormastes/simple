# Host WM Shell Backends — Detail Design

<!-- codex-architecture -->

Status: design slice (2026-04-20)
Owners: `src/app/ui.web/`, `src/lib/common/ui/window_surface_registry.spl`,
`src/os/compositor/host_compositor_entry.spl`
Related: `doc/04_architecture/ui_web_protocol.md`,
`doc/04_architecture/shared_wm_stack.md`,
`doc/03_plan/agent_tasks/host_wm_shell_backends_remaining.md`

## HostWebAdapter

`HostWebAdapter` is the adapter boundary between the Simple-owned
`ui.web` protocol and a host shell. It is a role, not yet a single Simple
interface type. The role is implemented today by `src/app/ui.web/wm.js`,
`tools/electron-shell/preload.js`, and the Simple runtime modules that emit
or consume protocol frames.

Responsibilities:

1. Render `snapshot` and `patch_batch` frames.
2. Forward host input to Simple.
3. Execute `host_window_command` frames when native windows are supported.
4. Send native feedback back to Simple.
5. Report capabilities during the protocol handshake.

`SimpleWebAdapter` means embedded web rendering with
`UI_SURFACE_KIND_SIMPLE_WEB`. It can render and forward input, but it does not
spawn native BrowserWindows. `ElectronWebAdapter` means the same protocol plus
native BrowserWindow command execution and feedback with
`UI_SURFACE_KIND_ELECTRON`.

## Constant Ownership

`HOST_NATIVE_EVENT_SOURCE` is owned by
`src/app/ui.web/host_adapter_contract.spl`. It marks host-origin feedback and
prevents Simple from echoing native events back into new host commands.

`UI_SURFACE_KIND_LEGACY`, `UI_SURFACE_KIND_SIMPLE_WEB`,
`UI_SURFACE_KIND_ELECTRON`, and `UI_SURFACE_KIND_HEADLESS` are owned by
`src/lib/common/ui/window_surface_registry.spl`. These constants classify
window-surface bindings and are the current dispatch key for host taskbar
runtime behavior.

Current limit: native dispatch still checks
`binding.surface_kind == UI_SURFACE_KIND_ELECTRON` in several places. The
next design step is to move that to Simple-owned adapter capabilities such as
`supports_native_windows`, `supports_embedded_surfaces`,
`supports_headless_session`, and `requires_js_host_bridge`.

## Modes

`desktop_embedded` opens a SimpleWeb surface and does not queue native-window
commands. `taskbar_only` records authoritative Simple session/taskbar state
and queues Electron native-window commands. `headless` records session/taskbar
state only and creates no local or native surface.

## JavaScript Boundary

Browser and Electron JavaScript is host bridge and renderer code only. App
logic, taskbar state, window-surface state, and native-feedback suppression
rules remain Simple-owned. JavaScript-disabled environments are static
snapshot/export targets only until a non-JavaScript transport is implemented.

## Theme CSS Ownership

Host macOS Electron WM uses the folder theme package as host chrome input, not
the SimpleWeb app renderer as an indirect source of truth. The Electron preload
loads the registry default from `config/themes/theme.sdn`, composes family
shape CSS, family widget CSS, theme base CSS, and theme widget overrides once
at shell boot, and exposes the result as host theme CSS to `index.html`.

`tools/electron-shell/index.html` owns only structural rules for Electron host
surfaces: `body`, `#wm-chrome`, `#wm-desktop`, `#wm-taskbar`, `.wm-window`,
`.wm-titlebar`, `.wm-body`, and taskbar item layout. Visual values in those
rules must come from theme custom properties such as `--app-background-image`,
`--app-surface`, `--app-border`, `--ui-fg`, `--ui-accent-dim`, radius,
spacing, blur, elevation, and font tokens.

`SimpleWebAdapter` still consumes the same package CSS through the Simple
renderer path for embedded browser surfaces. It must not become the authority
for host-native Electron window chrome. This keeps the host Mac WM route
usable when Electron is launched from `file://` with stdin/stdout IPC and no
`/ui/login` WebSocket renderer.

## Current Limits

Electron is advisory/dev-preview. Unit-level Simple state tests cover launch,
surface kind propagation, and native feedback handling, but a real
display-gated Electron OS smoke is not part of default CI.

`init_host_wm` uses the backend selector and initial size, but does not yet use
`HostWmConfig.title` to create a real host title. `tick_forever()` is a tight
present loop and needs event sleeping or host event pumping before it should be
used as a production host shell loop.
