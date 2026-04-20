# Host WM Shell Backends — Remaining Work

Status: active
Last updated: 2026-04-20
Related:
- `doc/04_architecture/ui_web_protocol.md`
- `doc/04_architecture/cross_platform_wm.md`
- `src/app/ui.web/host_adapter_contract.spl`
- `src/lib/common/ui/window_surface_registry.spl`
- `src/app/ui.web/taskbar_runtime.spl`
- `src/app/ui.web/wm.js`
- `tools/electron-shell/`

## Current Baseline

The host shell path now has a shared Simple-owned protocol contract for outbound host window commands and inbound native feedback:

- `HostWindowCommand` is serialized by `host_window_command_to_json`.
- `HOST_NATIVE_EVENT_SOURCE` is the canonical server-side marker for native feedback.
- `UI_SURFACE_KIND_LEGACY`, `UI_SURFACE_KIND_SIMPLE_WEB`, `UI_SURFACE_KIND_ELECTRON`, and `UI_SURFACE_KIND_HEADLESS` are canonical registry values.
- The host taskbar runtime supports `desktop_embedded`, `taskbar_only`, and `headless`.
- Electron native feedback updates Simple session/taskbar state without echoing new host commands.
- The browser/Electron client still uses JavaScript as the host API bridge because browser DOM, WebSocket, and Electron preload APIs are JavaScript APIs.

## Remaining Work

### P0 — Contract Hardening

- Add a generated or checked JSON-schema-style fixture for `host_window_command` and native `window_cmd` feedback so Simple and JS cannot drift silently.
- Add a negative test that non-`HOST_NATIVE_EVENT_SOURCE` feedback from an Electron surface queues host commands normally.
- Add server-side handling for `unmaximize_native_window` or remove the advertised action until supported end-to-end.
- Update `doc/04_architecture/ui_web_protocol.md` examples to name the Simple constants that own `native_event` and `surface_kind` values.

### P1 — Explicit Adapter Interface

- Introduce a small `HostWebAdapter` design section covering the common interface used by SimpleWeb and ElectronWeb:
  `render snapshot/patch`, `forward input`, `execute host window command`, `send native feedback`, and `report capabilities`.
- Represent adapter capabilities in Simple state, not scattered conditionals:
  `supports_native_windows`, `supports_embedded_surfaces`, `supports_headless_session`, and `requires_js_host_bridge`.
- Rename or document the runtime paths clearly:
  `SimpleWebAdapter` means embedded browser/web renderer surface.
  `ElectronWebAdapter` means the same protocol plus native BrowserWindow execution.

### P1 — SimpleWeb Renderer Backend

- Keep SimpleWeb UI state and rendering decisions in Simple; do not require app-authored JavaScript.
- Decide whether the browser transport remains JS-only or gains a no-custom-JS mode:
  static HTML form posts plus polling/SSE is possible but loses low-latency input and native host APIs.
- Add a SimpleWeb-only smoke that launches a manifest-backed app in `desktop_embedded` and verifies no host-native command is emitted.
- Add a documented fallback for environments that disable JavaScript: static snapshot rendering only, no live taskbar/window manipulation unless a non-JS transport is implemented.

### P1 — Electron Host OS Smoke

- Add an opt-in macOS/Linux smoke for `tools/electron-shell/`:
  launch taskbar shell, spawn `/sys/apps/terminal`, focus, minimize, restore, resize, set title, close.
- Verify native feedback does not echo commands by asserting the pending host command queue stays empty after native events.
- Keep this smoke out of default CI unless Electron and display access are explicitly available.

### P2 — App Content and Catalog

- Replace generic manifest-backed native HTML with per-app host content hooks.
- Persist pinned apps, order, and tray state instead of rebuilding from defaults each runtime reset.
- Add app launch errors to the taskbar model so failed host launches are visible to the shell.

### P2 — Documentation and Verification

- Add a short dev guide explaining when JS is required:
  browser/Electron host bridge requires JS; Simple application logic and server-side renderer state do not.
- Run the focused WM suite after each change:
  `bin/simple test test/app/ui.web/host_adapter_contract_test.spl`
  `bin/simple test test/app/ui.web/taskbar_runtime_test.spl`
  `bin/simple test test/app/ui.web/wm_bridge_test.spl`
  `bin/simple test test/app/ui.web/host_taskbar_launch_test.spl`
  `bin/simple test test/app/ui.electron/spawn_via_manifest_test.spl`
  `bin/simple test test/unit/app/ui/window_surface_registry_spec.spl`
  `node --check src/app/ui.web/wm.js`
- Run full-suite and MCP smoke only after unrelated OS/kernel working-copy changes are resolved or isolated.

## Non-Goals For This Plan

- Replacing all browser-side JavaScript immediately. That is a separate transport design because current browsers expose WebSocket, DOM, and Electron preload APIs through JavaScript.
- Moving application logic into JavaScript. Application state remains Simple-owned through `UISession`.
- Forking SimpleWeb and ElectronWeb protocols. Both must continue using the same wire contract.
