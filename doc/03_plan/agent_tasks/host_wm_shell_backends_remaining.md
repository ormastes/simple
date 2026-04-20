# Host WM Shell Backends — Completed Handoff

Status: completed
Last updated: 2026-04-20
Scope: SimpleWeb, ElectronWeb, shared host WM entrypoints, and host-native
surface backends that participate in the same `ui.web`/WM contract.

Related:
- `doc/04_architecture/ui_web_protocol.md`
- `doc/04_architecture/cross_platform_wm.md`
- `doc/04_architecture/shared_wm_stack.md`
- `doc/04_architecture/gui_layer_contract.md`
- `doc/04_architecture/ui_access_protocol.md`
- `doc/07_guide/ui_stack_guide.md`
- `doc/07_guide/tooling/wm_compare.md`
- `src/app/ui.web/host_adapter_contract.spl`
- `src/lib/common/ui/window_surface_registry.spl`
- `src/app/ui.web/taskbar_runtime.spl`
- `src/app/ui.web/wm_bridge.spl`
- `src/app/ui.web/wm.js`
- `tools/electron-shell/`
- `src/os/compositor/host_compositor_entry.spl`
- `src/os/compositor/hosted_backend*.spl`
- `src/runtime/hosted/`

## Completion Summary

Six parallel implementation agents closed the P0/P1 work and the remaining P2
catalog/layout gaps:

- Contract fixtures now pin exact `host_window_command` JSON and inbound native
  `window_cmd` feedback, including `HOST_NATIVE_EVENT_SOURCE`.
- `unmaximize_native_window` is implemented end-to-end across Simple runtime,
  WM bridge, JavaScript bridge, Electron preload/main, tests, and protocol docs.
- Native-host dispatch now uses `ui_surface_kind_is_native_host` and adapter
  capability state instead of duplicated Electron string checks.
- Electron shell boot uses the shared WebSocket WM client path, corrected
  package scripts, documented README, result-aware native suppression, and an
  opt-in advisory host smoke.
- Shared host WM entrypoints have selector/precedence tests across Electron,
  Tauri, TUI, browser, web server, and TUI-web entrypoints.
- Host compositor bootstrap uses title/config, event pumping, close/resize
  behavior, and documented Cocoa/Win32 winit-alias boundaries.
- Manifest-backed host content now comes from app content hooks with a clear
  unsupported page for manifests without hooks.
- Pinned app order and tray state can be saved and survive runtime reset; tests
  cover missing store, save/load, rejected corrupt saves, and corrupt-store
  fallback.
- Launch errors are surfaced in taskbar JSON and do not enqueue host commands.

Advisory limits:

- Electron live OS smoke is intentionally opt-in and skips unless
  `SIMPLE_ELECTRON_SMOKE=1` plus Electron/display access are available.
- Cocoa and Win32 Simple-side classes are documented winit-buffer aliases until
  true `rt_cocoa_*` / `rt_win32_*` runtime families are promoted.
- Runtime layout persistence is currently an in-process host store; durable
  disk-backed config can be layered under the same save/load API.

## Current Baseline

The host shell path has a shared Simple-owned protocol contract for outbound
host window commands and inbound native feedback:

- `HostWindowCommand` is serialized by `host_window_command_to_json`.
- `HOST_NATIVE_EVENT_SOURCE` is the canonical server-side marker for native
  feedback.
- `UI_SURFACE_KIND_LEGACY`, `UI_SURFACE_KIND_SIMPLE_WEB`,
  `UI_SURFACE_KIND_ELECTRON`, and `UI_SURFACE_KIND_HEADLESS` are canonical
  registry values.
- The host taskbar runtime supports `desktop_embedded`, `taskbar_only`, and
  `headless`.
- Electron native feedback updates Simple session/taskbar state without
  echoing new host commands.
- The browser/Electron client still uses JavaScript as the host API bridge
  because browser DOM, WebSocket, and Electron preload APIs are JavaScript
  APIs.

## Final Reality

The frontiers are now separated and covered by focused tests:

1. **Simple-side host shell contract** has fixture coverage for outbound host
   commands and inbound native feedback, including negative no-echo behavior.
2. **Electron renderer boot contract** is cohesive around the shared
   WebSocket/client bridge, with IPC/native BrowserWindow handling isolated in
   Electron preload/main code.
3. **Shared host compositor backends** now have a non-busy host bootstrap path
   and explicit alias documentation for Cocoa/Win32 until real platform
   backends are promoted.

## Completion Criteria

- Contract drift is guarded by checked fixtures or golden tests for both
  `host_window_command` and inbound native `window_cmd` feedback.
- SimpleWeb and ElectronWeb share one wire contract; no app logic moves into
  JavaScript.
- Native Electron feedback updates Simple state without echoing host commands.
- Non-native-feedback Electron commands still queue host commands normally.
- `unmaximize_native_window` is supported end-to-end and remains in the
  advertised contract.
- Adapter capabilities are represented in Simple state rather than spread
  across `surface_kind == Electron` and `electron_available` checks.
- Electron live OS smoke is opt-in, display-gated, and advisory unless Electron
  is promoted to a release target.
- Shared host WM entrypoint and compositor/backend docs match implementation.
- Focused WM test suite and JS syntax checks pass.

## Work Order

All items below are closed as of 2026-04-20. The detail is retained as the
traceability checklist for future regression work.

### P0 — Contract Closure

1. Add a checked fixture/golden for `host_window_command`.
   - Files:
     - `src/app/ui.web/host_adapter_contract.spl`
     - `test/app/ui.web/host_adapter_contract_test.spl`
     - `src/app/ui.web/wm.js`
   - Acceptance:
     - Exact field set is checked, including `action`, `window_id`,
       `surface_id`, `app_id`, `title`, `url`, `x`, `y`, `width`, and `height`.
     - String escaping is checked without relying only on loose substring tests.
     - A field rename or missing numeric field fails a focused test.

2. Add a checked fixture/golden for native feedback `window_cmd`.
   - Files:
     - `src/app/ui.web/host_adapter_contract.spl`
     - `src/app/ui.web/wm_bridge.spl`
     - `test/app/ui.web/wm_bridge_test.spl`
     - `test/app/ui.web/ui_routes_test.spl`
     - `src/app/ui.web/wm.js`
   - Acceptance:
     - Native feedback shape includes `source: "native_event"` and
       `window_id_hint`.
     - Focus, minimize, restore, maximize, move, resize, title, and close are
       represented.
     - The docs name `HOST_NATIVE_EVENT_SOURCE` as the owning constant.

3. Add the negative feedback test.
   - Files:
     - `test/app/ui.web/wm_bridge_test.spl`
     - `test/app/ui.web/ui_routes_test.spl`
   - Acceptance:
     - With an Electron surface and host taskbar runtime enabled, a frame with
       no `source` or a non-`HOST_NATIVE_EVENT_SOURCE` source queues one host
       command normally.
     - Existing native no-echo tests still assert zero queued frames.

4. Decide `unmaximize_native_window`.
   - Files:
     - `src/app/ui.web/taskbar_runtime.spl`
     - `src/app/ui.web/wm_bridge.spl`
     - `src/app/ui.web/wm.js`
     - `tools/electron-shell/preload.js`
     - `tools/electron-shell/main.js`
     - `doc/04_architecture/ui_web_protocol.md`
   - Acceptance:
     - Either Simple queues and syncs `unmaximize_native_window` with tests, or
       the action is removed from the advertised action list and JS bridge.
     - Native Electron `unmaximize` feedback has one documented mapping.

### P0 — Electron Boot Contract

1. Pick the Electron renderer mode.
   - Option A: Electron shell loads the WebSocket WM client and serves/copies
     the assets it needs, including `retained_renderer.js`.
   - Option B: Electron shell keeps stdin/stdout IPC and gains an explicit
     Electron adapter method equivalent to `wm.js` frame dispatch.
   - Acceptance:
     - Electron shell opens without console errors for missing
       `retained_renderer.js`, missing `handleMessage`, or failed `/ui/login`
       from a `file://` context.
     - Initial taskbar and shell chrome render.
     - The chosen mode is documented in `tools/electron-shell/README` or the
       nearest existing guide.

2. Fix shell packaging drift.
   - Files:
     - `tools/electron-shell/package.json`
     - `tools/electron-shell/launch.shs`
   - Acceptance:
     - `npm --prefix tools/electron-shell run start -- <entry>` works, or the
       script names are corrected and documented.

### P1 — Explicit Adapter Interface

1. Introduce a small `HostWebAdapter` design section.
   - Files:
     - `doc/04_architecture/ui_web_protocol.md`
     - `doc/04_architecture/shared_wm_stack.md`
     - `doc/05_design/host_wm_shell_backends.md` if detail design is needed
   - Interface responsibilities:
     - render snapshot/patch
     - forward input
     - execute host window command
     - send native feedback
     - report capabilities
   - Acceptance:
     - `SimpleWebAdapter` means embedded browser/web renderer surface.
     - `ElectronWebAdapter` means the same protocol plus native BrowserWindow
       execution.
     - Browser/Electron transport JS is documented as host bridge code, not app
       logic.

2. Represent adapter capabilities in Simple state.
   - Files:
     - `src/app/ui.web/taskbar_runtime.spl`
     - `src/lib/common/ui/window_surface_registry.spl`
     - `test/app/ui.web/taskbar_runtime_test.spl`
     - `test/unit/app/ui/window_surface_registry_spec.spl`
   - Capability fields:
     - `supports_native_windows`
     - `supports_embedded_surfaces`
     - `supports_headless_session`
     - `requires_js_host_bridge`
   - Acceptance:
     - `desktop_embedded`, `taskbar_only`, and `headless` behavior remains
       unchanged.
     - Native dispatch uses a capability/predicate such as
       `ui_surface_kind_is_native_host` rather than duplicating
       `surface_kind == UI_SURFACE_KIND_ELECTRON`.

### P1 — SimpleWeb Renderer Backend

1. Add SimpleWeb no-native smoke.
   - Files:
     - `test/app/ui.web/taskbar_runtime_test.spl`
     - `test/app/ui.web/host_taskbar_launch_test.spl`
   - Acceptance:
     - Launch `examples/hello_taskbar` and `/sys/apps/terminal` in
       `desktop_embedded`.
     - Verify a SimpleWeb surface opens.
     - Verify `host_taskbar_runtime_take_client_frames(...)` returns zero.

2. Document the JS-disabled fallback.
   - Files:
     - `doc/04_architecture/ui_web_protocol.md`
     - `doc/07_guide/ui_stack_guide.md`
   - Acceptance:
     - JavaScript-disabled environments are described as static snapshot
       rendering only unless a non-JS transport is implemented.
     - Live taskbar/window manipulation remains tied to browser/Electron host
       bridge capability.

### P1 — Electron Host OS Smoke

1. Add an opt-in real Electron host smoke.
   - Files:
     - `tools/electron-shell/`
     - a new gated smoke script under `scripts/` or `tools/electron-shell/`
   - Scenario:
     - launch taskbar shell
     - spawn `/sys/apps/terminal`
     - focus
     - minimize
     - restore
     - resize
     - set title
     - close
   - Acceptance:
     - Smoke proves real BrowserWindow events, not just Simple-only unit state.
     - Native feedback reaches Simple and leaves the pending host command queue
       empty after native-origin events.
     - Smoke skips clearly when Electron or display access is unavailable.
     - Smoke is not required in default CI unless Electron is promoted beyond
       advisory/dev-preview status.

2. Harden native feedback suppression.
   - Files:
     - `src/app/ui.web/wm.js`
     - `tools/electron-shell/main.js`
   - Acceptance:
     - Suppression is result-aware or expiring so a failed native command cannot
       swallow a later real OS event.
     - Move/resize/title event bursts update Simple state exactly once per final
       accepted event.

### P1 — Shared Host WM Entrypoints

1. Verify all shared-WM entrypoint flags.
   - Files:
     - `src/app/ui.electron/async_app.spl`
     - `src/app/ui.tauri/async_app.spl`
     - `src/app/ui.tui/async_app.spl`
     - `src/app/ui.browser/main.spl`
     - `src/app/ui.web/server.spl`
     - `src/app/ui.tui_web/app.spl`
     - `test/unit/app/ui/*`
   - Acceptance:
     - `--shared-wm` and env vars choose the expected `HostBackendKind`.
     - CLI/env precedence is tested.
     - Browser, Electron, WebCanvas, and Tui selector behavior is explicit even
       where the runtime currently falls back to winit selector `0`.

2. Fix or document the missing tracker handoff.
   - Files:
     - `doc/04_architecture/cross_platform_wm.md`
     - `doc/04_architecture/gui_layer_contract.md`
     - `doc/07_guide/ui_stack_guide.md`
   - Acceptance:
     - References to missing `doc/03_plan/gui_drawing_layer_variations.md` are
       either restored by adding the file or retargeted to this plan.

### P1 — Host Compositor Backend Alignment

1. Make `init_host_wm` a real bootstrap or document its current limit.
   - Files:
     - `src/os/compositor/host_compositor_entry.spl`
     - `test/unit/os/compositor/host_compositor_entry_spec.spl`
   - Acceptance:
     - `title` is used or explicitly removed from the contract.
     - A nonzero host surface/window path is created when supported.
     - `tick_forever()` does not busy-loop without event pumping or sleeping.
     - Close stops `WmService`; resize updates compositor dimensions.

2. Align Cocoa and Win32 backend names with implementation.
   - Files:
     - `src/os/compositor/hosted_backend_cocoa.spl`
     - `src/os/compositor/hosted_backend_win32.spl`
     - `src/runtime/hosted/`
     - `src/compiler_rust/native_all/Cargo.toml`
   - Acceptance:
     - Either platform-specific Simple classes call the matching
       `rt_cocoa_*` / `rt_win32_*` families, or they are renamed/documented as
       winit aliases.
     - Fill/blend/gradient/read-pixel tests are deterministic.
     - Feature-gated runtime artifacts fail cleanly or fall back intentionally
       when real backend features are absent.

3. Add platform smoke commands.
   - Platforms:
     - macOS Cocoa/AppKit, main-thread only
     - Windows Win32/GDI
     - Linux winit under X11, Wayland, or Xvfb
   - Acceptance:
     - Each platform has a one-command smoke or a documented skip reason.
     - Default stub runtime cannot be mistaken for a real host backend.

### P2 — App Content and Catalog

1. Replace generic manifest-backed native HTML with per-app host content hooks.
   - Files:
     - `src/app/ui.web/taskbar_runtime.spl`
     - `src/os/desktop/app_manifest.spl`
     - per-app manifest/content modules
   - Acceptance:
     - `/sys/apps/terminal` and other built-ins can provide app-specific host
       content without hardcoding route HTML.
     - Unknown app behavior still returns a clear unsupported page.

2. Persist pinned apps, order, and tray state.
   - Files:
     - `src/app/ui.web/taskbar_runtime.spl`
     - storage/config module selected by implementation design
   - Acceptance:
     - Runtime reset no longer rebuilds user pin/order state from defaults when
       persisted state exists.
     - Tests cover load, save, missing store, and corrupt store fallback.

3. Surface app launch errors in the taskbar model.
   - Files:
     - `src/lib/common/ui/taskbar_model.spl`
     - `src/app/ui.web/taskbar_shell.spl`
     - `src/app/ui.web/taskbar_runtime.spl`
   - Acceptance:
     - Failed launches are visible to the shell and testable from JSON model
       output.
     - Errors do not enqueue host commands.

## Agent Split

### Carver — Contract Fixtures

Owner:
- `HostWindowCommand` and native feedback schema/golden coverage.

Files:
- `src/app/ui.web/host_adapter_contract.spl`
- `test/app/ui.web/host_adapter_contract_test.spl`
- `test/app/ui.web/wm_bridge_test.spl`
- `test/app/ui.web/ui_routes_test.spl`

Acceptance:
- Exact host command and native feedback shapes are fixture-checked.
- Non-`HOST_NATIVE_EVENT_SOURCE` negative case queues a host command.

### Wegener — Runtime Capabilities

Owner:
- Adapter capability state and native-host surface predicates.

Files:
- `src/app/ui.web/taskbar_runtime.spl`
- `src/lib/common/ui/window_surface_registry.spl`
- `test/app/ui.web/taskbar_runtime_test.spl`
- `test/unit/app/ui/window_surface_registry_spec.spl`

Acceptance:
- Native dispatch is capability-driven, not Electron-string-driven.
- Existing `desktop_embedded`, `taskbar_only`, and `headless` tests remain
  green.

### Copernicus — Electron Renderer Contract

Owner:
- Electron shell boot mode, renderer asset contract, and JS bridge drift.

Files:
- `src/app/ui.web/wm.js`
- `tools/electron-shell/index.html`
- `tools/electron-shell/main.js`
- `tools/electron-shell/preload.js`
- `tools/electron-shell/package.json`

Acceptance:
- Electron shell boots without missing `retained_renderer.js`,
  `handleMessage`, or file-context `/ui/login` failures.
- `npm --prefix tools/electron-shell run start -- <entry>` is valid or clearly
  replaced.

### Mencius — Architecture And Tracker Handoff

Owner:
- Docs that define host WM contract and verification gates.

Files:
- `doc/04_architecture/ui_web_protocol.md`
- `doc/04_architecture/cross_platform_wm.md`
- `doc/04_architecture/shared_wm_stack.md`
- `doc/04_architecture/gui_layer_contract.md`
- `doc/07_guide/ui_stack_guide.md`

Acceptance:
- Protocol docs name Simple constants for native event and surface kind values.
- Missing `gui_drawing_layer_variations.md` handoff is resolved.
- Electron scope is marked advisory unless promotion gates close.

### Popper — Host Compositor Backends

Owner:
- `init_host_wm`, Cocoa/Win32 naming, runtime feature hardening, event loop
  behavior.

Files:
- `src/os/compositor/host_compositor_entry.spl`
- `src/os/compositor/hosted_backend*.spl`
- `src/runtime/hosted/`
- `src/compiler_rust/native_all/Cargo.toml`

Acceptance:
- Host WM bootstrap either creates real host surfaces or documents a clear
  stub/alias boundary.
- Feature-gated real backends cannot be confused with default stubs.

### Lovelace — Plan And Verification Gates

Owner:
- Work-order coherence, focused command list, and exit criteria.

Files:
- `doc/03_plan/agent_tasks/host_wm_shell_backends_remaining.md`
- focused test docs under `doc/03_plan/sys_test/` if added

Acceptance:
- Every P0/P1 task has files, acceptance criteria, and a verification command.
- Optional Electron/live OS gates have explicit skip conditions.

### Hopper — SimpleWeb Smoke

Owner:
- Embedded browser/web renderer launch behavior.

Files:
- `test/app/ui.web/taskbar_runtime_test.spl`
- `test/app/ui.web/host_taskbar_launch_test.spl`
- `doc/07_guide/ui_stack_guide.md`

Acceptance:
- `desktop_embedded` launches open SimpleWeb surfaces and emit zero native
  host commands.
- JS-disabled fallback is documented as static snapshot only.

### Turing — Electron Live Smoke

Owner:
- Real BrowserWindow smoke and native event ordering.

Files:
- `tools/electron-shell/`
- new gated smoke script under `scripts/` or `tools/electron-shell/`

Acceptance:
- A single opt-in command covers spawn, focus, minimize, restore, resize,
  title, and close.
- Smoke verifies native feedback does not echo.

### Noether — Shared Entrypoint Matrix

Owner:
- `--shared-wm` and env-var coverage for all host UI entrypoints.

Files:
- `src/app/ui.electron/async_app.spl`
- `src/app/ui.tauri/async_app.spl`
- `src/app/ui.tui/async_app.spl`
- `src/app/ui.browser/main.spl`
- `src/app/ui.web/server.spl`
- `src/app/ui.tui_web/app.spl`

Acceptance:
- Each entrypoint has a focused selector/precedence test or documented gap.

### Curie — App Catalog And Persistence

Owner:
- Per-app content hooks, persisted pin/order/tray state, launch error model.

Files:
- `src/app/ui.web/taskbar_runtime.spl`
- `src/lib/common/ui/taskbar_model.spl`
- `src/app/ui.web/taskbar_shell.spl`
- `src/os/desktop/app_manifest.spl`

Acceptance:
- Manifest-backed apps can provide real host content.
- Failed launches are visible in the taskbar model.

## Verification Gates

Focused Simple tests:

```sh
bin/simple test test/app/ui.web/host_adapter_contract_test.spl
bin/simple test test/app/ui.web/taskbar_runtime_test.spl
bin/simple test test/app/ui.web/wm_bridge_test.spl
bin/simple test test/app/ui.web/ui_routes_test.spl
bin/simple test test/app/ui.web/server_native_window_test.spl
bin/simple test test/app/ui.web/web_runtime_adapter_test.spl
bin/simple test test/app/ui.web/host_taskbar_launch_test.spl
bin/simple test test/app/ui.electron/spawn_via_manifest_test.spl
bin/simple test test/unit/app/ui/window_surface_registry_spec.spl
bin/simple test test/unit/app/ui/electron_app_spec.spl
```

JS/Electron syntax checks:

```sh
node --check src/app/ui.web/wm.js
cd tools/electron-shell && node --check main.js
cd tools/electron-shell && node --check preload.js
cd tools/electron-shell && node --check screenshot.js
cd tools/electron-shell && node --check export_snapshot.js
```

Optional live Electron smoke:

```sh
npm --prefix tools/electron-shell run smoke:host
# Skips unless SIMPLE_ELECTRON_SMOKE=1 and Electron/display access are present.
```

Additional shared-WM/backend checks when `src/os/compositor/**` or
`src/runtime/hosted/**` changes:

```sh
bin/simple test test/unit/os/compositor/host_compositor_entry_spec.spl
bin/simple test test/unit/os/compositor/hosted_backend_cocoa_spec.spl
bin/simple test test/unit/os/compositor/hosted_backend_win32_spec.spl
bin/simple test test/unit/os/compositor/compositor_spec.spl
```

Run full-suite and MCP smoke only after unrelated OS/kernel working-copy
changes are resolved or isolated.

## Verified On 2026-04-20

- `bin/simple test test/app/ui.web/host_adapter_contract_test.spl`
- `bin/simple test test/app/ui.web/taskbar_runtime_test.spl`
- `bin/simple test test/app/ui.web/wm_bridge_test.spl`
- `bin/simple test test/app/ui.web/ui_routes_test.spl`
- `bin/simple test test/app/ui.web/server_native_window_test.spl`
- `bin/simple test test/app/ui.web/web_runtime_adapter_test.spl`
- `bin/simple test test/app/ui.web/host_taskbar_launch_test.spl`
- `bin/simple test test/app/ui.web`
- `bin/simple test test/app/ui.electron/spawn_via_manifest_test.spl`
- `bin/simple test test/unit/app/ui/window_surface_registry_spec.spl`
- `bin/simple test test/unit/app/ui/electron_app_spec.spl`
- `bin/simple test test/unit/app/ui/shared_wm_entrypoints_spec.spl`
- `bin/simple test test/unit/os/compositor/host_compositor_entry_spec.spl`
- `bin/simple test test/unit/os/compositor/hosted_backend_cocoa_spec.spl`
- `bin/simple test test/unit/os/compositor/hosted_backend_win32_spec.spl`
- `bin/simple test test/unit/os/compositor/compositor_spec.spl`
- `node --check src/app/ui.web/wm.js`
- `node --check tools/electron-shell/main.js`
- `node --check tools/electron-shell/preload.js`
- `node --check tools/electron-shell/screenshot.js`
- `node --check tools/electron-shell/export_snapshot.js`
- `node --check tools/electron-shell/electron_host_smoke.js`
- `npm --prefix tools/electron-shell run smoke:host` skipped with the expected
  opt-in message because `SIMPLE_ELECTRON_SMOKE=1` was not set.

## Exit Criteria

- All P0 tasks are done and default-local focused tests are green.
- P1 tasks are implemented or explicitly documented as advisory promotion
  boundaries.
- P2 app catalog, layout persistence, and launch-error model coverage is in
  place.
- Electron live smoke has documented skip conditions and is advisory unless
  Electron becomes a release target.
- Shared host WM docs no longer overclaim beyond implementation.
- No new app logic moved into JavaScript; JS remains host bridge and renderer
  integration code only.

## Non-Goals For This Plan

- Replacing all browser-side JavaScript immediately. That is a separate
  transport design because current browsers expose WebSocket, DOM, and Electron
  preload APIs through JavaScript.
- Moving application logic into JavaScript. Application state remains
  Simple-owned through `UISession`.
- Forking SimpleWeb and ElectronWeb protocols. Both must continue using the
  same wire contract.
- Promoting Electron to a release target. This plan may add advisory Electron
  smoke coverage without making Electron mandatory in default CI.
