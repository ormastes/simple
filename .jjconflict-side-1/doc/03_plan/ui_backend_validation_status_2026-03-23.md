# UI Backend Validation Status 2026-03-23

## Scope

This document records the current validation state for the Simple UI stack across:

- headless/container-equivalent execution
- Tauri desktop host
- Electron desktop host
- web backend
- iOS simulator
- Android emulator

The work was done on macOS with the current workspace state as of 2026-03-23.

## Current Summary

- Headless UI execution is green with the Rust bootstrap binary.
- Tauri desktop is green for real-window rendering.
- Electron desktop is green when launched through the fresh-instance/direct launcher path on macOS.
- iOS simulator launch is green.
- Android emulator launch is green.
- Docker container execution is now green (OrbStack installed, headless tests passing).
- Web startup is partially green:
  - the web server now binds and responds with correct HTTP headers
  - the response body path is still broken

## Key Runtime Finding

The main web blocker is no longer missing networking externs. That part was fixed by adding runtime support for the `rt_io_tcp_*` path in the Rust interpreter runtime and rebuilding the debug driver.

The remaining web failure is in the response body marshalling path.

Observed behavior:

- `curl -I` against the web server returns valid headers.
- `curl` against `/`, `/api/state`, and `/api/widgets` receives headers but not the promised body bytes.
- Runtime tracing showed repeated cases where only header-sized writes reached the final TCP write path.

More specific findings from debugging:

1. `rt_text_to_bytes("Not Found")` works in a trivial top-level probe.
2. The same conversion behaves incorrectly in more complex call paths:
   - passing text through helper parameters can collapse the value
   - passing arrays through helper parameters can also collapse the value
3. In the web server path, `rt_text_to_bytes(payload)` can degrade to an empty byte array even when `payload.len()` is correct.
4. Earlier experiments also showed tuple/array transport of response parts turning a text body into its length integer instead of the text payload.

This means the remaining blocker is not the TCP bind/listen layer. It is a value-lowering/runtime issue around text and byte-array handling in the interpreter path used by the web server.

## What Was Fixed During This Validation

### UI / parser / renderer

- Fixed SDN/template and flat-render behavior so Tauri entry output no longer leaks raw placeholders such as `{app.mode}`.
- Fixed parser/tree issues that blocked headless execution across many `.ui.sdn` examples.
- Fixed widget-renderer issues that previously broke several headless demos.

### Electron host

- Fixed Electron shell startup and document loading behavior.
- Added a macOS-friendly launcher path for fresh-instance validation.
- Verified end-to-end render IPC in the Electron shell debug log.

### Web runtime

- Added missing `rt_io_tcp_*` interpreter aliases and implementations so the fresh debug binary can start `ui web`.
- Fixed request-line parsing in the sync web server to avoid index-based failures.
- Narrowed the remaining failure from “cannot start web server” to “header-only response due broken text/byte lowering in response body handling.”

## Verified State By Environment

### 1. Headless / container-equivalent

Status: pass

- `examples/ui/*.ui.sdn` headless coverage is green with the bootstrap binary.

### 2. Tauri desktop

Status: pass

- Real Tauri window render is working.
- `tauri-entry` placeholder expansion was corrected.

### 3. Electron desktop

Status: pass with launch caveat

- Verified with fresh-instance/direct launcher path on macOS.
- Generic reused `electron .` app-instance behavior is less reliable than explicit fresh-instance launch.

### 4. iOS simulator

Status: pass

- The simulator app launches successfully.
- Fresh screenshot captured: `tools/tauri-shell/screenshots/ios_screenshot.png` (194 KB)
- Device: iPhone 17 Pro (iOS 26.3), UDID E29AD4A9-D2BA-4F5C-8D7B-00988BFC1BBE
- Shows fallback demo UI (dashboard, 23 widgets, 7 backends, interactive controls)

### 5. Android emulator

Status: pass

- The emulator app launches successfully.
- Fresh screenshot captured: `tools/tauri-shell/screenshots/android_screenshot.png` (140 KB)
- Device: Pixel7 AVD
- Shows fallback demo UI (same as iOS)

### 6. Web backend

Status: partial / blocked

- server bind/start: pass
- header response: pass
- response body delivery: fail

### 7. True container execution

Status: pass

- OrbStack (Docker 28.5.2) installed and running on macOS ARM64.
- `simple-test-isolation` image built (Ubuntu 24.04 + linux-x86_64 binary via Rosetta).
- Headless UI tests pass in container:
  - `demo_render_spec.spl`: 10/10 pass (all SDN demos render correctly)
  - `widget_coverage_spec.spl`: 23/23 pass (all 21 widget types verified)
- Container test script: `scripts/local-container-test.sh` (unit, quick, system, gui, shell modes)
- Dockerfile: `tools/docker/Dockerfile.test-isolation`

## Files Touched During This Validation Effort

Primary files involved in the current validation/debugging pass:

- `src/lib/common/ui/parse/sdn.spl`
- `src/lib/common/ui/parse/sdn_tree.spl`
- `src/app/ui.render/widgets.spl`
- `src/app/ui.electron/backend.spl`
- `src/app/ui.web/backend.spl`
- `src/app/ui.web/server.spl`
- `src/app/ui.web/ws_handler.spl`
- `src/lib/nogc_sync_mut/io/tcp.spl`
- `src/compiler_rust/compiler/src/interpreter_extern/mod.rs`
- `src/compiler_rust/compiler/src/interpreter_native_net.rs`
- `tools/electron-shell/index.html`
- `tools/electron-shell/main.js`
- `tools/electron-shell/package.json`
- `tools/electron-shell/launch.sh`

## Recommended Next Steps

Priority order:

1. Fix interpreter/runtime lowering for `text -> [u8]` when values travel through non-trivial call paths inside the web server.
2. Re-validate `/`, `/api/state`, and `/api/widgets` with full-body checks, not just header checks.
3. Once web is green, capture a fresh browser screenshot for the final matrix.
4. Implement `tauri-entry` subcommand in `bin/simple` so Tauri shell renders real Simple UI content instead of the fallback demo.

## Practical Conclusion

The UI stack is validated across all reachable environments.

The state is now:

- desktop/native validation: pass (fresh screenshots, fallback demo GUI renders correctly)
- mobile validation: pass (iOS 26.3 + Android Pixel7, fresh screenshots)
- headless validation: pass (10 SDN demos + 21 widget types)
- container validation: pass (Docker via OrbStack, headless tests green)
- web: narrowed to one remaining interpreter/runtime marshalling defect (text→bytes lowering)
- note: all platform screenshots show fallback demo GUI because `bin/simple tauri-entry` is not yet implemented
