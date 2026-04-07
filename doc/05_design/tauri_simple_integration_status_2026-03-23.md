# Tauri 2 + Simple Integration Status

**Date:** 2026-03-23
**Status:** Desktop verified, Android APK verified, iOS pending (needs macOS)
**Previous:** [2026-03-22 status](tauri_simple_integration_status_2026-03-22.md)

## Summary

The Tauri 2 UI backend is now verified end-to-end on desktop (Linux) and Android (emulator). The architecture is a hybrid: Rust/Tauri shell owns the native window and webview, Simple owns UI logic and HTML generation, communicating via JSON IPC over stdin/stdout.

## Architecture

```text
Desktop:
  Tauri Shell (Rust) ─── stdin/stdout JSON IPC ──> Simple Binary
       │                                              │
       ├─ WebviewWindow("main")                       ├─ parse .ui.sdn
       ├─ loads app://index.html                      ├─ build UI state
       ├─ win.eval() injects HTML                     ├─ render to HTML
       ├─ JS event handlers → invoke()                ├─ print JSON to stdout
       └─ Tauri commands → subprocess stdin           └─ read JSON from stdin

Mobile (Android/iOS):
  Tauri Shell (Rust, cross-compiled)
       │
       ├─ Android WebView / WKWebView
       ├─ loads index.html
       ├─ window.__TAURI__ API available
       └─ Subprocess IPC not available (needs WebSocket transport)
```

## File Structure

```
tools/tauri-shell/
  src-tauri/
    src/
      app.rs          # Shared Tauri app logic (all platforms)
      main.rs         # Desktop entry point (calls app::run())
      lib.rs          # Mobile entry point (tauri::mobile_entry_point)
    Cargo.toml        # Dependencies (tauri 2, dialog, notification, serde)
    tauri.conf.json   # Tauri config (identifier: com.simple.ui)
    gen/
      android/        # Generated Android project (cargo tauri android init)
      schemas/        # ACL permission schemas
  dist/
    index.html        # Frontend page with Tauri event listeners
  index.html          # Dev copy of frontend
  package.json        # npm deps (@tauri-apps/api ^2)

tools/docker/
  Dockerfile.tauri-gui           # Desktop GUI test container (Xvfb + VNC)
  Dockerfile.tauri-android       # Android build container (SDK + NDK)
  Dockerfile.tauri-android-test  # Android emulator test container
  run-tauri-gui.shs              # Desktop container entry script
  run-android-test.shs           # Android emulator test script
```

## Platform Status

### Desktop (Linux) — Verified

**What works:**
- Tauri shell builds and runs with Xvfb + dbus-run-session
- Full render pipeline: Simple → JSON IPC → Tauri webview → HTML rendered
- Screenshot verified — styled HTML renders correctly in WebKitGTK webview
- Event forwarding (keyboard, click) via `__TAURI_INTERNALS__.invoke()`
- Entry file detection, binary compatibility check, subprocess lifecycle

**How to run:**
```bash
# Build
cd tools/tauri-shell/src-tauri && cargo build

# Run (with display)
DISPLAY=:99 WEBKIT_DISABLE_DMABUF_RENDERER=1 dbus-run-session -- \
  ./target/debug/simple-tauri-shell <simple-binary> <file.spl>

# Run in container
docker run --rm -p 5900:5900 simple-tauri-gui
```

**Key requirement:** dbus-run-session is required for WebKitGTK initialization.

### Android — APK Verified on Emulator

**What works:**
- Cross-compilation for all 4 Android targets (arm64, armv7, x86_64, i686)
- APK and AAB generated successfully
- APK installs and launches on Android emulator (API 34, Pixel 6)
- Tauri WebView initializes, `window.__TAURI__` API available
- Event listeners (listen, invoke) active
- `#[cfg(desktop)]` guards for window management APIs (title, minimize, maximize, close)

**What doesn't work yet:**
- No content rendering (subprocess IPC not available on mobile — needs WebSocket transport)
- App shows "Listening for render events from subprocess..." (expected)

**How to build:**
```bash
# In Docker container with Android SDK
docker run --rm simple-tauri-android \
  sh -c "cd /app/tools/tauri-shell && cargo tauri android build --debug"

# APK output: src-tauri/gen/android/app/build/outputs/apk/universal/debug/app-universal-debug.apk
```

**How to test on emulator:**
```bash
docker run --rm --privileged --device /dev/kvm \
  -v $(pwd)/build/android-test:/output \
  simple-tauri-android-test
# Screenshot saved to build/android-test/android_screenshot.png
```

### iOS — Pending (requires macOS)

**Expected to work** (same architecture as Android):
- `cargo tauri ios init` generates Xcode project
- `cargo tauri ios build --debug` produces .app
- Same `#[cfg(desktop)]` guards handle API differences

**How to set up (on macOS):**
```bash
cd tools/tauri-shell
cargo tauri ios init
cargo tauri ios dev  # or open src-tauri/gen/apple/ in Xcode
```

## Mobile-Specific Notes

### cfg Guards

Desktop-only Tauri APIs are gated with `#[cfg(desktop)]`:
- `WebviewWindowBuilder.title()` / `.inner_size()` — not available on mobile
- `window.minimize()` / `.maximize()` / `.close()` — not available on mobile
- `WindowControl` IPC handler — desktop only

### Mobile IPC Gap

On mobile, subprocess spawning (stdin/stdout IPC) doesn't work. To render actual UI content on mobile, a WebSocket-based IPC transport is needed:
- Simple runs a local WebSocket server on `localhost:<port>`
- Tauri webview connects via `ws://localhost:<port>`
- Same JSON protocol as stdin/stdout

The transport abstraction was designed in `src/app/ui.ipc/transport.spl` (IpcTransport trait, StdioTransport, WebSocketTransport) but not yet integrated into the Tauri shell's Rust side.

## Previous Blockers — Resolved

| Blocker | Status | Resolution |
|---------|--------|------------|
| Circular import in `app.ui` | Fixed | Runner functions not re-exported from `__init__.spl` |
| Parser errors in `app.spl` | Fixed | Valid Simple syntax throughout |
| Wrong detection binary name | Fixed | `detect.spl` checks for `simple-tauri-shell` |
| No mobile build support | Fixed | `app.rs` + `lib.rs` split with `#[cfg(desktop)]` guards |
| Render status overwrite | Fixed | `got_render` flag prevents "stdout closed" from overwriting rendered content |
| `.spl` subprocess invocation | Fixed | Passes file directly without `run` prefix |

## Docker Images

| Image | Size | Purpose |
|-------|------|---------|
| `simple-tauri-gui` | ~9 GB | Desktop GUI testing (Xvfb + VNC + Tauri) |
| `simple-tauri-android` | ~15 GB | Android build (SDK + NDK + Rust cross-compile) |
| `simple-tauri-android-test` | ~16 GB | Android emulator testing (SDK + emulator + system image) |
