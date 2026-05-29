# Tauri 2 Backend — Headless Container Testing Guide

How to build and test the Tauri UI backend in headless containers without a physical display.

## Prerequisites

- Docker with `--privileged` support
- KVM access (`/dev/kvm`) for Android emulator

## Quick Start

### Desktop Test

```bash
# Build container (first time only, ~10 min)
docker build -f tools/docker/Dockerfile.tauri-gui -t simple-tauri-gui .

# Run — opens VNC on port 5900
docker run --rm -p 5900:5900 simple-tauri-gui

# Connect VNC viewer to localhost:5900 to see the window
```

### Android Test

```bash
# Build container (first time only, ~20 min)
docker build -f tools/docker/Dockerfile.tauri-android -t simple-tauri-android .
docker build -f tools/docker/Dockerfile.tauri-android-test -t simple-tauri-android-test .

# Run emulator test — screenshot saved to build/android-test/
mkdir -p build/android-test
docker run --rm --privileged --device /dev/kvm \
  -v $(pwd)/build/android-test:/output \
  simple-tauri-android-test

# View screenshot
open build/android-test/android_screenshot.png
```

## Desktop Testing in Detail

### Without Container (local Xvfb)

Requires: `xvfb`, `dbus-x11`, Tauri build deps (`libwebkit2gtk-4.1-dev`, `libsoup-3.0-dev`, `libjavascriptcoregtk-4.1-dev`)

```bash
# Build bundled desktop shell
cd tools/tauri-shell
mkdir -p dist && cp index.html dist/index.html
cargo build --manifest-path src-tauri/Cargo.toml

# Start virtual display
Xvfb :99 -screen 0 1280x720x24 &

# Run standalone shell (dbus-run-session is required for WebKitGTK)
DISPLAY=:99 WEBKIT_DISABLE_DMABUF_RENDERER=1 \
  dbus-run-session -- \
  ./src-tauri/target/debug/simple-tauri-shell <simple-binary> <entry-file>

# Convenience helper (defaults to ../../bin/simple + hello_tauri.ui.sdn)
DISPLAY=:99 WEBKIT_DISABLE_DMABUF_RENDERER=1 \
  dbus-run-session -- \
  ./run-desktop.command

# Take screenshot
DISPLAY=:99 xwd -root -out /tmp/screenshot.xwd
convert /tmp/screenshot.xwd /tmp/screenshot.png
```

### Entry Files and Limits

The Tauri shell accepts two types of entry files:

| Type | Invocation | Requires |
|------|-----------|----------|
| `.spl` | `simple <file>` | Any Simple binary |
| `.ui.sdn` | `simple tauri-entry <file>` | Simple binary with `ui` command |

Current limitation:
- `simple-tauri-shell` is standalone single-window mode only.
- `--shared-wm` and `SIMPLE_UI_TAURI_SHARED_WM=1` are rejected explicitly because the Tauri shell does not yet wire the shared host WM event loop through its native window bootstrap.

For testing with older Simple binaries, use `.spl` files that output render JSON:

```simple
# examples/ui/test_render.spl
fn main():
    val html = "<div><h1>Hello</h1></div>"
    val escaped = html.replace("\"", "\\\"")
    print "{\"type\":\"render\",\"html\":\"{escaped}\"}"
```

### Environment Variables

| Variable | Purpose | Example |
|----------|---------|---------|
| `DISPLAY` | X11 display for Xvfb | `:99` |
| `WEBKIT_DISABLE_DMABUF_RENDERER` | Bypass GPU/DRI permission issues | `1` |
| `SIMPLE_BIN` | Override Simple binary path | `./bin/simple` |
| `SIMPLE_ENTRY` | Override entry file path | `examples/ui/hello.spl` |

### Verifying the Render Pipeline

Check stderr logs for these key lines:

```
[tauri-shell] creating window from app://index.html   # Window created
[tauri-shell] window created                           # WebView initialized
[tauri-shell] subprocess pid=XXXXX                     # Simple process spawned
[tauri-shell] raw stdout: {"type":"render",...}         # Render JSON received
[tauri-shell] render, html_len=NNN                     # HTML parsed
[tauri-shell] eval OK                                  # HTML injected into webview
```

If `creating window` never appears, `dbus-run-session` is likely missing.

## Android Testing in Detail

### Build APK Only (no emulator)

```bash
# Mount local source changes into the build container
docker run --rm \
  -v $(pwd)/tools/tauri-shell/src-tauri/src:/app/tools/tauri-shell/src-tauri/src:ro \
  -v $(pwd)/tools/tauri-shell/src-tauri/Cargo.toml:/app/tools/tauri-shell/src-tauri/Cargo.toml:ro \
  -v $(pwd)/build:/output \
  simple-tauri-android \
  sh -c 'cd /app/tools/tauri-shell && cargo tauri android build --debug && \
    cp src-tauri/gen/android/app/build/outputs/apk/universal/debug/app-universal-debug.apk /output/simple-ui.apk'

# APK at build/simple-ui.apk
```

### Run on Emulator with Screenshot

```bash
docker run --rm --privileged --device /dev/kvm \
  -v $(pwd)/tools/tauri-shell/src-tauri/src:/app/tools/tauri-shell/src-tauri/src:ro \
  -v $(pwd)/tools/tauri-shell/src-tauri/Cargo.toml:/app/tools/tauri-shell/src-tauri/Cargo.toml:ro \
  -v $(pwd)/build/android-test:/output \
  simple-tauri-android-test
```

The test script:
1. Starts Xvfb (virtual display for emulator rendering)
2. Builds the APK
3. Boots Android emulator (Pixel 6, API 34, x86_64)
4. Installs APK via adb
5. Launches `com.simple.ui/.MainActivity`
6. Waits 5 seconds for render
7. Takes screenshot via `adb exec-out screencap`
8. Saves to `/output/android_screenshot.png`

### Verifying Android WebView

The screenshot should show the debug panel with:

```
Page loaded
window.__TAURI__: object
Tauri API found. Keys: app, core, dpi, event, ...
Found event.listen
Found core.invoke
Listening for 'render' events from subprocess...
Event forwarding active
```

This confirms the Tauri WebView and JS bridge are working on Android.

### Install APK on Physical Device

```bash
adb install build/simple-ui.apk
adb shell am start -n com.simple.ui/.MainActivity
```

## Mobile-Specific Code

Desktop-only APIs are gated in `src/app.rs`:

```rust
// Window title and size — desktop only
#[cfg(desktop)]
{ builder = builder.title("Simple UI").inner_size(1280.0, 720.0); }

// Window control (minimize/maximize/close) — desktop only
#[cfg(desktop)]
if let Some(win) = app.get_webview_window("main") { ... }

// Window close on exit — desktop only
#[cfg(desktop)]
{ let _ = _window.close(); }
```

## Troubleshooting

| Problem | Cause | Fix |
|---------|-------|-----|
| GTK init failed | No display or dbus | Use `dbus-run-session` with `DISPLAY` set |
| `creating window` never appears | WebKitGTK can't init | Set `WEBKIT_DISABLE_DMABUF_RENDERER=1` |
| `incompatible Simple binary` | Binary lacks `ui` command | Use `.spl` entry file instead of `.ui.sdn` |
| Render shows then gets overwritten | `stdout closed` status | Fixed — `got_render` flag prevents overwrite |
| Android `no library targets` | Missing `lib.rs` | Ensure `app.rs` + `main.rs` + `lib.rs` split |
| Android `close()` not found | Desktop-only API | Add `#[cfg(desktop)]` guard |
| Emulator won't start | No KVM | Run with `--privileged --device /dev/kvm` |
