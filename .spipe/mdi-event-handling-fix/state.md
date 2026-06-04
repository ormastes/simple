# MDI Event Handling Fix State

Date: 2026-06-04

## Scope

Investigate and fix wrong or dummy MDI behavior across Electron, Tauri, and pure Simple-backed WM paths, with special attention to event routing and taskbar/icon rendering evidence.

## Implemented

- Electron renderer forwards common web input envelopes instead of dummy event IPC.
- Electron MDI windows route body click, input, key, pointer, and mouse events; the real MDI proof checks body click/input routing.
- Electron live-smoke package entry points at `examples/06_io/ui/hello_electron.ui.sdn`.
- Tauri MDI proof now requires the full event runtime surface: `bindWindowEvents`, action, key, input, and mouse senders.
- Tauri mobile/iOS runtime selection includes iOS bundled runtime hooks and explicit no-runtime live-MDI bridge error messaging.
- Tauri mobile startup errors render through a mobile-safe inline shell page instead of falling back to `tauri.localhost` asset failure or Android `data:` URL crashes.
- Tauri Android can package a target-compatible Simple runtime as an extracted native library and bundle a self-contained Simple MDI smoke source for live subprocess rendering.
- Android live MDI replays early subprocess window messages after the WebView shell is ready and logs mobile MDI proof without closing the app.
- Rust compiler/runtime Android portability holes fixed for PTY ioctl/errno, interpreter PTY, torch runtime library naming, and native-project Android symbol stubs.
- Pure Simple WM lifecycle keeps focus/z-order coherent across minimize, restore, maximize, destroy, and drag release.
- Hosted pure-WM capture no longer calls the crashing timing extern, writes PPM rows in chunks, and relies on wrapper-side semantic pixel validation.
- Evidence wrappers under `scripts/check` resolve repo root correctly from `scripts/check`; hosted wrapper no longer uses Bash-only `SECONDS`.

## Current Passing Evidence

- `npm --prefix tools/electron-shell run smoke`: pass.
- Electron real MDI proof via `examples/06_io/ui/electron_wm.spl`: pass; 4 windows, desktop present, image rendered, drag moved, full event runtime present, body click/input routed, HTML rendered.
- `cd tools/tauri-shell/src-tauri && cargo test --lib`: pass, 12 tests.
- `src/compiler_rust`: Android x86_64 `simple` runtime build pass; artifact `src/compiler_rust/target/x86_64-linux-android/release/simple`.
- `src/compiler_rust`: native `cargo check -p simple-runtime -p simple-compiler -p simple-driver --bin simple` pass.
- `src/compiler_rust/target/release/simple check examples/06_io/ui/tauri_mobile_mdi_smoke.spl`: pass.
- `src/compiler_rust/target/release/simple run examples/06_io/ui/tauri_mobile_mdi_smoke.spl --mode=interpreter --clean`: pass; emits 4 `openWindow` IPC JSON lines.
- `SIMPLE_ANDROID_RUNTIME_X86_64=... SIMPLE_MOBILE_ENTRY_SOURCE=... ANDROID_HOME=/usr/lib/android-sdk ANDROID_SDK_ROOT=/usr/lib/android-sdk cargo tauri android build --target x86_64 --debug`: pass; APK contains `lib/x86_64/libsimple_mobile_runtime_exec.so`.
- Android emulator `simple-pixel-8-api36` install/launch/capture: live MDI pass; screenshot `build/tauri_android_mdi/android_emulator_screenshot_live_mdi_final.png` shows stacked MDI windows from the Simple subprocess.
- Android logcat `build/tauri_android_mdi/emulator_logcat_live_mdi_final.txt`: pass; packaged runtime path selected, subprocess pid logged, 4 `openWindow` messages processed, proof logged as `count=4`, `imageCount=1`, `dragMoved=true`, `hasWindowEventRuntime=true`, `bodyClickRouted=true`, `bodyInputRouted=true`, `htmlRenderable=true`, with no `F DEBUG`, panic, `InvalidUri`, redefinition, parse, or permission errors.
- `sh scripts/check/check-tauri-mobile-mdi-evidence.shs`: pass; validates smoke source IPC, packaged Android native runtime, Android live MDI screenshot/logcat proof, iOS tool availability, and `doc/06_spec` layout guard.
- `bin/simple check src/os/compositor/hosted_wm_capture_evidence.spl`: pass.
- `SIMPLE_BIN=src/compiler_rust/target/release/simple HOSTED_WM_CAPTURE_TIMEOUT_SECS=90 sh scripts/check/check-hosted-wm-capture-evidence.shs`: pass; 270x150 PPM, 40500 non-background pixels, 448 bright pixels, 26453 accent pixels.
- `sh scripts/check/check-electron-simple-web-engine2d-image-taskbar-command-bitmap-evidence.shs`: pass; exact checksum match, mismatch count 0, no blur/tolerance.
- `sh scripts/check/check-shared-wm-renderer-unification-evidence.shs`: pass.
- `RUN_QEMU_LIVE_CAPTURE=0 sh scripts/check/check-wm-launch-capture-evidence.shs`: pass; contract/spec pass, Electron live smoke pass, QEMU live skipped.
- `bin/simple test test/01_unit/os/compositor/wm_action_applier_spec.spl --mode=interpreter --clean`: pass, 12 scenarios.
- `bin/simple test test/01_unit/app/ui/wm_runtime_bridge_spec.spl --mode=interpreter --clean`: pass, 5 scenarios.
- `find doc/06_spec -name '*_spec.spl' | wc -l`: 0.

## Remaining Gaps

- iOS simulator rendering is unavailable on this Linux host (`xcrun`/`xcodebuild` absent); current iOS coverage is runtime selection/error-gating and Tauri shell unit tests.
- QEMU live capture was skipped in the latest WM launch evidence because no live QMP socket was supplied.
- Legacy Simple Web layout manifest still has unrelated opacity/text parity failures; Engine2D taskbar/icon evidence passes exactly.
