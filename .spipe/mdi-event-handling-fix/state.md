# MDI Event Handling Fix State

Date: 2026-06-05

## Task Type

feature

## Refined Goal

Provide backend-neutral MDI CSS/theme application, title-bar widget mounting, and event routing across Electron, Tauri, and pure Simple HTML/WM paths.

## Acceptance Criteria

- AC-1: Shared MDI desktop output includes an applied CSS/theme marker and taskbar/menu CSS that Electron, Tauri, and pure Simple renderers can consume without backend-specific IPC changes.
- AC-2: Shared HTML window helpers can render escaped title-bar controls with reusable CSS hooks for pure Simple body rendering.
- AC-3: Electron MDI chrome mounts app-provided title-bar widgets from window HTML and routes their actions/inputs/keys through window-scoped event handling.
- AC-4: Tauri MDI chrome mounts app-provided title-bar widgets from window HTML and routes their actions/inputs/keys through window-scoped event handling.
- AC-5: Focused Simple, Electron syntax, and Tauri unit checks pass; live Electron/Tauri evidence must prove `openWindow` windows include the title-bar widget marker before this feature is complete.

## Phase

implementation-complete

## Scope

Investigate and fix wrong or dummy MDI behavior across Electron, Tauri, and pure Simple-backed WM paths, with special attention to event routing and taskbar/icon rendering evidence.

## Implemented

- Electron renderer forwards common web input envelopes instead of dummy event IPC.
- Shared MDI demo renders stable app-provided Terminal action/input controls and a visible dock/taskbar with six styled icon pills and readable labels.
- Electron MDI windows route body click, input, key, pointer, and mouse events; the real MDI proof now exercises the app-provided Terminal button/input and a rendered keydown event instead of injecting synthetic proof controls.
- Electron MDI proof now captures a real Electron page PNG when `SIMPLE_ELECTRON_MDI_SCREENSHOT_PATH` is set, and `scripts/check/check-electron-mdi-evidence.shs` validates JSON event/render proof, visible taskbar DOM, nonblank screenshot pixels, and semantic dock/icon/label pixel regions under Xvfb.
- Electron live-smoke package entry points at `examples/06_io/ui/hello_electron.ui.sdn`.
- Tauri MDI proof now requires the full event runtime surface: `bindWindowEvents`, action, key, input, and mouse senders; the proof path uses app-provided controls, records action/input/key routing fields, and reports taskbar item/icon counts plus visible icon/label checks.
- Tauri mobile/iOS runtime selection includes iOS bundled runtime hooks and explicit no-runtime live-MDI bridge error messaging.
- Tauri mobile startup errors render through a mobile-safe inline shell page instead of falling back to `tauri.localhost` asset failure or Android `data:` URL crashes.
- Tauri Android can package a target-compatible Simple runtime as an extracted native library and bundle a self-contained Simple MDI smoke source for live subprocess rendering.
- Android live MDI replays early subprocess window messages after the WebView shell is ready and logs mobile MDI proof without closing the app.
- iOS live MDI evidence now has a repeatable wrapper: `scripts/check/check-tauri-ios-mobile-mdi-evidence.shs`; on macOS it runs a Tauri iOS simulator URL-mode WebView probe backed by host-generated Simple `openWindow` IPC from `examples/06_io/ui/tauri_mobile_mdi_smoke.spl`, captures a screenshot, and validates MDI windows, taskbar icons, drag, body click, body input, image, source window count, Simple smoke text, and HTML render proof reported back to a local evidence server.
- The iOS/Android MDI WebView probe and screenshot validator now live in `scripts/check/ios_mdi_probe_server.py` with Linux-runnable self-tests for Simple IPC parsing, the proof endpoint, proof validation, browser-executed event handling, Tauri URL-mode WebView execution, PNG screenshot nonblank validation, and semantic dock/taskbar pixel validation.
- Rust compiler/runtime Android portability holes fixed for PTY ioctl/errno, interpreter PTY, torch runtime library naming, and native-project Android symbol stubs.
- Pure Simple WM lifecycle keeps focus/z-order coherent across minimize, restore, maximize, destroy, and drag release.
- Hosted pure-WM capture no longer calls the crashing timing extern, writes PPM rows in chunks, and relies on wrapper-side semantic pixel validation; hosted capture timeout is now a failing proof, not an `unavailable` success.
- Evidence wrappers under `scripts/check` resolve repo root correctly from `scripts/check`; hosted wrapper no longer uses Bash-only `SECONDS`, QEMU/GTK WM wrapper paths call `scripts/check/check-wm-launch-capture-evidence.shs`, and WM launch evidence is strict by default unless a live proof is explicitly skipped by environment.
- SPipe dev command and submodule gitlink check wrappers resolve the repository root from `scripts/setup` and `scripts/check` correctly.
- Shared HTML window content now exposes backend-neutral title-bar widget helpers (`html_titlebar_button`, `html_window_content_with_titlebar_widgets`, `html_window_info_with_titlebar_widgets`) so pure Simple HTML, Electron MDI chrome, and Tauri MDI chrome can share app-provided title-bar controls.
- Shared MDI desktop rendering now emits a `qmake-theme-applied` CSS marker and QMake-style theme CSS for the shared taskbar/menu shell.
- Electron and Tauri MDI runtimes now clone `[data-simple-titlebar-widget]` controls from app HTML into the host title bar and route click/input/key events through the existing window-scoped event delegate.

## Current Passing Evidence

- `npm --prefix tools/electron-shell run smoke`: pass.
- Electron real MDI proof via `examples/06_io/ui/electron_wm.spl`: pass; 4 windows, desktop present, image rendered, drag moved, full event runtime present, app-provided action/input controls found, click/input/key routed, 6 taskbar items/icons visible, 6 labels visible, HTML rendered.
- `SIMPLE_MDI_FAST_PROOF=1 sh scripts/check/check-electron-mdi-evidence.shs`: pass; validates Electron MDI JSON proof, screenshot `build/electron_mdi_evidence/electron_mdi.png` as a nonblank 1279x719 PNG with 64 sampled colors, and semantic dock/icon regions (`dark_pixels=898344`, `bright_pixels=5449`, `accent_pixels=3856`, `dock_dark_pixels=135835`, `dock_bright_pixels=810`, `dock_accent_pixels=3467`).
- `cd tools/tauri-shell/src-tauri && cargo test`: pass, 12 library tests plus binary/doc-test harnesses; includes the MDI bootstrap/runtime surface checks after adding app-control/key and taskbar proof fields.
- `src/compiler_rust`: Android x86_64 `simple` runtime build pass; artifact `src/compiler_rust/target/x86_64-linux-android/release/simple`.
- `src/compiler_rust`: native `cargo check -p simple-runtime -p simple-compiler -p simple-driver --bin simple` pass.
- `src/compiler_rust/target/release/simple check examples/06_io/ui/tauri_mobile_mdi_smoke.spl`: pass.
- `src/compiler_rust/target/release/simple run examples/06_io/ui/tauri_mobile_mdi_smoke.spl --mode=interpreter --clean`: pass; emits 4 `openWindow` IPC JSON lines.
- `SIMPLE_ANDROID_RUNTIME_X86_64=... SIMPLE_MOBILE_ENTRY_SOURCE=... ANDROID_HOME=/usr/lib/android-sdk ANDROID_SDK_ROOT=/usr/lib/android-sdk cargo tauri android build --target x86_64 --debug`: pass; APK contains `lib/x86_64/libsimple_mobile_runtime_exec.so`.
- Android emulator `simple-pixel-8-api36` install/launch/capture: live MDI pass; screenshot `build/tauri_android_mdi/android_emulator_screenshot_live_mdi_final.png` shows stacked MDI windows from the Simple subprocess.
- Android live MDI screenshot PNG validation: pass; `build/tauri_android_mdi/android_emulator_screenshot_live_mdi_final.png` is 1080x2400 with 64+ sampled colors.
- Android live MDI screenshot semantic validation: pass; same screenshot has MDI-window coverage plus dedicated dock/taskbar body, label, and icon-color checks.
- Android logcat `build/tauri_android_mdi/emulator_logcat_live_mdi_final.txt`: pass; packaged runtime path selected, subprocess pid logged, 4 `openWindow` messages processed, proof logged as `count=4`, `imageCount=1`, `dragMoved=true`, `hasWindowEventRuntime=true`, app action/input controls found, `bodyClickRouted=true`, `bodyInputRouted=true`, `bodyKeyRouted=true`, taskbar items/icons visible, `htmlRenderable=true`, with no `F DEBUG`, panic, `InvalidUri`, redefinition, parse, or permission errors.
- Synthetic Android screenshot semantic validation: pass; `python3 scripts/check/ios_mdi_probe_server.py --validate-android-mdi-screenshot <synthetic-png>` reports `android_live_mdi_screenshot_semantic=pass` with `dock_dark_pixels`, `dock_bright_pixels`, and `dock_accent_pixels`.
- `python3 scripts/check/ios_mdi_probe_server.py --self-test`: pass.
- `sh scripts/check/check-tauri-ios-mobile-mdi-evidence.shs --browser-self-test`: pass; renders the Simple-IPC-backed probe in Electron/Xvfb, validates proof JSON, validates screenshot PNG pixels, and validates MDI/taskbar semantics (`dark_pixels=268128`, `bright_pixels=37802`, `accent_pixels=2300`, `taskbar_accent_pixels=1508`, `dark_rows=817`).
- `sh scripts/check/check-tauri-ios-mobile-mdi-evidence.shs --tauri-url-self-test`: pass; renders the Simple-IPC-backed probe through the Tauri desktop shell URL-mode path, validates Tauri external URL log markers, captures `build/tauri_ios_mdi/ios_mdi_probe_tauri_url.png`, validates it as a 1280x720 nonblank PNG, and validates MDI/taskbar semantics (`dark_pixels=870201`, `bright_pixels=38411`, `accent_pixels=2143`, `taskbar_accent_pixels=1509`, `dark_rows=719`).
- `sh scripts/check/check-tauri-mobile-mdi-evidence.shs`: pass; validates smoke source IPC, packaged Android native runtime, Android live MDI screenshot/logcat proof, iOS MDI helper/browser/Tauri URL-mode self-tests, iOS tool availability, and `doc/06_spec` layout guard.
- `sh -n scripts/check/check-tauri-ios-mobile-mdi-evidence.shs`: pass.
- `sh scripts/check/check-tauri-ios-mobile-mdi-evidence.shs`: unavailable on this Linux host; reports that iOS simulator evidence requires macOS with Xcode.
- `bin/simple check src/os/compositor/hosted_wm_capture_evidence.spl`: pass.
- `SIMPLE_BIN=src/compiler_rust/target/release/simple HOSTED_WM_CAPTURE_TIMEOUT_SECS=90 sh scripts/check/check-hosted-wm-capture-evidence.shs`: pass; 270x150 PPM, 40500 non-background pixels, 448 bright pixels, 26453 accent pixels. Timeout paths now emit `hosted_wm_capture_status=fail` and exit 1.
- `sh scripts/check/check-electron-simple-web-engine2d-image-taskbar-command-bitmap-evidence.shs`: pass; exact checksum match, mismatch count 0, no blur/tolerance.
- `sh scripts/check/check-shared-wm-renderer-unification-evidence.shs`: pass.
- `RUN_QEMU_LIVE_CAPTURE=0 SIMPLE_MDI_FAST_PROOF=1 sh scripts/check/check-wm-launch-capture-evidence.shs`: pass; contract/spec pass, Electron live smoke pass, strengthened Electron MDI JSON+screenshot/semantic taskbar proof pass, QEMU live skipped. By default the wrapper now fails if requested Electron/QEMU live evidence is unavailable.
- `RUN_ELECTRON_LIVE_SMOKE=0 RUN_ELECTRON_MDI_EVIDENCE=0 RUN_QEMU_LIVE_CAPTURE=0 WM_CAPTURE_EVIDENCE_TIMEOUT_SECS=120 BUILD_DIR=build/wm-launch-capture-evidence-codex-smoke REPORT_PATH=build/wm-launch-capture-evidence-codex-smoke/report.md sh scripts/check/check-wm-launch-capture-evidence.shs`: pass; contract/spec pass with Electron/QEMU live probes explicitly skipped rather than claimed.
- `bin/simple test test/01_unit/os/compositor/wm_action_applier_spec.spl --mode=interpreter --clean`: pass, 12 scenarios.
- `bin/simple test test/01_unit/app/ui/wm_runtime_bridge_spec.spl --mode=interpreter --clean`: pass, 5 scenarios.
- `python3 -m py_compile scripts/check/ios_mdi_probe_server.py && python3 scripts/check/ios_mdi_probe_server.py --self-test && node --check scripts/check/ios_mdi_probe_electron_self_test.js && node --check src/app/ui.electron/bridge.js`: pass.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/ui/html_window_spec.spl --mode=interpreter --clean --fail-fast`: pass, 7 scenarios including title-bar widget CSS/action/escaping coverage.
- `SIMPLE_LIB=src bin/simple check src/lib/common/ui/html_window.spl src/app/ui_shared_mdi/main.spl test/01_unit/lib/common/ui/html_window_spec.spl`: pass.
- `SIMPLE_LIB=src SIMPLE_MDI_FAST_PROOF=1 bin/simple run src/app/ui_shared_mdi/main.spl --mode=interpreter --clean`: pass; emits one `render` frame, four `openWindow` messages (`terminal`, `editor`, `browser`, `files`), and the Terminal title-bar widget marker `data-simple-titlebar-widget` without `Segmentation`, `CODEGEN`, panic, or error output.
- `node --check src/app/ui.electron/bridge.js`: pass.
- `cd tools/tauri-shell/src-tauri && cargo test`: pass, 12 library tests plus binary/doc-test harnesses; Tauri MDI bootstrap assertions include `mountTitlebarWidgets`, `.wm-titlebar-widgets`, and `[data-simple-titlebar-widget]`.
- `sh -n scripts/check/check-wm-launch-capture-evidence.shs && sh -n scripts/check/check-electron-mdi-evidence.shs && sh -n scripts/check/check-tauri-ios-mobile-mdi-evidence.shs && sh -n scripts/check/check-tauri-mobile-mdi-evidence.shs && sh -n scripts/check/check-hosted-wm-capture-evidence.shs && sh -n scripts/check/check-qemu-gtk-wm-capture-evidence.shs`: pass.
- `sh scripts/setup/install-spipe-dev-command.shs --check`: pass.
- `sh scripts/check/check-spipe-submodule-gitlinks.shs --check`: pass; `.spipe/spipe` gitlink and `examples/05_stdlib/spipe` tracked-tree entries verified.
- `find doc/06_spec -name '*_spec.spl' | wc -l`: 0.

## External Evidence Notes

- iOS simulator rendering is unavailable on this Linux host (`xcrun`/`xcodebuild` absent). The macOS proof path is `sh scripts/check/check-tauri-ios-mobile-mdi-evidence.shs`; it uses `SIMPLE_DASHBOARD_URL` to attach Tauri iOS to a local Simple-IPC-backed MDI/event probe rather than trying to execute an Android-style packaged Simple subprocess on iOS.
- QEMU live capture was skipped in the latest WM launch evidence because no live QMP socket was supplied.
- Legacy Simple Web layout manifest still has unrelated opacity/text parity failures; Engine2D taskbar/icon evidence passes exactly.
