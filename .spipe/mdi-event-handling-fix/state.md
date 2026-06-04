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
- Pure Simple WM lifecycle keeps focus/z-order coherent across minimize, restore, maximize, destroy, and drag release.
- Hosted pure-WM capture no longer calls the crashing timing extern, writes PPM rows in chunks, and relies on wrapper-side semantic pixel validation.
- Evidence wrappers under `scripts/check` resolve repo root correctly from `scripts/check`; hosted wrapper no longer uses Bash-only `SECONDS`.

## Current Passing Evidence

- `npm --prefix tools/electron-shell run smoke`: pass.
- Electron real MDI proof via `examples/06_io/ui/electron_wm.spl`: pass; 4 windows, desktop present, image rendered, drag moved, full event runtime present, body click/input routed, HTML rendered.
- `cd tools/tauri-shell/src-tauri && cargo test --lib`: pass, 10 tests.
- `bin/simple check src/os/compositor/hosted_wm_capture_evidence.spl`: pass.
- `SIMPLE_BIN=src/compiler_rust/target/release/simple HOSTED_WM_CAPTURE_TIMEOUT_SECS=90 sh scripts/check/check-hosted-wm-capture-evidence.shs`: pass; 270x150 PPM, 40500 non-background pixels, 448 bright pixels, 26453 accent pixels.
- `sh scripts/check/check-electron-simple-web-engine2d-image-taskbar-command-bitmap-evidence.shs`: pass; exact checksum match, mismatch count 0, no blur/tolerance.
- `sh scripts/check/check-shared-wm-renderer-unification-evidence.shs`: pass.
- `RUN_QEMU_LIVE_CAPTURE=0 sh scripts/check/check-wm-launch-capture-evidence.shs`: pass; contract/spec pass, Electron live smoke pass, QEMU live skipped.
- `bin/simple test test/01_unit/os/compositor/wm_action_applier_spec.spl --mode=interpreter --clean`: pass, 12 scenarios.
- `bin/simple test test/01_unit/app/ui/wm_runtime_bridge_spec.spl --mode=interpreter --clean`: pass, 5 scenarios.
- `find doc/06_spec -name '*_spec.spl' | wc -l`: 0.

## Remaining Gaps

- Android/iOS GUI sample rendering has not been executed on a device or simulator in this environment. Current coverage is runtime selection/error-gating and Tauri shell unit tests.
- QEMU live capture was skipped in the latest WM launch evidence because no live QMP socket was supplied.
- Legacy Simple Web layout manifest still has unrelated opacity/text parity failures; Engine2D taskbar/icon evidence passes exactly.
