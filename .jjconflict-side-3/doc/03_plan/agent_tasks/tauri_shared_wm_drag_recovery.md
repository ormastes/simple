# Tauri Shared-WM Drag Recovery Plan

## Status
The goal is not achieved yet. The user reports the Tauri MDI/window-manager
surface still cannot drag windows. The last visible failure was caused by the
Tauri `--shared-wm` launch path showing a static Rust data-URL mock instead of
the live Simple shared-WM process.

## Current Fix In Progress
- Remove the static shared-WM mock path from `tools/tauri-shell/src-tauri/src/lib.rs`.
- Force `--shared-wm` to spawn `src/app/ui/main.spl tauri ... --shared-wm`.
- Use `mdi_shell_html()` as the initial page so `openWindow` / `renderWindow`
  messages attach to the live MDI bridge.

## Acceptance Criteria
- `--shared-wm` startup logs a Simple subprocess PID, not `shared WM visual mode`.
- Simple emits `openWindow` messages for MDI windows.
- Tauri injects `window.__SIMPLE_TAURI_WM__` and `#wm-desktop`.
- Pointer or mouse drag on `.wm-titlebar` changes `.wm-window.style.left/top`.
- Button clicks and text input inside `.wm-body` are routed to Simple.
- The user can manually drag at least one MDI window in the opened Tauri app.

## Test Plan
- Run `cargo test --manifest-path tools/tauri-shell/src-tauri/Cargo.toml -- --nocapture`.
- Run `cargo build --manifest-path tools/tauri-shell/src-tauri/Cargo.toml`.
- Run `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/app/ui.web/html.spl`.
- Launch:
  `SIMPLE_LIB=src SIMPLE_EXECUTION_MODE=interpret SIMPLE_TIMEOUT_SECONDS=600 SIMPLE_UI_TAURI_SHARED_WM=1 tools/tauri-shell/src-tauri/target/debug/simple-tauri-shell src/compiler_rust/target/release/simple examples/06_io/ui/simpleos_web_wm.ui.sdn --shared-wm`
- Verify the log does not contain `shared WM visual mode`.
- If drag still fails, instrument `tauri_mdi_init_script()` with a proof hook
  that reports titlebar pointerdown, pointermove, pointerup, and final position.

## Follow-Up Work
- Add a regression test asserting shared-WM no longer calls the static data URL
  path and does include `--shared-wm` in the Simple subprocess args.
- Remove or quarantine any generated/static demo code that can be mistaken for
  the real SimpleOS window manager.
