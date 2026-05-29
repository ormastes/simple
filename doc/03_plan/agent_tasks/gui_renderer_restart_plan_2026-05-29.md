# GUI Renderer Restart Plan — 2026-05-29

## Objective

Resume the GUI renderer goal without relying on chat history:

- Open and verify a GUI app backed by Tauri.
- Open and verify a GUI app backed by the pure Simple web renderer.
- Verify Simple web renderer + Engine2D CPU path.
- Verify Simple web renderer + Engine2D Metal-requested path.
- Open and verify the Simple browser app using the Simple web renderer.
- Keep Pure Simple as the main implementation. Rust changes are only seed/runtime bridge work.

## Current Pause State

The current worktree at pause time contains only:

- `doc/test/test_db_runs.sdn.lock` as an uncommitted generated lock file.
- This restart plan.

The previous GUI/browser source fix was committed as jj change `yqupqtwunsnr`
(`fix: open simple renderer browser and tauri gui paths`) during the session,
but a later rebase left current `main` without those source edits. If the same
fix is still needed, recover it with:

```bash
jj restore --from yqupqtwunsnr --to @ \
  scripts/macos-gui-run.shs \
  src/app/ui.browser/app.spl \
  src/lib/gc_async_mut/gpu/engine2d/backend_software.spl \
  src/lib/nogc_sync_mut/io/string_helpers.spl \
  src/lib/nogc_sync_mut/ui/access_store.spl \
  test/unit/lib/gpu/engine2d/backend_software_simd_spec.spl
```

Also confirm whether `examples/ui/web_engine2d_gui.spl` on current `main`
already has the wall-clock visibility loop. If not, recover or reapply:

- `extern fn rt_time_now_unix_micros() -> i64`
- `val end_at = rt_time_now_unix_micros() + 60000000`
- `while running and rt_time_now_unix_micros() < end_at:`

## Evidence Already Collected

These checks passed during the session and should be repeated after restore:

- Headless Simple web renderer:
  - `examples/ui/web_engine2d_gui.spl`
  - CPU and Metal-requested paths both rendered 768 pixels.
  - CPU/Metal sample parity printed `true true`.
- On-screen Simple web renderer:
  - `scripts/macos-gui-run.shs examples/ui/web_engine2d_gui.spl`
  - macOS window: `Simple Web + Engine2D`, outer size `640x512`.
  - Screenshot: `build/screenshots/web_engine2d_gui_current.png`.
- Headless Simple browser:
  - `/tmp/browser_snapshot_probe.spl`
  - CPU snapshot wrote `build/screenshots/browser_cpu_probe.ppm`.
  - Metal-requested snapshot wrote `build/screenshots/browser_metal_probe.ppm`.
- On-screen Simple browser:
  - `scripts/macos-gui-run.shs src/app/ui/main.spl browser examples/ui/hello_gui.ui.sdn --backend cpu`
  - macOS window: `Simple Browser`, outer size `336x256`.
  - Screenshot: `build/screenshots/simple_browser_cpu_gui_current.png`.
- Tauri:
  - `scripts/macos-tauri-simple-run.shs examples/ui/hello_tauri.ui.sdn`
  - Tauri shell opened a native window with rendered `Hello Tauri`.
  - Screenshot: `build/screenshots/tauri_gui_current.png`.

## Known Fixes To Re-Check

1. `scripts/macos-gui-run.shs`
   - Must forward extra program args after the `.spl` entry.
   - Must absolutize existing forwarded file paths before `open ... --args`.

2. `src/app/ui.browser/app.spl`
   - Browser loop should continuously pump `rt_winit_event_loop_poll_events(..., 1)`.
   - Use `rt_time_now_unix_micros()` to present periodically without `rt_thread_sleep`.
   - Do not auto-open SQLite access store unless `access_db_path` is explicitly provided, because default interpreter builds may lack `rt_sqlite_open`.

3. `src/lib/nogc_sync_mut/io/string_helpers.spl`
   - `text_hash_native` must avoid interpreter integer overflow.

4. Engine2D SIMD path
   - Keep Pure Simple scalar behavior correct.
   - Ensure `backend_software_simd_spec.spl` passes.

## Restart Verification Commands

```bash
timeout 75s env SIMPLE_TIMEOUT_SECONDS=0 SIMPLE_EXECUTION_MODE=interpret \
  SIMPLE_LIB=$PWD/src src/compiler_rust/target/debug/simple \
  examples/ui/web_engine2d_gui.spl

timeout 120s env SIMPLE_TIMEOUT_SECONDS=0 SIMPLE_EXECUTION_MODE=interpret \
  SIMPLE_LIB=$PWD/src src/compiler_rust/target/debug/simple \
  test/unit/lib/gpu/engine2d/backend_software_simd_spec.spl

timeout 100s env SIMPLE_TIMEOUT_SECONDS=0 SIMPLE_EXECUTION_MODE=interpret \
  SIMPLE_LIB=$PWD/src src/compiler_rust/target/debug/simple \
  /tmp/browser_snapshot_probe.spl

env SIMPLE_TIMEOUT_SECONDS=120 \
  scripts/macos-gui-run.shs examples/ui/web_engine2d_gui.spl

env SIMPLE_TIMEOUT_SECONDS=180 \
  scripts/macos-gui-run.shs src/app/ui/main.spl browser \
  examples/ui/hello_gui.ui.sdn --backend cpu

env SIMPLE_TIMEOUT_SECONDS=120 \
  scripts/macos-tauri-simple-run.shs examples/ui/hello_tauri.ui.sdn
```

After on-screen runs, capture screenshots under `build/screenshots/` and confirm
the macOS window metadata with `osascript` or visible screenshot evidence.

## Sync Command

After restoring or reapplying source fixes and verifying:

```bash
jj commit -m "fix: open simple renderer browser and tauri gui paths"
before=$(jj file list | wc -l | tr -d ' ')
jj git fetch
jj rebase -r @- -d main@origin
after=$(jj file list | wc -l | tr -d ' ')
test "$after" -ge "$before"
jj bookmark set main -r @-
jj git push --bookmark main
jj git push --dry-run --bookmark main
```
