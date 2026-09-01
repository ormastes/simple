# Electron MDI windows unreachable from live entrypoint

## Status
Open.

## Severity
High — documented mandatory MDI contract for electron lane is non-functional end-to-end.

## Summary
The live electron entrypoint (`src/app/ui.electron/bridge.js:210-212`) hardcodes `src/app/ui.electron/app.spl` as the only reachable Simple-side process. That entrypoint's `run_electron` only emits single-page `{"type":"render"}` messages via `electron_render_ipc_json`, never calling `build_ipc_open_window`/`build_ipc_render_window`/`build_ipc_close_window`.

## Evidence
- `bridge.js:398-699` contains ~300 lines of fully-built DOM window-management JS (`receiveElectronMessage`, create/focus/drag/resize/close/z-order) only driven by MDI message types.
- Only code emitting `openWindow` is `src/app/ui_shared_mdi/main.spl` (a demo entry never spawned by bridge.js; no reference to `ui_shared_mdi` in bridge.js).
- Traced path: `npm run desktop` → bridge.js → app.spl → electron_render_ipc_json — all three confirm flat single-surface rendering.

## Failure Scenario
Launch via documented path (`npm run desktop`), open any `.ui.sdn` file → single surface window; the entire MDI internal-window subsystem is dead code because nothing sends the messages that exercise it.

## Next Step
Either route MDI-aware demo entry from bridge.js, or wire shared-WM support into the reachable `run_electron` path and remove the dead JS.
