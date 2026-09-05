# Three parallel Electron main-loop implementations, two dead

## Status
Open.

## Severity
Medium — dead code, maintenance/confusion risk.

## Summary
Three separate "Electron main loop" implementations exist: `src/app/ui.electron/main.spl` (ElectronMain stub, dev-preview only), `async_app.spl` (AsyncElectronApp with real shared-WM support), and `app.spl` (run_electron, the only reachable one via bridge.js). Only the third is ever spawned in production.

## Evidence
- **main.spl**: Explicitly marked "Dev-preview only... must not be added to CI"; main() is a stub that never loops.
- **async_app.spl**: Contains real `--shared-wm` channel-based loop (`run_shared_wm_electron`); grepped entire repo (`src/`, `test/`) — only referenced by its own file, `__init__.spl` re-export, and isolated unit spec. No CLI entrypoint or bridge.js path ever constructs it.
- **app.spl**: Only reachable path via bridge.js (see bug M1).

## Failure Scenario
Developer finds `--shared-wm` support in `async_app.spl` and assumes it's live; instead, shell always launches `app.spl` with no shared-WM support at all.

## Next Step
Merge logic into one module or delete dead implementations per repo rule: no duplicate module splits.
