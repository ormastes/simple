# UI Browser --shared-wm flag silently drops on real launch path

## Status
Open.

## Severity
Medium-High — flag advertised in --help but silently no-ops for the only case that matters.

## Summary
`src/app/ui.browser/main.spl:71` parses `--shared-wm` into `shared_wm`, but the real-launch branch (lines 73-78) calls `run_browser_gui_with_access_store(file_path, 0, access_db)` — the function signature (`app.spl:288`) has no `shared_wm` parameter. The flag is only used for dry-run/planned JSON output (lines 81, 92).

## Evidence
- `main.spl:71` parses flag into `shared_wm: bool`.
- `run_browser_gui_with_access_store(file_path, 0, access_db)` signature has no `shared_wm` parameter.
- `shared_wm_requested_browser`/`shared_wm_backend_kind_browser` helper functions (lines 187-194) exist and are unit-tested in isolation but never called from `main()` (lines 26-93).

## Failure Scenario
`bin/simple ui.browser file.ui.sdn --open --shared-wm` silently launches plain (non-shared-WM) window; flag only affects printed plan when `--open` is absent.

## Next Step
Wire `shared_wm` parameter through to `run_browser_gui_with_access_store` or remove the flag from CLI parsing.
