# UI Browser --shared-wm flag silently drops on real launch path
## Resolved — verified 2026-11-25 by code inspection

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## Verification 2026-11-25 (release/1.0.0 @ 64dfa6d980f)

The flag is now wired end-to-end; the failure scenario below no longer
applies:

- `src/app/ui.browser/main.spl:80` parses `--shared-wm` /
  `SIMPLE_UI_BROWSER_SHARED_WM=1` via `shared_wm_requested_browser` (now
  called from `main()`, not dead code).
- `src/app/ui.browser/main.spl:89` — the real-launch branch passes it:
  `run_browser_gui_with_access_store(file_path, 0, access_db, shared_wm)`.
- `src/app/ui.browser/app.spl:362` — the signature now carries
  `shared_wm: bool = false`; lines 365-366 route a true value to
  `run_shared_wm_browser("Simple Browser")` (app.spl:347), which joins the
  shared host WM instead of spawning a standalone winit window.
- `shared_wm_backend_kind_browser` is exercised by
  `test/01_unit/app/ui/shared_wm_entrypoints_spec.spl:60,71`.

Limit: runtime verification was environment-blocked on this Windows host —
`bin/simple.exe test` fails repo-wide at HEAD with
`unknown decorator '@representation_boundary'` (seed predates commit
cfd89933699), and a `run` probe importing `app.ui.browser.main` hits the
same decorator in the lib import chain. Verified by code inspection only.

## Status
Resolved (was: Open).

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

