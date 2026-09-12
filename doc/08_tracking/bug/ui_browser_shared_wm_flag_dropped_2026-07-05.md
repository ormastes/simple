# UI Browser --shared-wm flag silently drops on real launch path

## Status

**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)
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

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule C: filed before 2026-07-29, no runnable repro cheap enough to verify in this pass); closed as stale per the "too old / not valid -> close" triage policy, superseding the prior status line above. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification if reopened.
