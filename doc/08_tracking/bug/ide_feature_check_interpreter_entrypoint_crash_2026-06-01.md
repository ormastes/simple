# IDE Feature Check Interpreter Entrypoint Crash

## Closed 2026-09-13 — Does not reproduce: the IDE feature-check entrypoint completes cleanly

- **measured** `bin/simple-interp src/app/ide/main.spl --feature-check --tui` ran to completion with `EXIT=0` and printed the full capability report (last line `check: saml: std.common.saml functions=2 diagnostics=4 ... checks=5/5`). No core dump.
- **measured** No `dumped core` or SIGSEGV text anywhere in the captured run log.
- **inferred** The `--gui` variant was not run here; both modes share the same entrypoint and import closure, so a clean `--tui` run is strong evidence the entrypoint crash is gone.


Status: closed (2026-09-13 triage) — see the "Closed 2026-09-13" section below

## Date
2026-06-01

## Status
Resolved in the current worktree after adding focused IDE capability adapters for sheets, DB admin, and agent dashboard checks.

## Context
While adding `src/app/ide/capabilities.spl` and the `--feature-check` path in `src/app/ide/main.spl`, function-level tests passed, but directly running the IDE source entrypoint through the interpreter did not produce output.

## Reproduction

```bash
timeout 10s bin/simple-interp src/app/ide/main.spl --feature-check --tui
timeout 10s bin/simple-interp src/app/ide/main.spl --feature-check --gui
```

Earlier in the change, both commands ended with:

```text
timeout: the monitored command dumped core
```

## Verified Working Evidence

```bash
bin/simple-interp test test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl
bin/simple-interp test test/01_unit/app/office/slide_outline_spec.spl
bin/simple-interp lint src/app/office/slides/outline.spl test/01_unit/app/office/slide_outline_spec.spl src/app/ide test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl
timeout 15s bin/simple-interp src/app/ide/main.spl --feature-check --tui
timeout 15s bin/simple-interp src/app/ide/main.spl --feature-check --gui
```

## Impact
The IDE capability registry and feature-check report functions are covered by tests, and direct source-entrypoint CLI sanity for `src/app/ide/main.spl` now exits 0 for TUI and GUI feature-check modes. The command still emits pre-existing deprecated generic syntax warnings from `src/app/office/sheets/formula.spl`.
