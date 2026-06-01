# IDE Feature Check Interpreter Entrypoint Crash

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
bin/simple-interp test test/system/app/ide/feature/ide_office_plugin_suite_spec.spl
bin/simple-interp test test/unit/app/office/slide_outline_spec.spl
bin/simple-interp lint src/app/office/slides/outline.spl test/unit/app/office/slide_outline_spec.spl src/app/ide test/system/app/ide/feature/ide_office_plugin_suite_spec.spl
timeout 15s bin/simple-interp src/app/ide/main.spl --feature-check --tui
timeout 15s bin/simple-interp src/app/ide/main.spl --feature-check --gui
```

## Impact
The IDE capability registry and feature-check report functions are covered by tests, and direct source-entrypoint CLI sanity for `src/app/ide/main.spl` now exits 0 for TUI and GUI feature-check modes. The command still emits pre-existing deprecated generic syntax warnings from `src/app/office/sheets/formula.spl`.
