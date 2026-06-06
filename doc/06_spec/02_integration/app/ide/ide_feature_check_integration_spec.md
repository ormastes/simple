# ide_feature_check_integration_spec

> IDE feature-check integration specification.

## Overview

This manual verifies the real IDE command path through `bin/simple run src/app/ide/main.spl`. It complements the system spec by proving that the restored production entrypoint prints complete TUI and GUI feature-check reports and still preserves normal help and unknown-option behavior.

**Requirements:** `doc/03_plan/sys_test/ide_office_plugin_suite.md`
**Plan:** `doc/03_plan/sys_test/ide_office_plugin_suite.md`
**Design:** `doc/03_plan/app/ide/simple_ide_submodule_plan_2026-06-04.md`
**Research:** N/A - integration hardening for an existing restored feature lane.

## Execution

```bash
SIMPLE_LIB=src bin/simple-interp test/02_integration/app/ide/ide_feature_check_integration_spec.spl
```

Expected result: `3 examples, 0 failures`.

## Coverage Matrix

| Area | Scenario Evidence |
|------|-------------------|
| TUI feature-check | CLI output starts with the IDE feature-check header and includes all five capability groups. |
| GUI feature-check | CLI output includes GUI backend, TUI panel, and launch summaries. |
| CLI hardening | `--help` exits successfully and `--bad-mode` exits with an unknown-option error. |

## Scenarios

### IDE feature-check CLI integration

#### prints the complete TUI feature-check manual through the app entrypoint

```simple
val (out, err, code) = _run_ide(["--feature-check", "--tui"])
expect(code).to_equal(0)
expect(out).to_start_with("Simple IDE feature check")
expect(out).to_contain("mode: tui")
expect(out).to_contain("capabilities: 5")
expect(out).to_contain("markdown: Markdown Preview")
expect(out).to_contain("slides: Presentation Slides")
expect(out).to_contain("sheets: Spreadsheet")
expect(out).to_contain("agent-dashboard: Agent Dashboard")
expect(out).to_contain("db-admin: Database Admin")
expect(out).to_contain("plugin-manifest: plugins: entries=5")
```

#### prints the complete GUI feature-check manual through the app entrypoint

```simple
val (out, err, code) = _run_ide(["--feature-check", "--gui"])
expect(code).to_equal(0)
expect(out).to_start_with("Simple IDE feature check")
expect(out).to_contain("mode: gui")
expect(out).to_contain("gui-backend: theme=dark")
expect(out).to_contain("tui-panels: preview=")
expect(out).to_contain("launch: launch: tui=tui gui=gui sdl=gui-sdl")
```

#### keeps normal IDE help and unknown option behavior intact

```simple
val (help_out, help_err, help_code) = _run_ide(["--help"])
expect(help_code).to_equal(0)
expect(help_out).to_contain("Usage: simple ide")
expect(help_out).to_contain("--feature-check")

val (bad_out, bad_err, bad_code) = _run_ide(["--bad-mode"])
expect(bad_code).to_equal(1)
expect(bad_out).to_contain("Unknown option: --bad-mode")
```
