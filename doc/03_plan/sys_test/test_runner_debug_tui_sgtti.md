# Test Runner Debug TUI SGTTI System Test Plan

## Scope

Validate the `--session-debug` TUI evidence surface for the test runner:

- render deterministic session-debug text from a `SessionSchedule`
- capture visible TUI text under `build/test-artifacts`
- expose the same state through `SgttiTestDriver`
- keep parser/help behavior aligned with `--session-debug`
- prove normal runner entrypoints do not import SGTTI or construct debug TUI state

## Requirements Covered

| ID | Requirement | Evidence |
|----|-------------|----------|
| REQ-TRD-001 | Session-debug mode renders target, mode, enabled/debug flags, counts, and groups. | `test/03_system/app/testing/feature/test_runner_debug_tui_sgtti_spec.spl` |
| REQ-TRD-002 | The rendered TUI is captured as text evidence. | `build/test-artifacts/03_system/app/testing/feature/test_runner_debug_tui_sgtti/debug_tui.txt` |
| REQ-TRD-003 | The debug TUI is queryable through SGTTI/WinText visible state. | `test/03_system/app/testing/feature/test_runner_debug_tui_sgtti_spec.spl` |
| REQ-TRD-004 | `--session-debug` parser/help behavior remains visible and aligned. | `test/03_system/app/testing/feature/test_runner_debug_tui_sgtti_spec.spl` |
| REQ-TRD-005 | SGTTI has zero overhead on normal runner entrypoints unless explicitly imported by test/debug code. | import-boundary scenario in `test_runner_debug_tui_sgtti_spec.spl` |

## Execution

```bash
SIMPLE_LIB=src bin/simple-interp test/03_system/app/testing/feature/test_runner_debug_tui_sgtti_spec.spl
SIMPLE_LIB=src bin/simple check src/app/test_daemon/session_types.spl src/app/test_runner_new/test_runner_debug_tui.spl src/app/test_runner_new/main.spl test/03_system/app/testing/feature/test_runner_debug_tui_sgtti_spec.spl
find doc/06_spec -name '*_spec.spl' | wc -l
```

## Capture Policy

The spec writes TUI text evidence to
`build/test-artifacts/03_system/app/testing/feature/test_runner_debug_tui_sgtti/debug_tui.txt`.
Generated manuals embed or link that capture through `**TUI Captures:**`.

## Zero-Overhead Policy

SGTTI is a test/debug evidence interface. Default production/test-runner paths
must not import SGTTI or debug TUI construction modules. Native entry-closure
builds should therefore omit SGTTI when the debug/test surface is not imported.
