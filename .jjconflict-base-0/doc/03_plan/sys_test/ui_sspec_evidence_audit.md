# UI SSPEC Evidence Audit System Test Plan

## Scope

This audit verifies that the critical UI-facing application system specs have
both executable SSPEC files and mirrored generated manuals under `doc/06_spec`.
It also checks that the UI testing surfaces cover browser UI access, Draw IR
inspection, SGTTI shared state, IDE Office TUI feature checks, and the
test-runner debug TUI capture path.

## Requirements

| Requirement | Evidence |
|-------------|----------|
| REQ-UI-SSPEC-001 | Core UI app feature specs have mirrored generated manuals. |
| REQ-UI-SSPEC-002 | Browser, Draw IR, SGTTI, IDE, and test-runner debug TUI specs expose concrete UI evidence mechanisms. |
| REQ-UI-SSPEC-003 | Generated manuals are non-stub scenario manuals with source traceability. |

## Execution

```sh
SIMPLE_LIB=src bin/simple-interp test/03_system/app/testing/feature/ui_sspec_evidence_audit_spec.spl
SIMPLE_LIB=src bin/simple check test/03_system/app/testing/feature/ui_sspec_evidence_audit_spec.spl
```

## Pass Criteria

The audit passes when all expected executable specs and manuals exist, the
manuals reference their source specs, and critical UI evidence markers are
present in the corresponding executable specs.
