# Control Flow - If/Else Specification

Tests for conditional control flow using if/else statements.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1001 |
| Category | Language |
| Status | In Progress |
| Source | `test/feature/usage/control_flow_if_else_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Tests for conditional control flow using if/else statements.
Verifies correct evaluation of conditions and execution of appropriate branches.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/control_flow_if_else/result.json` |

## Scenarios

- executes if body when condition is true
- skips if body when condition is false
- executes if body when condition is true
- executes else body when condition is false
- handles nested if statements
- handles nested if-else
- evaluates first matching condition
- executes final else when no conditions match
- evaluates AND conditions
- evaluates OR conditions
- evaluates NOT conditions
