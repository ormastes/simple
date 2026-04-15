# Debug State Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/dap/debug_state_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Documentation was generated from executable SSpec scenarios.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/dap/debug_state/result.json` |

## Scenarios

- starts inactive by default
- activates debug mode
- deactivates debug mode
- toggles debug mode
- starts not paused
- pauses execution
- can pause multiple times
- continues from paused state
- can continue when not paused
- handles multiple pause/continue cycles
- sets current file and line
- updates location multiple times
- tracks location through different files
- returns current file
- returns current line
- tracks line changes in same file
- handles line 0
- handles large line numbers
- handles empty file path
- handles paths with special characters
- handles absolute paths
- handles relative paths
- maintains state across operations
- preserves location when toggling debug
- has no overhead when inactive
- handles high frequency location updates
- tracks location while stepping
- maintains breakpoints while paused
- tracks location with active breakpoints
- handles full debug session lifecycle
