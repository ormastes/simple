# Integration Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/dap/integration_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
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
| `result.json` | JSON artifact | `target/test-artifacts/feature/dap/integration/result.json` |

## Scenarios

- executes a simple debugging session
- steps through sequential code
- steps over function call
- steps into function call
- steps out of function
- tracks recursive factorial calls
- handles deep recursion
- debugs across multiple files
- hits breakpoint then steps
- sets breakpoint while stepping
- handles breakpoint at non-existent line
- recovers from pause without continue
- handles missing stack frames
- handles rapid mode switching
- handles many breakpoints
- handles frequent location updates
- handles large stack depths
- debugs a simple program
- debugs loop with breakpoint
- debugs conditional branches
