# Dap Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/dap/dap_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
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
| `result.json` | JSON artifact | `build/test-artifacts/feature/dap/dap/result.json` |

## Scenarios

- handles initialize request
- responds with adapter capabilities
- sets line breakpoints
- sets conditional breakpoints
- sets function breakpoints
- starts program execution
- handles continue request
- handles step over request
- handles step into request
- handles step out request
- handles pause request
- retrieves stack trace
- retrieves scopes for frame
- retrieves variables in scope
- evaluates expressions in stopped context
- evaluates watch expressions
- sends stopped event on breakpoint hit
- sends output event for program output
- sends terminated event when program exits
