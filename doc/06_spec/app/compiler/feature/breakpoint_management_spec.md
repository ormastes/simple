# Breakpoint Management Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/dap/breakpoint_management_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
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
| `result.json` | JSON artifact | `build/test-artifacts/feature/dap/breakpoint_management/result.json` |

## Scenarios

- adds a single breakpoint
- adds multiple breakpoints in same file
- adds breakpoints in different files
- allows duplicate breakpoints with different IDs
- removes a breakpoint
- removes specific breakpoint from multiple
- handles removing non-existent breakpoint
- returns false for non-existent breakpoint
- checks breakpoint in correct file only
- checks breakpoint at correct line only
- should break when at breakpoint location
- should not break when not at breakpoint
- should not break when debug inactive
- handles line number 0
- handles large line numbers
- handles empty file path
- handles special characters in file path
