# Step Modes Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/dap/step_modes_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
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
| `result.json` | JSON artifact | `target/test-artifacts/feature/dap/step_modes/result.json` |

## Scenarios

- sets continue mode
- does not break without breakpoint
- sets step over mode
- breaks at same depth
- breaks at lower depth
- does not break at higher depth
- sets step into mode
- breaks at any depth - same level
- breaks at any depth - deeper
- breaks at any depth - shallower
- sets step out mode
- breaks at lower depth
- does not break at same depth
- does not break at higher depth
- transitions from Continue to StepOver
- transitions from StepOver to StepInto
- transitions from StepInto to StepOut
- returns to Continue after step completes
- tracks depth correctly
- stores and retrieves start depth
- breakpoints override continue mode
- breakpoints work with step modes
