# Math Autograd Runtime Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/usage/math_autograd_runtime_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Documentation was generated from executable SSpec scenarios.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 2 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/math_autograd_runtime/result.json` |
| `summary.txt` | Text artifact | `target/test-artifacts/feature/usage/math_autograd_runtime/summary.txt` |

## Scenarios

- evaluates scalar math expression
- evaluates with implicit multiplication
- computes gradients on requires_grad parameter
- accumulates gradients across loss blocks
- keeps detached values out of autograd and restores gradient tracking after escaped nograd
- prevents gradient recording
- nested nograd does not leak state
- only tracks gradient-enabled parts
- resumes normal gradient behavior
