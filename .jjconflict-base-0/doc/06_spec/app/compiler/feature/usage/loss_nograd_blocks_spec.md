# loss{} and nograd{} Block Tests

Tests that `loss{}` and `nograd{}` blocks parse, evaluate, and render the same supported math-expression subset as `m{}` blocks. Runtime autograd semantics are covered by `math_autograd_runtime_spec.spl`.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1099-1102 (loss/nograd block support) |
| Category | Syntax / Math DSL |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/feature/usage/loss_nograd_blocks_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests that `loss{}` and `nograd{}` blocks parse, evaluate, and render the
same supported math-expression subset as `m{}` blocks. Runtime autograd
semantics are covered by `math_autograd_runtime_spec.spl`.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 2 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/loss_nograd_blocks/result.json` |
| `summary.txt` | Text artifact | `build/test-artifacts/feature/usage/loss_nograd_blocks/summary.txt` |

## Scenarios

- evaluates addition
- evaluates subtraction
- evaluates multiplication
- evaluates division
- evaluates integer power
- evaluates fractional power
- evaluates frac
- evaluates nested frac
- reads outer variables
- reads multiple outer variables
- evaluates sqrt
- evaluates exp
- evaluates abs
- evaluates addition
- evaluates subtraction
- evaluates multiplication
- evaluates division
- evaluates integer power
- evaluates fractional power
- evaluates frac
- reads outer variables
- evaluates sqrt
- evaluates exp
- renders LaTeX via render_latex_raw
- renders Unicode via to_pretty
- renders LaTeX via render_latex_raw
- renders Unicode via to_pretty
