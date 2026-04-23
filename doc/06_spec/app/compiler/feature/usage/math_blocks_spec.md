# Math Block Tensor Operations Specification

The `m{}` math block supports torch-compatible tensor operations for numerical computing. Each math block is a self-contained DSL expression that returns a Block value.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1090-1098 (subset: tensor ops) |
| Category | Syntax / Math DSL |
| Difficulty | 4/5 |
| Status | Implemented |
| Source | `test/feature/usage/math_blocks_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

The `m{}` math block supports torch-compatible tensor operations for numerical computing.
Each math block is a self-contained DSL expression that returns a Block value.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/math_blocks/result.json` |

## Scenarios

- evaluates addition
- evaluates subtraction
- evaluates multiplication
- evaluates division
- evaluates complex expression
- respects operator precedence
- evaluates power
- evaluates negative numbers
- evaluates sqrt of 16
- evaluates sqrt of 9
- evaluates abs of negative
- evaluates abs of positive
- evaluates frac
- evaluates nested functions
- computes dot product
- computes dot product simple
- evaluates pi greater than 3
- evaluates pi less than 4
- evaluates e greater than 2
- evaluates e less than 3
- evaluates array subscript
- evaluates nested array subscript
- evaluates LaTeX frac
- evaluates LaTeX sqrt
- evaluates Greek letter pi
- exports simple arithmetic
- exports fractions
- exports Greek letters
