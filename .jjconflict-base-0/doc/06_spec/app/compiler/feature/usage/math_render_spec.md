# Math Block Rendering Specification

Intensive tests for the math expression rendering pipeline:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1090-1102 (math block rendering) |
| Category | Syntax / Math DSL / Rendering |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/feature/usage/math_render_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 129 |
| Active scenarios | 129 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Intensive tests for the math expression rendering pipeline:
- `to_text()`:         Normalized plain text
- `to_debug()`:        AST structure
- `to_pretty()`:       Unicode pretty print
- `to_md()`:           Markdown LaTeX
- `render_latex_raw()`: Raw LaTeX output

Covers edge cases: nested fracs, sum/integral binders, transpose,
subscript, complex DL equations, Greek letters, operator precedence,
implicit multiplication, and LaTeX-style commands.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/math_render/result.json` |

## Scenarios

- renders addition
- renders subtraction
- renders multiplication
- renders division
- renders negation
- renders parenthesized group
- renders power
- renders complex expression
- renders sqrt
- renders abs
- renders frac as division
- renders nested frac
- renders multi-arg function
- renders subscript
- renders nested subscript
- renders transpose
- renders sum
- renders integral
- renders number
- renders float
- renders identifier
- renders addition
- renders subtraction
- renders multiplication
- renders division
- renders power
- renders negation
- renders group
- renders frac
- renders nested frac
- renders sqrt call
- renders multi-arg call
- renders subscript
- renders transpose
- renders add-mul precedence
- renders power right-assoc with unary
- renders sigmoid
- renders layer norm
- renders addition
- renders subtraction
- renders explicit multiplication as cdot
- renders division
- renders power
- renders negation
- renders frac
- renders nested frac
- renders frac with complex numerator
- renders frac with complex denominator
- renders sqrt
- renders known function sin
- renders known function cos
- renders known function exp
- renders known function log
- renders known function ln
- renders known function tanh
- renders unknown function as operatorname
- renders nested sqrt in frac
- renders alpha
- renders pi
- renders theta
- renders sigma
- renders omega
- renders upper Gamma
- renders upper Sigma
- renders upper Omega
- renders subscript
- renders transpose
- renders sum
- renders integral
- renders sigmoid
- renders MSE loss
- renders softmax numerator
- renders layer norm
- renders SGD update
- renders cross entropy
- renders xavier init
- renders attention scores
- renders plain identifier
- renders greek alpha
- renders greek pi
- renders greek theta
- renders greek sigma
- renders greek omega
- renders greek lambda
- renders upper Gamma
- renders upper Delta
- renders upper Sigma
- renders upper Omega
- renders addition
- renders subtraction
- renders negation
- renders x^2
- renders x^3
- renders x^n
- renders simple frac
- renders nested frac
- renders sqrt
- renders sqrt of expression
- renders sum with Unicode sigma
- renders integral with Unicode symbol
- renders sigmoid
- renders layer norm
- renders SGD update with greek
- renders xavier init
- wraps in dollar signs
- renders frac in markdown
- renders greek in markdown
- renders complex DL equation
- renders sum binder
- renders triple-nested frac
- renders frac inside sqrt inside frac
- renders power of frac
- renders 2x
- renders 3(x + 1)
- renders attention formula
- renders batch norm
- renders KL divergence
- renders GELU approximation
- renders Adam optimizer update
- m{} and loss{} render same to_pretty
- m{} and loss{} render same LaTeX
- renders alpha * beta + gamma
- renders partial derivative notation
- renders nabla operator
- renders A[i][j]
- renders x[i]^2
- renders single number
- renders single identifier
- renders single greek letter
