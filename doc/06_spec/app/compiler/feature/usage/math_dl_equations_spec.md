# Deep Learning Equation Tests for m{} Math Blocks

Tests that composite DL equations parse, evaluate correctly, render to LaTeX, and render to nvim-friendly Unicode. Covers all 27 DL equations found in `examples/simple_deeplearning_study/` and `src/lib/gc_async_mut/torch/`.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1090-1098 (DL equation coverage) |
| Category | Syntax / Math DSL |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/feature/usage/math_dl_equations_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 72 |
| Active scenarios | 72 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests that composite DL equations parse, evaluate correctly, render to LaTeX,
and render to nvim-friendly Unicode. Covers all 27 DL equations found in
`examples/simple_deeplearning_study/` and `src/lib/gc_async_mut/torch/`.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/math_dl_equations/result.json` |

## Scenarios

- evaluates sigmoid(2) correctly
- renders sigmoid LaTeX
- renders sigmoid Unicode
- evaluates tanh(1) correctly
- renders tanh LaTeX
- renders tanh Unicode
- evaluates relu(3) correctly
- evaluates relu(-2) correctly
- renders relu LaTeX
- renders relu Unicode
- evaluates gelu(1) correctly
- renders gelu LaTeX
- renders gelu Unicode
- evaluates softmax component
- renders softmax LaTeX
- renders softmax Unicode
- evaluates layer norm with concrete values
- renders layer norm LaTeX
- renders layer norm Unicode
- renders rms norm LaTeX
- renders rms norm Unicode
- evaluates dropout scaling
- renders dropout LaTeX
- renders dropout Unicode
- renders linear LaTeX
- renders linear Unicode
- renders embedding LaTeX with subscript
- renders embedding Unicode
- renders FFN LaTeX
- renders FFN Unicode
- renders attention LaTeX
- renders attention Unicode
- renders MHA LaTeX
- renders MHA Unicode
- renders transformer block LaTeX
- renders transformer block Unicode
- renders positional encoding LaTeX
- renders positional encoding Unicode
- renders cross-entropy LaTeX
- renders cross-entropy Unicode
- renders MSE LaTeX
- renders MSE Unicode
- evaluates temperature scaling
- renders temperature LaTeX
- renders temperature Unicode
- evaluates SGD update
- renders SGD LaTeX
- renders SGD Unicode
- evaluates SGD+momentum update
- renders SGD+momentum LaTeX
- renders SGD+momentum Unicode
- evaluates adam bias correction
- renders adam LaTeX
- renders adam Unicode
- renders gradient clip LaTeX
- renders gradient clip Unicode
- evaluates linear warmup
- renders warmup LaTeX
- renders warmup Unicode
- evaluates cosine decay at midpoint
- renders cosine decay LaTeX
- renders cosine decay Unicode
- evaluates cosine similarity of parallel vectors
- renders cosine similarity LaTeX
- renders cosine similarity Unicode
- evaluates accuracy at exact match
- evaluates accuracy with distance
- renders accuracy LaTeX
- renders accuracy Unicode
- evaluates xavier init
- renders xavier LaTeX
- renders xavier Unicode
