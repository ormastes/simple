# CLI Args Inference Rules Specification

Tests the type inference rules and struct shape validation for the cli keyword. The compiler generates a typed struct from the cli block, where each field corresponds to an option. This tests that the generated struct has the correct shape, field names, and types.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CLI-008 |
| Category | Language \| CLI |
| Status | Draft |
| Source | `test/feature/usage/cli_args_inference_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests the type inference rules and struct shape validation for the cli keyword.
The compiler generates a typed struct from the cli block, where each field
corresponds to an option. This tests that the generated struct has the
correct shape, field names, and types.

## Syntax

```simple
cli:
    verbose: false
    output: "out.txt"
    count: 1
    rate: 0.5
    tags: ["a", "b"]

```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/cli_args_inference/result.json` |

## Scenarios

- infers bool from boolean literal
- infers text from string literal
- infers i64 from integer literal
- infers f64 from float literal
- generates struct with all fields
- preserves field order
