# CLI Args Type Inference Specification

Tests type inference from default values in the `cli` keyword block. The compiler infers the type of each option from its default value: bool from true/false, text from string literals, i64 from integers, f64 from floats, and arrays from array literals.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CLI-002 |
| Category | Language \| CLI |
| Status | Draft |
| Source | `test/feature/usage/cli_args_types_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests type inference from default values in the `cli` keyword block.
The compiler infers the type of each option from its default value:
bool from true/false, text from string literals, i64 from integers,
f64 from floats, and arrays from array literals.

## Syntax

```simple
cli:
    flag: false           # inferred as bool
    name: "default"       # inferred as text
    count: 0              # inferred as i64
    rate: 0.5             # inferred as f64
    tags: ["a", "b"]      # inferred as [text]
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/cli_args_types/result.json` |

## Scenarios

- infers bool from false default
- infers bool from true default
- infers text from string default
- handles empty string default
- infers i64 from int default
- infers f64 from float default
- handles zero int default
- infers array from array default
- preserves type across parsing
- generates correct struct fields
