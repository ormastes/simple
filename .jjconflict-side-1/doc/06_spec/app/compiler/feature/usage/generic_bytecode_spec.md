# Generic Template Bytecode in SMF

Tests storage of generic function templates in the SMF (Simple Module Format) bytecode format.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #GENERIC-001 |
| Category | Compiler |
| Status | In Progress |
| Source | `test/feature/usage/generic_bytecode_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests storage of generic function templates in the SMF (Simple Module Format)
bytecode format.

## Syntax

```simple
fn identity<T>(x: T) -> T: x
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/generic_bytecode/result.json` |

## Scenarios

- stores generic function templates in .smf
