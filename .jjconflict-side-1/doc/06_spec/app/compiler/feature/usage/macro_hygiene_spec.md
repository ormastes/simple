# Macro Hygiene Specification

Tests for macro hygiene system that prevents variable capture through gensym renaming. Covers variable isolation, nested scopes, gensym uniqueness, and pattern matching with hygiene.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MACRO-001 |
| Category | Language \| Macros |
| Status | Implemented |
| Source | `test/feature/usage/macro_hygiene_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests for macro hygiene system that prevents variable capture through
gensym renaming. Covers variable isolation, nested scopes, gensym uniqueness,
and pattern matching with hygiene.

## Syntax

```simple
macro make_ten() -> (returns result: Int):
emit result:
val x = 10
x

val x = 5
val result = make_ten!()
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/macro_hygiene/result.json` |

## Scenarios

- prevents variable capture
- isolates macro internal variables
- preserves outer variable after macro
- handles nested scopes in macro
- handles nested macro calls
- handles nested blocks
- creates unique names across calls
- gensyms multiple variables
- isolates pattern variables
- isolates tuple destructuring
- isolates array destructuring
- isolates function parameters
- isolates function from outer scope
- handles nested functions
- handles complex multi-scope macro
- handles macro parameters
- handles nested macros with same names
- handles empty macro
- handles macro with early return
- handles variable shadowing
