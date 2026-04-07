# Macros Specification

Tests for the macro system including macro definitions, expansions, hygiene, and integration with the compiler's metaprogramming capabilities.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TBD |
| Category | Language |
| Difficulty | 4/5 |
| Status | Planned |
| Source | `test/feature/usage/macros_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests for the macro system including macro definitions, expansions,
hygiene, and integration with the compiler's metaprogramming capabilities.

## Syntax

```simple
macro my_macro(param) -> Result:
quote:
val result = ~param * 2
result
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Macro Definition | Compile-time code template generation |
| Hygiene | Prevention of variable name collisions in macro expansion |
| Quote/Unquote | Syntax for code as data and interpolation |
| Expansion | Runtime substitution of macro calls with generated code |

## Behavior

- Macros execute at compile-time to generate code
- Proper hygiene ensures macro-generated variables don't shadow user code
- Supports nested macros and recursive expansion
- Quote-unquote syntax for metaprogramming
- Error handling during macro expansion

## Related Specifications

- Generators - Similar metaprogramming concepts
- Code Generation - Template expansion and code synthesis

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/macros/result.json` |

## Scenarios

- placeholder test
- placeholder test
- placeholder test
