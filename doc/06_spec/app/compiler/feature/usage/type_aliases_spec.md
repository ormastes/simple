# Type Aliases Specification

Type aliases allow creating alternative names for existing types, improving code readability and maintainability. They enable domain-specific naming without introducing new types, and support generic type aliases for parameterized type shortcuts.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TYPE-ALIAS-001 to #TYPE-ALIAS-012 |
| Category | Language |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/feature/usage/type_aliases_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Type aliases allow creating alternative names for existing types, improving
code readability and maintainability. They enable domain-specific naming
without introducing new types, and support generic type aliases for
parameterized type shortcuts.

## Syntax

```simple
type UserId = i64
type IntList = [i64]
type StringMap = {str: str}
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Type Alias | Alternative name for an existing type |
| Collection Alias | Alias for array or dict types |
| Alias Chain | Alias that references another alias |

## Behavior

- Type aliases are fully interchangeable with their target type
- Aliases can reference collection types
- Aliases do not create new types (unlike newtypes)
- Aliases can reference other aliases (chaining)

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/type_aliases/result.json` |

## Scenarios

- aliases primitive types
- allows alias in function signature
- is interchangeable with base type
- aliases array types
- aliases dict types
- allows nested collection aliases
- supports alias of alias
- supports multiple levels of aliasing
- uses alias in struct definition
- uses alias in class definition
- uses alias as return type
