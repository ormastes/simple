# Type Inference Specification

Type inference automatically deduces types for variables, function parameters, and return values without explicit type annotations. Simple uses a Hindley-Milner style type inference system with unification and occurs-check.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #200-215 |
| Category | Language |
| Difficulty | 4/5 |
| Status | Implemented |
| Source | `test/feature/usage/type_inference_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Type inference automatically deduces types for variables, function parameters,
and return values without explicit type annotations. Simple uses a Hindley-Milner
style type inference system with unification and occurs-check.

## Syntax

```simple
val x = 42           # x: Int

val arr = [1, 2, 3]  # arr: [Int]

fn double(x):        # x: Int -> Int (inferred from usage)
x * 2
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Unification | Combines type constraints to find most general type |
| Type Variable | Placeholder type that gets resolved during inference |
| Occurs Check | Prevents infinite recursive types like `T = Array<T>` |
| Let-Polymorphism | Variables can have different types in different contexts |

## Behavior

- **Literals** infer primitive types (Int, Float, Bool, String, Nil)
- **Operations** propagate type constraints (e.g., `+` requires numbers)
- **Collections** infer element types from contents
- **Functions** infer parameter/return types from body and call sites
- **Generics** instantiate type parameters at call sites
- **Traits** resolve method types from trait definitions

## Related Specifications

- [Functions](../functions/functions_spec.md) - Function type signatures
- [Generics](../generics/generics_spec.md) - Generic type parameters
- [Traits](../traits/traits_spec.md) - Trait method resolution

## Implementation Notes

The type checker (`simple-type` crate) implements:
- Robinson's unification algorithm
- Fresh type variable generation
- Substitution-based type resolution
- Formal verification via Lean4 integration

Performance: Type inference is O(n) for most expressions, with unification
being nearly constant-time in practice.

## Examples

```simple
val x = 10           # Int
val y = 3.14         # Float
val name = "Alice"   # String
val flag = true      # Bool

fn add(a, b):
a + b            # Inferred: fn(Int, Int) -> Int

val numbers = [1, 2, 3]        # [Int]
val strings = ["a", "b", "c"]  # [String]
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/type_inference/result.json` |

## Scenarios

- infers and uses Int from literal
- infers Int from negative number
- infers Float from decimal
- infers String and uses string operations
- infers Bool from true
- infers Bool from false
- infers types for addition
- infers types for multiplication
- infers types in complex expression
- infers types for greater than
- infers types for equality
- infers Bool for and
- infers Bool for or
- infers array element type from integers
- infers array element type from strings
- supports operations on inferred array elements
- infers Int from both branches
- infers String from both branches
- infers Bool from both branches
- infers types from arithmetic operations
- infers types from comparison operations positive
- infers types from comparison operations negative
- infers types for binary operation
- infers types for mixed operations
- maintains Int type through operations
- maintains String type through concatenation
- infers through nested arithmetic
- infers through nested comparisons
- infers through mixed operations
