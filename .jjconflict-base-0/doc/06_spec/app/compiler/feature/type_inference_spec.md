# Type Inference Specification

**Feature ID:** #200-215 | **Category:** Language | **Difficulty:** 4/5 | **Status:** Implemented

_Source: `test/feature/usage/type_inference_spec.spl`_

---

## Overview

Type inference automatically deduces types for variables, function parameters,
and return values without explicit type annotations. Simple uses a Hindley-Milner
style type inference system with unification and occurs-check.

## Syntax

```simple
# Inferred from literal
val x = 42           # x: Int

# Inferred from usage
val arr = [1, 2, 3]  # arr: [Int]

# Inferred from return
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
# Basic inference
val x = 10           # Int
val y = 3.14         # Float
val name = "Alice"   # String
val flag = true      # Bool

# Function inference
fn add(a, b):
    a + b            # Inferred: fn(Int, Int) -> Int

# Generic inference
val numbers = [1, 2, 3]        # [Int]
val strings = ["a", "b", "c"]  # [String]
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 29 |

## Test Structure

### Type Inference - Literals

#### with integer literals

- ✅ infers and uses Int from literal
- ✅ infers Int from negative number
#### with float literals

- ✅ infers Float from decimal
#### with string literals

- ✅ infers String and uses string operations
#### with boolean literals

- ✅ infers Bool from true
- ✅ infers Bool from false
### Type Inference - Operators

#### with arithmetic operators

- ✅ infers types for addition
- ✅ infers types for multiplication
- ✅ infers types in complex expression
#### with comparison operators

- ✅ infers types for greater than
- ✅ infers types for equality
#### with logical operators

- ✅ infers Bool for and
- ✅ infers Bool for or
### Type Inference - Collections

#### with array literals

- ✅ infers array element type from integers
- ✅ infers array element type from strings
- ✅ supports operations on inferred array elements
### Type Inference - Control Flow

#### with if expressions

- ✅ infers Int from both branches
- ✅ infers String from both branches
- ✅ infers Bool from both branches
### Type Inference - Functions

#### with simple functions

- ✅ infers types from arithmetic operations
- ✅ infers types from comparison operations positive
- ✅ infers types from comparison operations negative
#### with multi-parameter functions

- ✅ infers types for binary operation
- ✅ infers types for mixed operations
### Type Inference - Variable Consistency

#### with let bindings

- ✅ maintains Int type through operations
- ✅ maintains String type through concatenation
### Type Inference - Complex Expressions

#### with nested expressions

- ✅ infers through nested arithmetic
- ✅ infers through nested comparisons
- ✅ infers through mixed operations

