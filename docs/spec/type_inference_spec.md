*Source: `simple/test/system/features/type_inference/type_inference_spec.spl`*
*Last Updated: 2026-01-16*

---

# Type Inference Specification

**Feature IDs:** #200-215
**Category:** Language
**Difficulty:** 4/5
**Status:** Implemented

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

## Literal Type Inference

    The type checker infers types from literal values.
    Variables can be used without type annotations.

### Scenario: Integer Literal Inference

        Integer literals are inferred as Int type.
        Operations like arithmetic confirm correct inference.

### Scenario: Float Literal Inference

        Float literals are inferred as Float type.

### Scenario: String Literal Inference

        String literals are inferred as String type.

### Scenario: Boolean Literal Inference

        Boolean literals are inferred as Bool type.

## Operator Type Inference

    Operators constrain operand types through unification.
    Type inference ensures operands have compatible types.

### Scenario: Arithmetic Type Inference

        Arithmetic operators work with inferred numeric types.

### Scenario: Comparison Type Inference

        Comparison operators return Bool with inferred operands.

### Scenario: Logical Operator Inference

        Logical operators work with inferred Bool types.

## Collection Type Inference

    Collections infer element types from their contents.

### Scenario: Array Element Type Inference

        Arrays infer element type from contents.
        All elements must have compatible types.

## Control Flow Type Inference

    Control flow expressions must have unified branch types.

### Scenario: If Expression Type Unification

        Both branches must have compatible inferred types.

## Function Type Inference

    Functions infer parameter and return types from usage.

### Scenario: Function Type Inference from Body

        Parameter types inferred from how they're used.
        Return type inferred from return expression.

### Scenario: Multiple Parameter Inference

        Each parameter type inferred independently.

## Variable Type Consistency

    Once a variable's type is inferred, it remains consistent.

### Scenario: Let Binding Type Persistence

        Variables maintain their inferred type.

## Complex Expression Type Inference

    Type constraints propagate through nested expressions.

### Scenario: Nested Expression Inference

        Types inferred through multiple levels of nesting.
