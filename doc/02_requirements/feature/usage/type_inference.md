# Type Inference Specification
*Source:* `test/feature/usage/type_inference_spec.spl`
**Feature IDs:** #200-215  |  **Category:** Language  |  **Status:** Implemented

## Overview



use std.text.{NL}

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

## Feature: Type Inference - Literals

## Literal Type Inference

    The type checker infers types from literal values.
    Variables can be used without type annotations.

### Scenario: with integer literals

### Scenario: Integer Literal Inference

        Integer literals are inferred as Int type.
        Operations like arithmetic confirm correct inference.

| # | Example | Status |
|---|---------|--------|
| 1 | infers and uses Int from literal | pass |
| 2 | infers Int from negative number | pass |

**Example:** infers and uses Int from literal
    Given val x = 42
    Given val y = x + 10
    Then  expect(y).to_equal(52)

**Example:** infers Int from negative number
    Given val x = -10
    Given val y = x * 2
    Then  expect(y).to_equal(-20)

### Scenario: with float literals

### Scenario: Float Literal Inference

        Float literals are inferred as Float type.

| # | Example | Status |
|---|---------|--------|
| 1 | infers Float from decimal | pass |

**Example:** infers Float from decimal
    Given val x = 3.14
    Given val y = x * 2.0
    Then  expect(y).to_be_greater_than(6.0)

### Scenario: with string literals

### Scenario: String Literal Inference

        String literals are inferred as String type.

| # | Example | Status |
|---|---------|--------|
| 1 | infers String and uses string operations | pass |

**Example:** infers String and uses string operations
    Given val name = "Alice"
    Given val greeting = "Hello, " + name
    Then  expect(greeting).to_equal("Hello, Alice")

### Scenario: with boolean literals

### Scenario: Boolean Literal Inference

        Boolean literals are inferred as Bool type.

| # | Example | Status |
|---|---------|--------|
| 1 | infers Bool from true | pass |
| 2 | infers Bool from false | pass |

**Example:** infers Bool from true
    Given val flag = true
    Given val result = if flag: "yes" else: "no"
    Then  expect(result).to_equal("yes")

**Example:** infers Bool from false
    Given val flag = false
    Given val result = if flag: "yes" else: "no"
    Then  expect(result).to_equal("no")

## Feature: Type Inference - Operators

## Operator Type Inference

    Operators constrain operand types through unification.
    Type inference ensures operands have compatible types.

### Scenario: with arithmetic operators

### Scenario: Arithmetic Type Inference

        Arithmetic operators work with inferred numeric types.

| # | Example | Status |
|---|---------|--------|
| 1 | infers types for addition | pass |
| 2 | infers types for multiplication | pass |
| 3 | infers types in complex expression | pass |

**Example:** infers types for addition
    Given val a = 10
    Given val b = 5
    Given val result = a + b
    Then  expect(result).to_equal(15)

**Example:** infers types for multiplication
    Given val a = 6
    Given val b = 7
    Given val result = a * b
    Then  expect(result).to_equal(42)

**Example:** infers types in complex expression
    Given val x = 2
    Given val y = 3
    Given val z = 4
    Given val result = x + y * z
    Then  expect(result).to_equal(14)

### Scenario: with comparison operators

### Scenario: Comparison Type Inference

        Comparison operators return Bool with inferred operands.

| # | Example | Status |
|---|---------|--------|
| 1 | infers types for greater than | pass |
| 2 | infers types for equality | pass |

**Example:** infers types for greater than
    Given val a = 10
    Given val b = 5
    Given val result = a > b
    Then  expect(result).to_equal(true)

**Example:** infers types for equality
    Given val a = 42
    Given val b = 42
    Given val result = a == b
    Then  expect(result).to_equal(true)

### Scenario: with logical operators

### Scenario: Logical Operator Inference

        Logical operators work with inferred Bool types.

| # | Example | Status |
|---|---------|--------|
| 1 | infers Bool for and | pass |
| 2 | infers Bool for or | pass |

**Example:** infers Bool for and
    Given val a = true
    Given val b = false
    Given val result = a && b
    Then  expect(result).to_equal(false)

**Example:** infers Bool for or
    Given val a = true
    Given val b = false
    Given val result = a || b
    Then  expect(result).to_equal(true)

## Feature: Type Inference - Collections

## Collection Type Inference

    Collections infer element types from their contents.

### Scenario: with array literals

### Scenario: Array Element Type Inference

        Arrays infer element type from contents.
        All elements must have compatible types.

| # | Example | Status |
|---|---------|--------|
| 1 | infers array element type from integers | pass |
| 2 | infers array element type from strings | pass |
| 3 | supports operations on inferred array elements | pass |

**Example:** infers array element type from integers
    Given val arr = [1, 2, 3, 4, 5]
    Given val first = arr[0]
    Given val last = arr[4]
    Then  expect(first).to_equal(1)
    Then  expect(last).to_equal(5)

**Example:** infers array element type from strings
    Given val arr = ["hello", "world"]
    Given val first = arr[0]
    Then  expect(first).to_equal("hello")

**Example:** supports operations on inferred array elements
    Given val numbers = [10, 20, 30]
    Given val doubled = numbers[0] * 2
    Then  expect(doubled).to_equal(20)

## Feature: Type Inference - Control Flow

## Control Flow Type Inference

    Control flow expressions must have unified branch types.

### Scenario: with if expressions

### Scenario: If Expression Type Unification

        Both branches must have compatible inferred types.

| # | Example | Status |
|---|---------|--------|
| 1 | infers Int from both branches | pass |
| 2 | infers String from both branches | pass |
| 3 | infers Bool from both branches | pass |

**Example:** infers Int from both branches
    Given val x = true
    Given val result = if x: 10 else: 20
    Given val doubled = result * 2
    Then  expect(doubled).to_equal(20)

**Example:** infers String from both branches
    Given val x = false
    Given val result = if x: "yes" else: "no"
    Given val upper = result.uppercase()
    Then  expect(upper).to_equal("NO")

**Example:** infers Bool from both branches
    Given val x = true
    Given val result = if x: true else: false
    Then  expect(result).to_equal(true)

## Feature: Type Inference - Functions

## Function Type Inference

    Functions infer parameter and return types from usage.

### Scenario: with simple functions

### Scenario: Function Type Inference from Body

        Parameter types inferred from how they're used.
        Return type inferred from return expression.

| # | Example | Status |
|---|---------|--------|
| 1 | infers types from arithmetic operations | pass |
| 2 | infers types from comparison operations positive | pass |
| 3 | infers types from comparison operations negative | pass |

**Example:** infers types from arithmetic operations
    Given val result = double(5)
    Then  expect(result).to_equal(10)

**Example:** infers types from comparison operations positive
    Given val result = is_positive(7)
    Then  expect(result).to_equal(true)

**Example:** infers types from comparison operations negative
    Given val result = is_positive(-3)
    Then  expect(result).to_equal(false)

### Scenario: with multi-parameter functions

### Scenario: Multiple Parameter Inference

        Each parameter type inferred independently.

| # | Example | Status |
|---|---------|--------|
| 1 | infers types for binary operation | pass |
| 2 | infers types for mixed operations | pass |

**Example:** infers types for binary operation
    Given val result = add_numbers(10, 5)
    Then  expect(result).to_equal(15)

**Example:** infers types for mixed operations
    Given val result = create_pair(42, "hello")
    Given val (first, second) = result
    Then  expect(first).to_equal(42)
    Then  expect(second).to_equal("hello")

## Feature: Type Inference - Variable Consistency

## Variable Type Consistency

    Once a variable's type is inferred, it remains consistent.

### Scenario: with let bindings

### Scenario: Let Binding Type Persistence

        Variables maintain their inferred type.

| # | Example | Status |
|---|---------|--------|
| 1 | maintains Int type through operations | pass |
| 2 | maintains String type through concatenation | pass |

**Example:** maintains Int type through operations
    Given val x = 10
    Given val y = x + 5
    Given val z = y * 2
    Then  expect(z).to_equal(30)

**Example:** maintains String type through concatenation
    Given val s1 = "Hello"
    Given val s2 = s1 + ", "
    Given val s3 = s2 + "World"
    Then  expect(s3).to_equal("Hello, World")

## Feature: Type Inference - Complex Expressions

## Complex Expression Type Inference

    Type constraints propagate through nested expressions.

### Scenario: with nested expressions

### Scenario: Nested Expression Inference

        Types inferred through multiple levels of nesting.

| # | Example | Status |
|---|---------|--------|
| 1 | infers through nested arithmetic | pass |
| 2 | infers through nested comparisons | pass |
| 3 | infers through mixed operations | pass |

**Example:** infers through nested arithmetic
    Given val a = 1
    Given val b = 2
    Given val c = 3
    Given val d = 4
    Given val result = a + b * c + d
    Then  expect(result).to_equal(11)

**Example:** infers through nested comparisons
    Given val a = 10
    Given val b = 5
    Given val c = 3
    Given val d = 7
    Given val result = (a > b) && (c < d)
    Then  expect(result).to_equal(true)

**Example:** infers through mixed operations
    Given val x = 5
    Given val y = 3
    Given val is_greater = x > y
    Given val message = if is_greater: "x wins" else: "y wins"
    Then  expect(message).to_equal("x wins")


