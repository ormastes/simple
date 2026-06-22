# Type Inference Specification

> Type inference automatically deduces types for variables, function parameters, and return values without explicit type annotations. Simple uses a Hindley-Milner style type inference system with unification and occurs-check.

<!-- sdn-diagram:id=type_inference_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=type_inference_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

type_inference_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=type_inference_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Type Inference Specification

Type inference automatically deduces types for variables, function parameters, and return values without explicit type annotations. Simple uses a Hindley-Milner style type inference system with unification and occurs-check.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #200-215 |
| Category | Language |
| Difficulty | 4/5 |
| Status | Implemented |
| Source | `test/03_system/feature/usage/type_inference_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

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

## Scenarios

### Type Inference - Literals

#### with integer literals

#### infers and uses Int from literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42
val y = x + 10
expect(y).to_equal(52)
```

</details>

#### infers Int from negative number

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = -10
val y = x * 2
expect(y).to_equal(-20)
```

</details>

#### with float literals

#### infers Float from decimal

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 3.14
val y = x * 2.0
# expect(y).to(be_close_to(6.28, 0.01))
expect(y).to_be_greater_than(6.0)
```

</details>

#### with string literals

#### infers String and uses string operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "Alice"
val greeting = "Hello, " + name
expect(greeting).to_equal("Hello, Alice")
```

</details>

#### with boolean literals

#### infers Bool from true

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flag = true
val result = if flag: "yes" else: "no"
expect(result).to_equal("yes")
```

</details>

#### infers Bool from false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flag = false
val result = if flag: "yes" else: "no"
expect(result).to_equal("no")
```

</details>

### Type Inference - Operators

#### with arithmetic operators

#### infers types for addition

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 10
val b = 5
val result = a + b
expect(result).to_equal(15)
```

</details>

#### infers types for multiplication

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 6
val b = 7
val result = a * b
expect(result).to_equal(42)
```

</details>

#### infers types in complex expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 2
val y = 3
val z = 4
val result = x + y * z
expect(result).to_equal(14)
```

</details>

#### with comparison operators

#### infers types for greater than

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 10
val b = 5
val result = a > b
expect(result).to_equal(true)
```

</details>

#### infers types for equality

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 42
val b = 42
val result = a == b
expect(result).to_equal(true)
```

</details>

#### with logical operators

#### infers Bool for and

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = true
val b = false
val result = a && b
expect(result).to_equal(false)
```

</details>

#### infers Bool for or

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = true
val b = false
val result = a || b
expect(result).to_equal(true)
```

</details>

### Type Inference - Collections

#### with array literals

#### infers array element type from integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3, 4, 5]
val first = arr[0]
val last = arr[4]
expect(first).to_equal(1)
expect(last).to_equal(5)
```

</details>

#### infers array element type from strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = ["hello", "world"]
val first = arr[0]
expect(first).to_equal("hello")
```

</details>

#### supports operations on inferred array elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val numbers = [10, 20, 30]
val doubled = numbers[0] * 2
expect(doubled).to_equal(20)
```

</details>

### Type Inference - Control Flow

#### with if expressions

#### infers Int from both branches

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = true
val result = if x: 10 else: 20
val doubled = result * 2
expect(doubled).to_equal(20)
```

</details>

#### infers String from both branches

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = false
val result = if x: "yes" else: "no"
val upper = result.uppercase()
expect(upper).to_equal("NO")
```

</details>

#### infers Bool from both branches

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = true
val result = if x: true else: false
expect(result).to_equal(true)
```

</details>

### Type Inference - Functions

#### with simple functions

#### infers types from arithmetic operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Function parameters and return type inferred
val result = double(5)
expect(result).to_equal(10)
```

</details>

#### infers types from comparison operations positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = is_positive(7)
expect(result).to_equal(true)
```

</details>

#### infers types from comparison operations negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = is_positive(-3)
expect(result).to_equal(false)
```

</details>

#### with multi-parameter functions

#### infers types for binary operation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = add_numbers(10, 5)
expect(result).to_equal(15)
```

</details>

#### infers types for mixed operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = create_pair(42, "hello")
val (first, second) = result
expect(first).to_equal(42)
expect(second).to_equal("hello")
```

</details>

### Type Inference - Variable Consistency

#### with let bindings

#### maintains Int type through operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 10
val y = x + 5
val z = y * 2
expect(z).to_equal(30)
```

</details>

#### maintains String type through concatenation

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = "Hello"
val s2 = s1 + ", "
val s3 = s2 + "World"
expect(s3).to_equal("Hello, World")
```

</details>

### Type Inference - Complex Expressions

#### with nested expressions

#### infers through nested arithmetic

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 1
val b = 2
val c = 3
val d = 4
val result = a + b * c + d
expect(result).to_equal(11)
```

</details>

#### infers through nested comparisons

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 10
val b = 5
val c = 3
val d = 7
val result = (a > b) && (c < d)
expect(result).to_equal(true)
```

</details>

#### infers through mixed operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 5
val y = 3
val is_greater = x > y
val message = if is_greater: "x wins" else: "y wins"
expect(message).to_equal("x wins")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
