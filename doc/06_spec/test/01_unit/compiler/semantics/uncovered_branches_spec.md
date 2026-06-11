# Uncovered Branches Specification

> 1. fn test long optional

<!-- sdn-diagram:id=uncovered_branches_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=uncovered_branches_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

uncovered_branches_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=uncovered_branches_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Uncovered Branches Specification

## Scenarios

### Type System - Optional Types

#### long optional type names

#### handles very long struct name as optional

1. fn test long optional
   - Expected: result == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct VeryLongStructNameThatExceedsTypicalBufferSizeForTesting:
    value: i64
    data: text
    flag: bool

fn test_long_optional() -> VeryLongStructNameThatExceedsTypicalBufferSizeForTesting?:
    nil

val result = test_long_optional()
expect(result == nil).to_equal(true)
```

</details>

#### works with nested long optional types

1. fn returns long optional
2. Some
   - Expected: x_val.inner equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct AnotherVeryLongStructNameForTestingNestedOptionalTypes:
    inner: i64

fn returns_long_optional() -> AnotherVeryLongStructNameForTestingNestedOptionalTypes?:
    Some(AnotherVeryLongStructNameForTestingNestedOptionalTypes(inner: 42))

val result = returns_long_optional()
if result != nil:
    val x_val = result.unwrap()
    expect(x_val.inner).to_equal(42)
```

</details>

#### function returning optional

#### handles function calls returning optional in if condition

1. fn maybe get
2. Some
3. fn maybe nil
   - Expected: x_result.unwrap() equals `42`
4. fail
   - Expected: called is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn maybe_get() -> i64?:
    Some(42)

fn maybe_nil() -> i64?:
    nil

val x_result = maybe_get()
if x_result != nil:
    expect(x_result.unwrap()).to_equal(42)

var called = false
val y_result = maybe_nil()
if y_result != nil:
    # Should not execute
    fail("maybe_nil returned a value")
else:
    called = true

expect(called).to_equal(true)
```

</details>

### Constant Expressions - Negative Numbers

#### negative integer constants

#### parses negative integer literals

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val neg_const = -42
expect(neg_const).to_equal(-42)
```

</details>

#### parses negative in arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [-1, -2, -3, -4, -5]
expect(arr.len()).to_equal(5)
expect(arr[0]).to_equal(-1)
expect(arr[4]).to_equal(-5)
```

</details>

#### negative float constants

#### parses negative float literals

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val neg_float = -3.14
expect(neg_float < 0.0).to_equal(true)
```

</details>

#### parses negative floats in arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val floats = [-1.5, -2.5, -3.5]
expect(floats.len()).to_equal(3)
```

</details>

### Array Types - Nested and Struct Arrays

#### nested arrays

#### handles 2D arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr2d = [[1, 2, 3], [4, 5, 6]]
expect(arr2d.len()).to_equal(2)
expect(arr2d[0].len()).to_equal(3)
expect(arr2d[1][2]).to_equal(6)
```

</details>

#### handles 3D arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr3d = [[[1]], [[2, 3]], [[4, 5, 6]]]
expect(arr3d.len()).to_equal(3)
expect(arr3d[2][0][2]).to_equal(6)
```

</details>

#### handles jagged arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val jagged = [[1], [2, 3], [4, 5, 6], [7, 8]]
expect(jagged.len()).to_equal(4)
expect(jagged[2].len()).to_equal(3)
```

</details>

#### arrays of optional types

#### creates array with mixed values and nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt_arr = [1, nil, 3, nil, 5]
expect(opt_arr.len()).to_equal(5)

var count = 0
for item in opt_arr:
    if item != nil:
        count = count + 1

expect(count).to_equal(3)
```

</details>

#### struct-like arrays

#### creates array of dicts simulating structs

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val points = [
    {"x": 0, "y": 0},
    {"x": 10, "y": 20},
    {"x": 30, "y": 40}
]

expect(points.len()).to_equal(3)
expect(points[1]["x"]).to_equal(10)
expect(points[2]["y"]).to_equal(40)
```

</details>

#### handles nested arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nested = [
    [1, 2],
    [3, 4]
]
expect(nested.len()).to_equal(2)
expect(nested[1][1]).to_equal(4)
```

</details>

### String Operations - Complex Cases

#### multiple string interpolations

#### handles multiple interpolations in one string

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 5
val y = 10
val result = x * y
val message = "x={x}, y={y}, result={result}"
expect(message).to_contain("x=5")
expect(message).to_contain("y=10")
expect(message).to_contain("result=50")
```

</details>

#### string concatenation chains

#### concatenates multiple strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val long_str = "a" + "b" + "c" + "d" + "e" + "f"
expect(long_str).to_equal("abcdef")
```

</details>

#### mixes interpolation and concatenation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42
val combined = "value: " + "{x}" + " done"
expect(combined).to_contain("42")
```

</details>

### Variable Declarations - Type Inference

#### whitespace handling

#### handles extra whitespace in declarations

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var    s    =    "hello"
expect(s).to_equal("hello")
```

</details>

#### handles text type inference

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text_var = "test"
expect(text_var).to_equal("test")
```

</details>

#### complex type annotations

<details>
<summary>Advanced: declares matrix with nested array types</summary>

#### declares matrix with nested array types

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matrix: [[i64]] = [[1, 2], [3, 4]]
expect(matrix[0][0]).to_equal(1)
expect(matrix[1][1]).to_equal(4)
```

</details>


</details>

#### declares array of arrays with explicit type

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bool_grid: [[bool]] = [[true, false], [false, true]]
expect(bool_grid[0][0]).to_equal(true)
expect(bool_grid[1][1]).to_equal(true)
```

</details>

### Control Flow - Complex Expressions

#### match expressions with multiple arms

#### matches optional values

1. fn check value
2. Some
   - Expected: check_value(Some(42)) equals `got 42`
   - Expected: check_value(nil) equals `nothing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn check_value(opt: i64?) -> text:
    match opt:
        Some(x): "got {x}"
        nil: "nothing"

expect(check_value(Some(42))).to_equal("got 42")
expect(check_value(nil)).to_equal("nothing")
```

</details>

#### lambda expressions

#### handles nested lambdas

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val add = \x: \y: x + y
val add5 = add(5)
expect(add5(10)).to_equal(15)
```

</details>

#### uses lambda in filter-like operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val numbers = [1, 2, 3, 4, 5]
val doubled = numbers.map(_1 * 2)
expect(doubled.len()).to_equal(5)
expect(doubled[0]).to_equal(2)
expect(doubled[4]).to_equal(10)
```

</details>

#### immediately invokes lambda

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = (\x: x * 2)(21)
expect(result).to_equal(42)
```

</details>

### Method Calls - Complex Arguments

#### string slice with expressions

#### uses expressions for slice bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello world"
val start = 1 + 1
val end = s.len() - 1
val sub = s[start..end]
expect(sub.len()).to_be_greater_than(0)
```

</details>

#### method chaining

#### chains replace operations

1. var step1 = s replace
2. var step2 = step1 replace


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello"
var step1 = s.replace("h", "H")
var step2 = step1.replace("e", "E")
expect(step2).to_start_with("H")
```

</details>

### Text Type - Explicit Annotations

#### text type declarations

#### declares text variable explicitly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s: text = "hello"
expect(s).to_equal("hello")
```

</details>

#### concatenates text types

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val greeting: text = "hello"
val name: text = "world"
val message = greeting + " " + name
expect(message).to_equal("hello world")
```

</details>

#### uses text methods

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s: text = "  hello  "
val trimmed = s.trim()
expect(trimmed).to_equal("hello")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/uncovered_branches_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Type System - Optional Types
- Constant Expressions - Negative Numbers
- Array Types - Nested and Struct Arrays
- String Operations - Complex Cases
- Variable Declarations - Type Inference
- Control Flow - Complex Expressions
- Method Calls - Complex Arguments
- Text Type - Explicit Annotations

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
