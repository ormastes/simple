# Uncovered Branches Specification

> Tests covering Type System - Optional Types, Constant Expressions - Negative Numbers, Array Types - Nested and Struct Arrays, String Operations - Complex Cases, Variable Declarations - Type Inference, Control Flow - Complex Expressions, Method Calls - Complex Arguments, Text Type - Explicit Annotations.

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

- handles very long struct name as optional
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("handles very long struct name as optional")
struct VeryLongStructNameThatExceedsTypicalBufferSizeForTesting:
    value: i64
    data: text
    flag: bool

fn test_long_optional() -> VeryLongStructNameThatExceedsTypicalBufferSizeForTesting?:
    nil

val result = test_long_optional()
expect(result).to_equal(nil)
```

</details>

#### works with nested long optional types

- works with nested long optional types
   - Expected: x_val.inner equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("works with nested long optional types")
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

- handles function calls returning optional in if condition
   - Expected: x_result.unwrap() equals `42`
   - Expected: called is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("handles function calls returning optional in if condition")
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

- parses negative integer literals
   - Expected: neg_const equals `-42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("parses negative integer literals")
val neg_const = -42
expect(neg_const).to_equal(-42)
```

</details>

#### parses negative in arrays

- parses negative in arrays
   - Expected: arr.len() equals `5`
   - Expected: arr[0] equals `-1`
   - Expected: arr[4] equals `-5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("parses negative in arrays")
val arr = [-1, -2, -3, -4, -5]
expect(arr.len()).to_equal(5)
expect(arr[0]).to_equal(-1)
expect(arr[4]).to_equal(-5)
```

</details>

#### negative float constants

#### parses negative float literals

- parses negative float literals
   - Expected: neg_float < 0.0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("parses negative float literals")
val neg_float = -3.14
expect(neg_float < 0.0).to_equal(true)
```

</details>

#### parses negative floats in arrays

- parses negative floats in arrays
   - Expected: floats.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("parses negative floats in arrays")
val floats = [-1.5, -2.5, -3.5]
expect(floats.len()).to_equal(3)
```

</details>

### Array Types - Nested and Struct Arrays

#### nested arrays

#### handles 2D arrays

- handles 2D arrays
   - Expected: arr2d.len() equals `2`
   - Expected: arr2d[0].len() equals `3`
   - Expected: arr2d[1][2] equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("handles 2D arrays")
val arr2d = [[1, 2, 3], [4, 5, 6]]
expect(arr2d.len()).to_equal(2)
expect(arr2d[0].len()).to_equal(3)
expect(arr2d[1][2]).to_equal(6)
```

</details>

#### handles 3D arrays

- handles 3D arrays
   - Expected: arr3d.len() equals `3`
   - Expected: arr3d[2][0][2] equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("handles 3D arrays")
val arr3d = [[[1]], [[2, 3]], [[4, 5, 6]]]
expect(arr3d.len()).to_equal(3)
expect(arr3d[2][0][2]).to_equal(6)
```

</details>

#### handles jagged arrays

- handles jagged arrays
   - Expected: jagged.len() equals `4`
   - Expected: jagged[2].len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("handles jagged arrays")
val jagged = [[1], [2, 3], [4, 5, 6], [7, 8]]
expect(jagged.len()).to_equal(4)
expect(jagged[2].len()).to_equal(3)
```

</details>

#### arrays of optional types

#### creates array with mixed values and nil

- creates array with mixed values and nil
   - Expected: opt_arr.len() equals `5`
   - Expected: count equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates array with mixed values and nil")
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

- creates array of dicts simulating structs
   - Expected: points.len() equals `3`
   - Expected: points[1]["x"] equals `10`
   - Expected: points[2]["y"] equals `40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates array of dicts simulating structs")
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

- handles nested arrays
   - Expected: nested.len() equals `2`
   - Expected: nested[1][1] equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("handles nested arrays")
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

- handles multiple interpolations in one string


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("handles multiple interpolations in one string")
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

- concatenates multiple strings
   - Expected: long_str equals `abcdef`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("concatenates multiple strings")
val long_str = "a" + "b" + "c" + "d" + "e" + "f"
expect(long_str).to_equal("abcdef")
```

</details>

#### mixes interpolation and concatenation

- mixes interpolation and concatenation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("mixes interpolation and concatenation")
val x = 42
val combined = "value: " + "{x}" + " done"
expect(combined).to_contain("42")
```

</details>

### Variable Declarations - Type Inference

#### whitespace handling

#### handles extra whitespace in declarations

- handles extra whitespace in declarations
   - Expected: s equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("handles extra whitespace in declarations")
var    s    =    "hello"
expect(s).to_equal("hello")
```

</details>

#### handles text type inference

- handles text type inference
   - Expected: text_var equals `test`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("handles text type inference")
val text_var = "test"
expect(text_var).to_equal("test")
```

</details>

#### complex type annotations

<details>
<summary>Advanced: declares matrix with nested array types</summary>

#### declares matrix with nested array types

- declares matrix with nested array types
   - Expected: matrix[0][0] equals `1`
   - Expected: matrix[1][1] equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("declares matrix with nested array types")
val matrix: [[i64]] = [[1, 2], [3, 4]]
expect(matrix[0][0]).to_equal(1)
expect(matrix[1][1]).to_equal(4)
```

</details>


</details>

#### declares array of arrays with explicit type

- declares array of arrays with explicit type
   - Expected: bool_grid[0][0] is true
   - Expected: bool_grid[1][1] is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("declares array of arrays with explicit type")
val bool_grid: [[bool]] = [[true, false], [false, true]]
expect(bool_grid[0][0]).to_equal(true)
expect(bool_grid[1][1]).to_equal(true)
```

</details>

### Control Flow - Complex Expressions

#### match expressions with multiple arms

#### matches optional values

- matches optional values
   - Expected: check_value(Some(42)) equals `got 42`
   - Expected: check_value(nil) equals `nothing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("matches optional values")
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

- handles nested lambdas
   - Expected: add5(10) equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("handles nested lambdas")
val add = \x: \y: x + y
val add5 = add(5)
expect(add5(10)).to_equal(15)
```

</details>

#### uses lambda in filter-like operations

- uses lambda in filter-like operations
   - Expected: doubled.len() equals `5`
   - Expected: doubled[0] equals `2`
   - Expected: doubled[4] equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("uses lambda in filter-like operations")
val numbers = [1, 2, 3, 4, 5]
val doubled = numbers.map(_1 * 2)
expect(doubled.len()).to_equal(5)
expect(doubled[0]).to_equal(2)
expect(doubled[4]).to_equal(10)
```

</details>

#### immediately invokes lambda

- immediately invokes lambda
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("immediately invokes lambda")
val result = (\x: x * 2)(21)
expect(result).to_equal(42)
```

</details>

### Method Calls - Complex Arguments

#### string slice with expressions

#### uses expressions for slice bounds

- uses expressions for slice bounds


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("uses expressions for slice bounds")
val s = "hello world"
val start = 1 + 1
val end = s.len() - 1
val sub = s[start..end]
expect(sub.len()).to_be_greater_than(0)
```

</details>

#### method chaining

#### chains replace operations

- chains replace operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("chains replace operations")
val s = "hello"
val replaced = s.replace("h", "H")
val chained = replaced.replace("e", "E")
expect(chained).to_start_with("H")
```

</details>

### Text Type - Explicit Annotations

#### text type declarations

#### declares text variable explicitly

- declares text variable explicitly
   - Expected: s equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("declares text variable explicitly")
val s: text = "hello"
expect(s).to_equal("hello")
```

</details>

#### concatenates text types

- concatenates text types
   - Expected: message equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("concatenates text types")
val greeting: text = "hello"
val name: text = "world"
val message = greeting + " " + name
expect(message).to_equal("hello world")
```

</details>

#### uses text methods

- uses text methods
   - Expected: trimmed equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("uses text methods")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Type System - Optional Types, Constant Expressions - Negative Numbers, Array Types - Nested and Struct Arrays, String Operations - Complex Cases, Variable Declarations - Type Inference, Control Flow - Complex Expressions, Method Calls - Complex Arguments, Text Type - Explicit Annotations.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a9ee444de4253e6719c1850f1eb9916f323944ecda2da6c31b484da160de4b2f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a9ee444de4253e6719c1850f1eb9916f323944ecda2da6c31b484da160de4b2f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a9ee444de4253e6719c1850f1eb9916f323944ecda2da6c31b484da160de4b2f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/semantics/uncovered_branches_spec.spl
mirror: doc/06_spec/01_unit/compiler/semantics/uncovered_branches_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/semantics/uncovered_branches_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/semantics/uncovered_branches_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/semantics/uncovered_branches_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 28 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/semantics/uncovered_branches_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles very long struct name as optional' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/uncovered_branches_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'works with nested long optional types' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/uncovered_branches_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles function calls returning optional in if condition' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
