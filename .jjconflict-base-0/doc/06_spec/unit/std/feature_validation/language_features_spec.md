# Language Features Specification

> Tests covering Feature #15 - Variables, Feature #24 - Closures, Feature #2 - Parser.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 52 | 52 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Language Features Specification

## Scenarios

### Feature #15 - Variables

#### val declarations (immutable)

#### declares immutable integer

- declares immutable integer
   - Expected: x equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares immutable integer")
val x = 42
expect(x).to_equal(42)
```

</details>

#### declares immutable string

- declares immutable string
   - Expected: name equals `Alice`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares immutable string")
val name = "Alice"
expect(name).to_equal("Alice")
```

</details>

#### declares immutable boolean

- declares immutable boolean
   - Expected: flag is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares immutable boolean")
val flag = true
expect(flag).to_equal(true)
```

</details>

#### declares immutable array

- declares immutable array
   - Expected: items.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares immutable array")
val items = [1, 2, 3]
expect(items.len()).to_equal(3)
```

</details>

#### declares immutable with expression

- declares immutable with expression
   - Expected: result equals `14`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares immutable with expression")
val result = 2 + 3 * 4
expect(result).to_equal(14)
```

</details>

#### var declarations (mutable)

#### declares mutable integer

- declares mutable integer
   - Expected: count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares mutable integer")
var count = 0
count = count + 1
expect(count).to_equal(1)
```

</details>

#### allows reassignment

- allows reassignment
   - Expected: value equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows reassignment")
var value = 10
value = 20
expect(value).to_equal(20)
```

</details>

<details>
<summary>Advanced: supports mutation in loops</summary>

#### supports mutation in loops

- supports mutation in loops
   - Expected: total equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports mutation in loops")
var total = 0
for i in [1, 2, 3, 4, 5]:
    total = total + i
expect(total).to_equal(15)
```

</details>


</details>

#### supports mutable string

- supports mutable string
   - Expected: msg equals `world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports mutable string")
var msg = "hello"
msg = "world"
expect(msg).to_equal("world")
```

</details>

#### let declarations

#### declares immutable binding with let

- declares immutable binding with let
   - Expected: x equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares immutable binding with let")
let x = 100
expect(x).to_equal(100)
```

</details>

#### declares let with string

- declares let with string
   - Expected: greeting equals `hi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares let with string")
let greeting = "hi"
expect(greeting).to_equal("hi")
```

</details>

#### type inference

#### infers integer type

- infers integer type
   - Expected: x equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infers integer type")
val x = 42
expect(x).to_equal(42)
```

</details>

#### infers string type

- infers string type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infers string type")
val s = "hello"
expect(s).to_start_with("h")
```

</details>

#### infers boolean type

- infers boolean type
   - Expected: b is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infers boolean type")
val b = true
expect(b).to_equal(true)
```

</details>

#### infers from expressions

- infers from expressions
   - Expected: sum equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infers from expressions")
val sum = 1 + 2
expect(sum).to_equal(3)
```

</details>

### Feature #24 - Closures

#### lambda syntax

#### creates simple lambda

- creates simple lambda
   - Expected: double(5) equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates simple lambda")
val double = _1 * 2
expect(double(5)).to_equal(10)
```

</details>

#### creates lambda with two parameters

- creates lambda with two parameters
   - Expected: add(3, 4) equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates lambda with two parameters")
val add = \a, b: a + b
expect(add(3, 4)).to_equal(7)
```

</details>

#### creates identity lambda

- creates identity lambda
   - Expected: id(42) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates identity lambda")
val id = \x: x
expect(id(42)).to_equal(42)
```

</details>

#### lambda with higher-order functions

#### uses lambda with map

- uses lambda with map
   - Expected: doubled equals `[2, 4, 6]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses lambda with map")
val numbers = [1, 2, 3]
val doubled = numbers.map(_ * 2)
expect(doubled).to_equal([2, 4, 6])
```

</details>

#### uses lambda with filter

- uses lambda with filter
   - Expected: evens equals `[2, 4, 6]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses lambda with filter")
val numbers = [1, 2, 3, 4, 5, 6]
val evens = numbers.filter(_ % 2 == 0)
expect(evens).to_equal([2, 4, 6])
```

</details>

#### closure capture (read-only)

#### captures outer variable

- captures outer variable
   - Expected: multiply(5) equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("captures outer variable")
val factor = 3
val multiply = _1 * factor
expect(multiply(5)).to_equal(15)
```

</details>

#### captures multiple outer variables

- captures multiple outer variables
   - Expected: compute(1) equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("captures multiple outer variables")
val base = 10
val offset = 5
val compute = _1 + base + offset
expect(compute(1)).to_equal(16)
```

</details>

#### captures string variable

- captures string variable
   - Expected: greet("World") equals `Hello, World!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("captures string variable")
val prefix = "Hello"
val greet = \name: "{prefix}, {name}!"
expect(greet("World")).to_equal("Hello, World!")
```

</details>

#### lambdas as values

#### stores lambda in val

- stores lambda in val
   - Expected: fn_val() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores lambda in val")
val fn_val = \: 42
expect(fn_val()).to_equal(42)
```

</details>

#### passes lambda to function

- passes lambda to function
   - Expected: result equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes lambda to function")
fn apply(f, x):
    f(x)
val result = apply(_1 * 10, 5)
expect(result).to_equal(50)
```

</details>

### Feature #2 - Parser

#### arithmetic expressions

#### parses addition

- parses addition
   - Expected: 1 + 2 equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses addition")
expect(1 + 2).to_equal(3)
```

</details>

#### parses subtraction

- parses subtraction
   - Expected: 10 - 3 equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses subtraction")
expect(10 - 3).to_equal(7)
```

</details>

#### parses multiplication

- parses multiplication
   - Expected: 4 * 5 equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses multiplication")
expect(4 * 5).to_equal(20)
```

</details>

#### parses division

- parses division
   - Expected: 10 / 2 equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses division")
expect(10 / 2).to_equal(5)
```

</details>

#### parses modulo

- parses modulo
   - Expected: 10 % 3 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses modulo")
expect(10 % 3).to_equal(1)
```

</details>

#### parses operator precedence

- parses operator precedence
   - Expected: 2 + 3 * 4 equals `14`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses operator precedence")
# Multiplication before addition
expect(2 + 3 * 4).to_equal(14)
```

</details>

#### parses parenthesized expressions

- parses parenthesized expressions
   - Expected: (2 + 3) * 4 equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses parenthesized expressions")
expect((2 + 3) * 4).to_equal(20)
```

</details>

#### comparison expressions

#### parses equality

- parses equality
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses equality")
expect(1).to_equal(1)
```

</details>

#### parses inequality

- parses inequality
   - Expected: 1 != 2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses inequality")
expect(1 != 2).to_equal(true)
```

</details>

#### parses less than

- parses less than
   - Expected: 1 < 2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses less than")
expect(1 < 2).to_equal(true)
```

</details>

#### parses greater than

- parses greater than
   - Expected: 2 > 1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses greater than")
expect(2 > 1).to_equal(true)
```

</details>

#### parses less than or equal

- parses less than or equal
   - Expected: 1 <= 1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses less than or equal")
expect(1 <= 1).to_equal(true)
```

</details>

#### parses greater than or equal

- parses greater than or equal
   - Expected: 2 >= 2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses greater than or equal")
expect(2 >= 2).to_equal(true)
```

</details>

#### logical expressions

#### parses and

- parses and
   - Expected: true and true is true
   - Expected: true and false is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses and")
expect(true and true).to_equal(true)
expect(true and false).to_equal(false)
```

</details>

#### parses or

- parses or
   - Expected: false or true is true
   - Expected: false or false is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses or")
expect(false or true).to_equal(true)
expect(false or false).to_equal(false)
```

</details>

#### parses not

- parses not
   - Expected: not false is true
   - Expected: not true is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses not")
expect(not false).to_equal(true)
expect(not true).to_equal(false)
```

</details>

#### string expressions

#### parses string literals

- parses string literals
   - Expected: s equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses string literals")
val s = "hello"
expect(s).to_equal("hello")
```

</details>

#### parses string interpolation

- parses string interpolation
   - Expected: msg equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses string interpolation")
val name = "world"
val msg = "hello {name}"
expect(msg).to_equal("hello world")
```

</details>

#### parses string concatenation

- parses string concatenation
   - Expected: a + b equals `foobar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses string concatenation")
val a = "foo"
val b = "bar"
expect(a + b).to_equal("foobar")
```

</details>

#### control flow parsing

#### parses if/else

- parses if/else
   - Expected: result equals `yes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses if/else")
val result = if true: "yes" else: "no"
expect(result).to_equal("yes")
```

</details>

<details>
<summary>Advanced: parses for loop</summary>

#### parses for loop

- parses for loop
   - Expected: sum equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses for loop")
var sum = 0
for i in [1, 2, 3]:
    sum = sum + i
expect(sum).to_equal(6)
```

</details>


</details>

<details>
<summary>Advanced: parses while loop</summary>

#### parses while loop

- parses while loop
   - Expected: run_while_loop() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses while loop")
fn run_while_loop() -> i64:
    var count = 0
    while count < 3:
        count = count + 1
    count
expect(run_while_loop()).to_equal(3)
```

</details>


</details>

#### function definitions

#### parses function with return value

- parses function with return value
   - Expected: square(5) equals `25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses function with return value")
fn square(x):
    x * x
expect(square(5)).to_equal(25)
```

</details>

#### parses function with multiple parameters

- parses function with multiple parameters
   - Expected: add_three(1, 2, 3) equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses function with multiple parameters")
fn add_three(a, b, c):
    a + b + c
expect(add_three(1, 2, 3)).to_equal(6)
```

</details>

#### collection literals

#### parses array literals

- parses array literals
   - Expected: arr.len() equals `3`
   - Expected: arr[0] equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses array literals")
val arr = [10, 20, 30]
expect(arr.len()).to_equal(3)
expect(arr[0]).to_equal(10)
```

</details>

#### parses empty array

- parses empty array
   - Expected: empty.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses empty array")
val empty = []
expect(empty.len()).to_equal(0)
```

</details>

#### parses dictionary literals

- parses dictionary literals
   - Expected: dict["key"] equals `value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses dictionary literals")
val dict = {"key": "value"}
expect(dict["key"]).to_equal("value")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/std/feature_validation/language_features_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Feature #15 - Variables, Feature #24 - Closures, Feature #2 - Parser.
- Feature #15 - Variables
- Feature #24 - Closures
- Feature #2 - Parser

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 52 |
| Active scenarios | 52 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `123038bafbe40e5ee86a8e2aa77746e4724238753f97e28d611ebbe2af878396`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `123038bafbe40e5ee86a8e2aa77746e4724238753f97e28d611ebbe2af878396`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `123038bafbe40e5ee86a8e2aa77746e4724238753f97e28d611ebbe2af878396`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/std/feature_validation/language_features_spec.spl
mirror: doc/06_spec/unit/std/feature_validation/language_features_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/std/feature_validation/language_features_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/std/feature_validation/language_features_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/std/feature_validation/language_features_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 31 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/std/feature_validation/language_features_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declares immutable integer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/std/feature_validation/language_features_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declares immutable string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/std/feature_validation/language_features_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declares immutable boolean' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
