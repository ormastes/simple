# Language Features Validation

> Validates core language features including variable declarations (val/var/let), lambda syntax and closure capture, and parser functionality basics.

<!-- sdn-diagram:id=language_features_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=language_features_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

language_features_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=language_features_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 52 | 52 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Language Features Validation

Validates core language features including variable declarations (val/var/let), lambda syntax and closure capture, and parser functionality basics.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #15 Variables, #24 Closures, #2 Parser |
| Category | Language |
| Status | Complete |
| Source | `test/01_unit/lib/common/feature_validation/language_features_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates core language features including variable declarations (val/var/let),
lambda syntax and closure capture, and parser functionality basics.

## Scenarios

### Feature #15 - Variables

#### val declarations (immutable)

#### declares immutable integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42
expect(x).to_equal(42)
```

</details>

#### declares immutable string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "Alice"
expect(name).to_equal("Alice")
```

</details>

#### declares immutable boolean

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flag = true
expect(flag).to_equal(true)
```

</details>

#### declares immutable array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = [1, 2, 3]
expect(items.len()).to_equal(3)
```

</details>

#### declares immutable with expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 2 + 3 * 4
expect(result).to_equal(14)
```

</details>

#### var declarations (mutable)

#### declares mutable integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = 0
count = count + 1
expect(count).to_equal(1)
```

</details>

#### allows reassignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var value = 10
value = 20
expect(value).to_equal(20)
```

</details>

<details>
<summary>Advanced: supports mutation in loops</summary>

#### supports mutation in loops

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var total = 0
for i in [1, 2, 3, 4, 5]:
    total = total + i
expect(total).to_equal(15)
```

</details>


</details>

#### supports mutable string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var msg = "hello"
msg = "world"
expect(msg).to_equal("world")
```

</details>

#### let declarations

#### declares immutable binding with let

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
let x = 100
expect(x).to_equal(100)
```

</details>

#### declares let with string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
let greeting = "hi"
expect(greeting).to_equal("hi")
```

</details>

#### type inference

#### infers integer type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42
expect(x).to_equal(42)
```

</details>

#### infers string type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello"
expect(s).to_start_with("h")
```

</details>

#### infers boolean type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = true
expect(b).to_equal(true)
```

</details>

#### infers from expressions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sum = 1 + 2
expect(sum).to_equal(3)
```

</details>

### Feature #24 - Closures

#### lambda syntax

#### creates simple lambda

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val double = \x: x * 2
expect(double(5)).to_equal(10)
```

</details>

#### creates lambda with two parameters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val add = \a, b: a + b
expect(add(3, 4)).to_equal(7)
```

</details>

#### creates identity lambda

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val id = \x: x
expect(id(42)).to_equal(42)
```

</details>

#### lambda with higher-order functions

#### uses lambda with map

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val numbers = [1, 2, 3]
val doubled = numbers.map(_ * 2)
expect(doubled).to_equal([2, 4, 6])
```

</details>

#### uses lambda with filter

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val numbers = [1, 2, 3, 4, 5, 6]
val evens = numbers.filter(_ % 2 == 0)
expect(evens).to_equal([2, 4, 6])
```

</details>

#### closure capture (read-only)

#### captures outer variable

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val factor = 3
val multiply = \x: x * factor
expect(multiply(5)).to_equal(15)
```

</details>

#### captures multiple outer variables

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = 10
val offset = 5
val compute = \x: x + base + offset
expect(compute(1)).to_equal(16)
```

</details>

#### captures string variable

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prefix = "Hello"
val greet = \name: "{prefix}, {name}!"
expect(greet("World")).to_equal("Hello, World!")
```

</details>

#### lambdas as values

#### stores lambda in val

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_val = \: 42
expect(fn_val()).to_equal(42)
```

</details>

#### passes lambda to function

- fn apply
- f
   - Expected: result equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn apply(f, x):
    f(x)
val result = apply(\x: x * 10, 5)
expect(result).to_equal(50)
```

</details>

### Feature #2 - Parser

#### arithmetic expressions

#### parses addition

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(1 + 2).to_equal(3)
```

</details>

#### parses subtraction

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(10 - 3).to_equal(7)
```

</details>

#### parses multiplication

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(4 * 5).to_equal(20)
```

</details>

#### parses division

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(10 / 2).to_equal(5)
```

</details>

#### parses modulo

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(10 % 3).to_equal(1)
```

</details>

#### parses operator precedence

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Multiplication before addition
expect(2 + 3 * 4).to_equal(14)
```

</details>

#### parses parenthesized expressions

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect((2 + 3) * 4).to_equal(20)
```

</details>

#### comparison expressions

#### parses equality

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(1 == 1).to_equal(true)
```

</details>

#### parses inequality

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(1 != 2).to_equal(true)
```

</details>

#### parses less than

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(1 < 2).to_equal(true)
```

</details>

#### parses greater than

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(2 > 1).to_equal(true)
```

</details>

#### parses less than or equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(1 <= 1).to_equal(true)
```

</details>

#### parses greater than or equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(2 >= 2).to_equal(true)
```

</details>

#### logical expressions

#### parses and

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(true and true).to_equal(true)
expect(true and false).to_equal(false)
```

</details>

#### parses or

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(false or true).to_equal(true)
expect(false or false).to_equal(false)
```

</details>

#### parses not

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(not false).to_equal(true)
expect(not true).to_equal(false)
```

</details>

#### string expressions

#### parses string literals

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello"
expect(s).to_equal("hello")
```

</details>

#### parses string interpolation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "world"
val msg = "hello {name}"
expect(msg).to_equal("hello world")
```

</details>

#### parses string concatenation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = "foo"
val b = "bar"
expect(a + b).to_equal("foobar")
```

</details>

#### control flow parsing

#### parses if/else

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = if true: "yes" else: "no"
expect(result).to_equal("yes")
```

</details>

<details>
<summary>Advanced: parses for loop</summary>

#### parses for loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- fn run while loop
   - Expected: run_while_loop() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- fn square
   - Expected: square(5) equals `25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn square(x):
    x * x
expect(square(5)).to_equal(25)
```

</details>

#### parses function with multiple parameters

- fn add three
   - Expected: add_three(1, 2, 3) equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn add_three(a, b, c):
    a + b + c
expect(add_three(1, 2, 3)).to_equal(6)
```

</details>

#### collection literals

#### parses array literals

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [10, 20, 30]
expect(arr.len()).to_equal(3)
expect(arr[0]).to_equal(10)
```

</details>

#### parses empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty = []
expect(empty.len()).to_equal(0)
```

</details>

#### parses dictionary literals

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dict = {"key": "value"}
expect(dict["key"]).to_equal("value")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 52 |
| Active scenarios | 52 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
