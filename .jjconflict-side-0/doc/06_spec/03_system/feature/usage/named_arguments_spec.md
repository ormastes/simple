# Named Arguments Specification

> Tests for named argument support allowing function calls with explicit parameter names, improving code clarity and enabling flexible argument ordering.

<!-- sdn-diagram:id=named_arguments_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=named_arguments_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

named_arguments_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=named_arguments_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Named Arguments Specification

Tests for named argument support allowing function calls with explicit parameter names, improving code clarity and enabling flexible argument ordering.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #NAMED-ARGS-001 |
| Category | Language \| Functions |
| Status | Implemented |
| Source | `test/03_system/feature/usage/named_arguments_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for named argument support allowing function calls with explicit
parameter names, improving code clarity and enabling flexible argument ordering.

## Syntax

```simple
fn create_user(name: text, email: text, age: i64) -> User:
User(name: name, email: email, age: age)

# Call with positional arguments
val user1 = create_user("Alice", "alice@example.com", 30)

# Call with named arguments
val user2 = create_user(age=25, name="Bob", email="bob@example.com")

# Mixed positional and named
val user3 = create_user("Charlie", email="charlie@example.com", age=35)
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Named Argument | Explicitly passing parameter by name |
| Positional Argument | Passing argument by position order |
| Argument Reordering | Non-positional order with named arguments |
| Default Values | Optional parameters with defaults |
| Clarity | Improved code readability with explicit parameter names |

## Behavior

- Named arguments can be passed in any order
- Positional arguments must precede named arguments (if mixed)
- Parameter names are part of the function signature
- Type checking applies to named arguments like positional
- Named arguments cannot be repeated in a single call
- Works with constructors and regular functions

## Scenarios

### Named Arguments Basic Usage

#### calls function with named arguments

1. fn greet
2. expect greet


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn greet(name, greeting):
    return 1
expect greet(name="world", greeting="hello") == 1
```

</details>

#### passes values correctly with named arguments

1. fn add
2. expect add


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn add(a, b):
    return a + b
expect add(a=10, b=20) == 30
```

</details>

#### works with string values

1. fn concat


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn concat(first, second):
    return first + second
val result = concat(first="Hello", second=" World")
var r = 0
if result == "Hello World":
    r = 1
expect r == 1
```

</details>

### Named Arguments Reordering

#### allows reversed argument order

1. fn sub
2. expect sub


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn sub(a, b):
    return a - b
expect sub(b=10, a=30) == 20
```

</details>

#### reorders three arguments

1. fn calc
2. expect calc


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn calc(x, y, z):
    return x + y * z
expect calc(z=4, x=2, y=3) == 14
```

</details>

#### reorders with different calculation

1. fn compute
2. expect compute


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn compute(first, second, third):
    return first * 100 + second * 10 + third
expect compute(third=3, first=1, second=2) == 123
```

</details>

### Mixed Positional and Named Arguments

#### mixes positional and named arguments

1. fn calc
2. expect calc


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn calc(x, y, z):
    return x + y * z
expect calc(2, z=4, y=3) == 14
```

</details>

#### uses positional first then named

1. fn process
2. expect process


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn process(a, b, c):
    return a * b + c
expect process(5, c=7, b=3) == 22
```

</details>

#### uses single positional with multiple named

1. fn combine
2. expect combine


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn combine(base, mult, add):
    return base * mult + add
expect combine(10, add=5, mult=2) == 25
```

</details>

### Named Arguments with Defaults

#### uses default when argument not provided

1. fn add
2. expect add


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn add(a, b=10):
    return a + b
expect add(5) == 15
```

</details>

#### overrides default with named argument

1. fn add
2. expect add


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn add(a, b=10):
    return a + b
expect add(5, b=20) == 25
```

</details>

#### works with multiple defaults

1. fn calculate
2. expect calculate
3. expect calculate
4. expect calculate


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn calculate(x, y=2, z=3):
    return x + y * z
expect calculate(1) == 7
expect calculate(1, y=5) == 16
expect calculate(1, z=10) == 21
```

</details>

### Named Arguments in Methods

#### uses named arguments with class methods

1. fn compute
2. expect calc compute


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Calculator:
    fn compute(self, a, b):
        return a * b

val calc = Calculator {}
expect calc.compute(a=6, b=7) == 42
```

</details>

#### reorders method arguments

1. fn subtract
2. expect m subtract


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Math:
    fn subtract(self, minuend, subtrahend):
        return minuend - subtrahend

val m = Math {}
expect m.subtract(subtrahend=15, minuend=50) == 35
```

</details>

### Named Arguments Edge Cases

#### handles single named argument

1. fn identity
2. expect identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn identity(x):
    return x
expect identity(x=42) == 42
```

</details>

#### handles many named arguments

1. fn sum5
2. expect sum5


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn sum5(a, b, c, d, e):
    return a + b + c + d + e
expect sum5(e=5, d=4, c=3, b=2, a=1) == 15
```

</details>

#### works with nested function calls

1. fn double
2. fn add
3. expect add


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn double(x):
    return x * 2
fn add(a, b):
    return a + b
expect add(a=double(x=5), b=double(x=3)) == 16
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
