# Functions (Python-Inspired Sample)

> Tests compilation of function definitions inspired by Python patterns including default parameters, keyword arguments, and closures. Verifies that Python-like function idioms compile and execute correctly via the native backend.

<!-- sdn-diagram:id=functions_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=functions_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

functions_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=functions_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Functions (Python-Inspired Sample)

Tests compilation of function definitions inspired by Python patterns including default parameters, keyword arguments, and closures. Verifies that Python-like function idioms compile and execute correctly via the native backend.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | In Progress |
| Source | `test/03_system/feature/compiler/sample/python_inspired_sample/functions_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests compilation of function definitions inspired by Python patterns including
default parameters, keyword arguments, and closures. Verifies that Python-like
function idioms compile and execute correctly via the native backend.

## Scenarios

### Functions

#### basic functions

#### defines and calls simple function

1. fn add
2. expect add


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn add(a: i64, b: i64) -> i64:
    a + b
expect add(2, 3) == 5
```

</details>

#### uses implicit return

1. fn square
2. expect square


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn square(x: i64) -> i64:
    x * x
expect square(4) == 16
```

</details>

#### uses explicit return

1. fn early return
2. expect early return
3. expect early return


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn early_return(x: i64) -> i64:
    if x < 0:
        return 0
    x * 2
expect early_return(-5) == 0
expect early_return(5) == 10
```

</details>

#### default parameters

#### uses default when argument omitted

1. fn greet
2. expect greet


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn greet(name: text, greeting: text = "Hello") -> text:
    "{greeting}, {name}!"
expect greet("Alice") == "Hello, Alice!"
```

</details>

#### overrides default with explicit value

1. fn greet
2. expect greet


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn greet(name: text, greeting: text = "Hello") -> text:
    "{greeting}, {name}!"
expect greet("Bob", "Hi") == "Hi, Bob!"
```

</details>

#### named arguments

#### passes arguments by name

1. fn describe
2. expect describe


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn describe(name: text, age: i64) -> text:
    "{name} is {age} years old"
expect describe(name: "Alice", age: 30) == "Alice is 30 years old"
```

</details>

#### reorders with named arguments

1. fn describe
2. expect describe


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn describe(name: text, age: i64) -> text:
    "{name} is {age} years old"
expect describe(age: 25, name: "Bob") == "Bob is 25 years old"
```

</details>

#### higher-order functions

#### passes function as argument

1. fn apply
2. f
3. fn double
4. expect apply


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn apply(f: fn(i64) -> i64, x: i64) -> i64:
    f(x)
fn double(n: i64) -> i64:
    n * 2
expect apply(double, 5) == 10
```

</details>

#### uses lambda expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val numbers = [1, 2, 3, 4]
val doubled = numbers.map(_1 * 2)
expect doubled[0] == 2
expect doubled[3] == 8
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
