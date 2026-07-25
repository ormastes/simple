# Function Definitions Specification

> Tests for function definition and invocation.

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
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Function Definitions Specification

Tests for function definition and invocation.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1004 |
| Category | Language |
| Status | In Progress |
| Source | `test/03_system/feature/usage/functions_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for function definition and invocation.
Verifies function parameters, return types, implicit returns, and various calling patterns.

## Scenarios

### Function Definitions

#### basic function definition

#### defines function with explicit return type

1. fn add
2. expect add


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn add(a: i32, b: i32) -> i32:
    return a + b
expect add(2, 3) == 5
```

</details>

#### uses implicit return of last expression

1. fn multiply
2. expect multiply


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn multiply(a: i32, b: i32) -> i32:
    a * b
expect multiply(3, 4) == 12
```

</details>

#### calls function with no parameters

1. fn get greeting
2. expect get greeting


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn get_greeting() -> text:
    "Hello, World!"
expect get_greeting() == "Hello, World!"
```

</details>

#### function parameters

#### passes multiple parameters

1. fn combine
2. expect combine


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn combine(x: i32, y: i32, z: i32) -> i32:
    x + y + z
expect combine(1, 2, 3) == 6
```

</details>

#### uses type inference for parameters

1. fn double
2. expect double


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn double(x):
    x * 2
expect double(5) == 10
```

</details>

#### uses named arguments

1. fn create point
2. expect create point


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn create_point(x: i32, y: i32) -> text:
    "{x}, {y}"
expect create_point(x: 3, y: 4) == "3, 4"
```

</details>

#### function return types

#### returns single value

1. fn square
2. expect square


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn square(x: i32) -> i32:
    x * x
expect square(5) == 25
```

</details>

#### returns early with explicit return

1. fn get sign
2. expect get sign


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn get_sign(x: i32) -> text:
    if x < 0:
        return "negative"
    "positive"
expect get_sign(-5) == "negative"
```

</details>

#### returns without explicit type annotation

1. fn concat
2. expect concat


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn concat(a: text, b: text):
    a + b
expect concat("hello", "world") == "helloworld"
```

</details>

#### function with no return

#### executes function with side effects

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var counter = 0
counter = counter + 1
expect counter == 1
```

</details>

#### calls function multiple times

1. fn set value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn set_value(x: i32) -> i32:
    x
val result = set_value(42)
expect result == 42
```

</details>

#### higher-order functions

#### accepts function parameter

1. fn apply
2. f
3. fn double
4. expect apply


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn apply(f: fn(i32) -> i32, x: i32) -> i32:
    f(x)
fn double(n: i32) -> i32:
    n * 2
expect apply(double, 5) == 10
```

</details>

#### uses lambda function

1. fn apply
2. f
3. expect apply


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn apply(f: fn(i32) -> i32, x: i32) -> i32:
    f(x)
expect apply(\n: n + 10, 5) == 15
```

</details>

#### returns function

1. fn make adder
2. expect add five


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn make_adder(x: i32) -> fn(i32) -> i32:
    \y: x + y
val add_five = make_adder(5)
expect add_five(3) == 8
```

</details>

#### generic functions

#### defines generic function

1. fn identity<T>
2. expect identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn identity<T>(x: T) -> T:
    x
expect identity(42) == 42
```

</details>

#### uses generic with constraints

1. fn get first<T>


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn get_first<T>(items: List<T>) -> Option<T>:
    items.first
val result = get_first([1, 2, 3])
expect result == 1
```

</details>

#### uses multiple type parameters

1. fn pair<A, B>
2. expect pair


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn pair<A, B>(a: A, b: B) -> text:
    "pair"
expect pair(1, "hello") == "pair"
```

</details>

#### recursive functions

#### defines recursive factorial function

1. fn factorial
2. n * factorial
3. expect factorial


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn factorial(n: i32) -> i32:
    if n <= 1:
        1
    else:
        n * factorial(n - 1)
expect factorial(5) == 120
```

</details>

#### uses tail recursion

1. fn sum to
2. n + sum to
3. expect sum to


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn sum_to(n: i32) -> i32:
    if n <= 0:
        0
    else:
        n + sum_to(n - 1)
expect sum_to(10) == 55
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
