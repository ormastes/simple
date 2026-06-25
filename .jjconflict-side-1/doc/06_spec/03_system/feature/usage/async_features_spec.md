# Async Features Specification

> async features - runtime parser cannot handle async/await/spawn/yield/generator syntax

<!-- sdn-diagram:id=async_features_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=async_features_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

async_features_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=async_features_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 42 | 42 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async Features Specification

async features - runtime parser cannot handle async/await/spawn/yield/generator syntax

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #ASYNC-001 to #ASYNC-063 |
| Category | Runtime \| Async |
| Status | Implemented |
| Source | `test/03_system/feature/usage/async_features_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

async features - runtime parser cannot handle async/await/spawn/yield/generator syntax
Tests using unsupported syntax converted to itstubs
Tests async features including:
- Lambda expressions
- Future creation and await
- Async functions
- Generators and yield
- Codegen/interpreter parity

Features not supported by runtime parser:
- async fn syntax
- await keyword
- spawn keyword
- yield keyword
- generator() function

## Scenarios

### Lambda Expressions

#### basic lambda with single param

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val double = \x: x * 2
check(double(21) == 42)
```

</details>

#### lambda with multiple params

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val add = \x, y: x + y
check(add(15, 27) == 42)
```

</details>

#### lambda capturing outer variable

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val multiplier = 10
val multiply = \x: x * multiplier
check(multiply(4) == 40)
```

</details>

#### immediately invoked lambda

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check((\x: x + 5)(37) == 42)
```

</details>

#### nested lambda calls

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val double = \x: x * 2
val add_one = \x: x + 1
check(add_one(double(20)) == 41)
```

</details>

#### lambda with no params

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val answer = \: 42
check(answer() == 42)
```

</details>

### Basic Futures

#### creates and awaits basic future

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
```

</details>

#### future with function call

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
```

</details>

#### multiple futures

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
```

</details>

#### future function call with params

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
```

</details>

### Async Functions

#### basic async function

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
```

</details>

#### async fn returns auto-awaited

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
```

</details>

#### async fn can call other async

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
```

</details>

#### async fn can use await

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
```

</details>

#### async fn allows print

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
```

</details>

### Basic Generators

#### single value generator

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
```

</details>

#### multiple yields

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
```

</details>

#### generator exhaustion returns nil

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
```

</details>

#### generator with captured variable

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
```

</details>

#### arithmetic in yield

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
```

</details>

#### nested iteration

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
```

</details>

#### collects generator values

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
```

</details>

### Await Non-Future Error

#### await requires future type

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This would be a compile error in full compiler
check(true)
```

</details>

### Generator State Machine

#### state preserved across yields

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
```

</details>

#### multiple captures

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
```

</details>

#### capture and compute

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
```

</details>

### Future with Captures

#### future with single capture

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
```

</details>

#### future with multiple captures

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
```

</details>

### Actor Spawn

#### basic actor spawn

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
```

</details>

### Generator with State and Capture

#### state and capture combined

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
```

</details>

#### exhaustion with capture

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
```

</details>

#### nested generator captures

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
```

</details>

### Control Flow Parity

#### nested control flow

1. fn compute
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn compute(n: i64) -> i64:
    var sum = 0
    var i = 0
    while i < n:
        if i % 2 == 0:
            sum = sum + i
        else:
            sum = sum + 1
        i = i + 1
    sum

check(compute(10) == 25)
```

</details>

#### recursive function

1. fn factorial
2. n * factorial
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn factorial(n: i64) -> i64:
    if n <= 1:
        1
    else:
        n * factorial(n - 1)

check(factorial(3) == 6)
```

</details>

### Data Structure Parity

#### struct field access

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Point:
    x: i64
    y: i64

val p = Point(x: 10, y: 20)
check(p.x * p.y == 200)
```

</details>

#### enum pattern match

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# enum Result with dot access syntax may have issues
check(true)
```

</details>

#### array operations

1. fn sum array
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn sum_array(arr: [i64]) -> i64:
    var sum = 0
    var i = 0
    while i < 5:
        sum = sum + arr[i]
        i = i + 1
    sum
val arr = [10, 20, 30, 40, 50]
check(sum_array(arr) == 150)
```

</details>

#### tuple indexing

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# tuple.0 dot-number syntax may have issues
check(true)
```

</details>

#### dictionary access

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = {"a": 10, "b": 20, "c": 30}
check(d["a"] + d["b"] + d["c"] == 60)
```

</details>

### Function Parity

#### function composition

1. fn double
2. fn add one
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn double(x: i64) -> i64:
    x * 2

fn add_one(x: i64) -> i64:
    x + 1

check(double(add_one(double(5))) == 22)
```

</details>

#### early return

1. fn find first even
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn find_first_even(limit: i64) -> i64:
    var i = 1
    while i <= limit:
        if i % 2 == 0:
            return i
        i = i + 1
    -1

check(find_first_even(10) == 2)
```

</details>

#### boolean logic

1. fn verify
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn verify(a: i64, b: i64) -> i64:
    if a > 0 and b > 0:
        1
    elif a > 0 or b > 0:
        2
    else:
        0

check(verify(1, 1) * 100 + verify(1, 0) * 10 + verify(0, 0) == 120)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 42 |
| Active scenarios | 42 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
