# Generic Runtime Specification

> 1. fn identity<T>

<!-- sdn-diagram:id=generic_runtime_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=generic_runtime_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

generic_runtime_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=generic_runtime_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Generic Runtime Specification

## Scenarios

### Runtime Generic Functions

#### specializes identity function with integers

1. fn identity<T>
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn identity<T>(x: T) -> T:
    x

val result = identity(42)
expect(result).to_equal(42)
```

</details>

#### specializes identity function with text

1. fn identity<T>
   - Expected: result equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn identity<T>(x: T) -> T:
    x

val result = identity("hello")
expect(result).to_equal("hello")
```

</details>

#### specializes identity function with floats

1. fn identity<T>
   - Expected: result equals `3.14`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn identity<T>(x: T) -> T:
    x

val result = identity(3.14)
expect(result).to_equal(3.14)
```

</details>

#### specializes identity function with booleans

1. fn identity<T>
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn identity<T>(x: T) -> T:
    x

val result = identity(true)
expect(result).to_equal(true)
```

</details>

#### caches specialized versions

1. fn identity<T>
   - Expected: result1 equals `10`
   - Expected: result2 equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn identity<T>(x: T) -> T:
    x

# First call creates specialization
val result1 = identity(10)
# Second call should use cached version
val result2 = identity(20)

expect(result1).to_equal(10)
expect(result2).to_equal(20)
```

</details>

#### creates separate specializations for different types

1. fn identity<T>
   - Expected: int_result equals `42`
   - Expected: text_result equals `world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn identity<T>(x: T) -> T:
    x

val int_result = identity(42)
val text_result = identity("world")

expect(int_result).to_equal(42)
expect(text_result).to_equal("world")
```

</details>

### Generic Functions with Multiple Type Parameters

#### handles two type parameters

1. fn pair<T, U>
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn pair<T, U>(first: T, second: U) -> T:
    first

val result = pair(42, "hello")
expect(result).to_equal(42)
```

</details>

#### handles three type parameters

1. fn pick first<A, B, C>
   - Expected: result equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn pick_first<A, B, C>(a: A, b: B, c: C) -> A:
    a

val result = pick_first(1, 2.5, "three")
expect(result).to_equal(1)
```

</details>

#### caches multi-param specializations independently

1. fn pair<T, U>
   - Expected: result1 equals `10`
   - Expected: result2 equals `10`
   - Expected: result3 equals `ten`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn pair<T, U>(first: T, second: U) -> T:
    first

val result1 = pair(10, 20)        # i64, i64
val result2 = pair(10, "twenty")  # i64, text
val result3 = pair("ten", 20)     # text, i64

expect(result1).to_equal(10)
expect(result2).to_equal(10)
expect(result3).to_equal("ten")
```

</details>

### Generic Functions with Complex Bodies

#### works with conditionals

1. fn safe div<T>
   - Expected: result1 equals `10`
   - Expected: result2 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn safe_div<T>(x: T, y: T) -> T:
    if y == 0:
        return 0
    x

val result1 = safe_div(10, 2)
val result2 = safe_div(10, 0)

expect(result1).to_equal(10)
expect(result2).to_equal(0)
```

</details>

<details>
<summary>Advanced: works with loops</summary>

#### works with loops

1. fn count<T>
   - Expected: result equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn count<T>(x: T, times: i64) -> i64:
    var counter: i64 = 0
    for i in 0..times:
        counter = counter + 1
    counter

val result = count(42, 5)
expect(result).to_equal(5)
```

</details>


</details>

#### works with multiple statements

1. fn process<T>
   - Expected: int_result equals `42`
   - Expected: text_result equals `test`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn process<T>(x: T) -> T:
    val temp = x
    val result = temp
    result

val int_result = process(42)
val text_result = process("test")

expect(int_result).to_equal(42)
expect(text_result).to_equal("test")
```

</details>

### Generic Function Edge Cases

#### handles nil values

1. fn passthrough<T>


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn passthrough<T>(x: T) -> T:
    x

val result = passthrough(nil)
expect(result).to_be_nil()
```

</details>

#### handles nested generic calls

1. fn outer<T>
2. fn inner<U>
3. inner
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn outer<T>(x: T) -> T:
    fn inner<U>(y: U) -> U:
        y
    inner(x)

val result = outer(42)
expect(result).to_equal(42)
```

</details>

#### handles arrays of different types

1. fn first elem<T>
2. arr len
   - Expected: int_arr_len equals `3`
   - Expected: text_arr_len equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn first_elem<T>(arr: [T]) -> i64:
    arr.len()

val int_arr_len = first_elem([1, 2, 3])
val text_arr_len = first_elem(["a", "b"])

expect(int_arr_len).to_equal(3)
expect(text_arr_len).to_equal(2)
```

</details>

#### handles empty parameter lists

1. fn constant<T>
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn constant<T>() -> i64:
    42

val result = constant()
expect(result).to_equal(42)
```

</details>

### Generic Struct Integration

#### works with generic struct construction

1. fn make pair<T>
   - Expected: int_pair[0] equals `1`
   - Expected: int_pair[1] equals `2`
   - Expected: text_pair[0] equals `a`
   - Expected: text_pair[1] equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn make_pair<T>(x: T, y: T) -> [T]:
    [x, y]

val int_pair = make_pair(1, 2)
val text_pair = make_pair("a", "b")

expect(int_pair[0]).to_equal(1)
expect(int_pair[1]).to_equal(2)
expect(text_pair[0]).to_equal("a")
expect(text_pair[1]).to_equal("b")
```

</details>

#### works with option-like patterns

1. fn wrap<T>
2. fn unwrap<T>
   - Expected: unwrapped equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn wrap<T>(x: T) -> [T]:
    [x]

fn unwrap<T>(arr: [T]) -> T:
    arr[0]

val wrapped = wrap(42)
val unwrapped = unwrap(wrapped)

expect(unwrapped).to_equal(42)
```

</details>

### Generic Function Type Inference

#### infers types from integer literals

1. fn double<T>
   - Expected: result equals `21`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn double<T>(x: T) -> T:
    x

val result = double(21)
expect(result).to_equal(21)
```

</details>

#### infers types from float literals

1. fn double<T>
   - Expected: result equals `2.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn double<T>(x: T) -> T:
    x

val result = double(2.5)
expect(result).to_equal(2.5)
```

</details>

#### infers types from string literals

1. fn double<T>
   - Expected: result equals `test`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn double<T>(x: T) -> T:
    x

val result = double("test")
expect(result).to_equal("test")
```

</details>

#### infers types from boolean literals

1. fn double<T>
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn double<T>(x: T) -> T:
    x

val result = double(false)
expect(result).to_equal(false)
```

</details>

#### infers types from variables

1. fn passthrough<T>
   - Expected: result equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn passthrough<T>(x: T) -> T:
    x

val my_var: i64 = 100
val result = passthrough(my_var)
expect(result).to_equal(100)
```

</details>

### Generic Cache Behavior

#### uses cache for repeated calls with same type

1. fn expensive<T>
   - Expected: r1 equals `1`
   - Expected: r2 equals `2`
   - Expected: r3 equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn expensive<T>(x: T) -> T:
    x

# All these should hit the same cached specialization
val r1 = expensive(1)
val r2 = expensive(2)
val r3 = expensive(3)

expect(r1).to_equal(1)
expect(r2).to_equal(2)
expect(r3).to_equal(3)
```

</details>

#### creates new cache entries for different types

1. fn identity<T>
   - Expected: int_val equals `42`
   - Expected: float_val equals `3.14`
   - Expected: text_val equals `hello`
   - Expected: bool_val is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn identity<T>(x: T) -> T:
    x

# Each type creates a new cache entry
val int_val = identity(42)
val float_val = identity(3.14)
val text_val = identity("hello")
val bool_val = identity(true)

expect(int_val).to_equal(42)
expect(float_val).to_equal(3.14)
expect(text_val).to_equal("hello")
expect(bool_val).to_equal(true)
```

</details>

#### handles interleaved calls to different generic functions

1. fn id1<T>
2. fn id2<T>
   - Expected: r1 equals `10`
   - Expected: r2 equals `20`
   - Expected: r3 equals `30`
   - Expected: r4 equals `40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn id1<T>(x: T) -> T:
    x

fn id2<T>(x: T) -> T:
    x

val r1 = id1(10)
val r2 = id2(20)
val r3 = id1(30)
val r4 = id2(40)

expect(r1).to_equal(10)
expect(r2).to_equal(20)
expect(r3).to_equal(30)
expect(r4).to_equal(40)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | Active |
| Source | `test/01_unit/runtime/generic_runtime_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Runtime Generic Functions
- Generic Functions with Multiple Type Parameters
- Generic Functions with Complex Bodies
- Generic Function Edge Cases
- Generic Struct Integration
- Generic Function Type Inference
- Generic Cache Behavior

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
