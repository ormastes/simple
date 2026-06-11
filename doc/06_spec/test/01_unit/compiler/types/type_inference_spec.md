# Type Inference Unit Tests

> 1. check

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

# Type Inference Unit Tests

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #COMPILER-TYPES-001 |
| Category | Compiler \| Types |
| Status | Implemented |
| Source | `test/01_unit/compiler/types/type_inference_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### Integer Type Inference

#### infer i64 from integer literal

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42
check(x == 42)
```

</details>

#### infer i64 from negative literal

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = -5
check(x == -5)
```

</details>

#### infer i64 from zero

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0
check(x == 0)
```

</details>

#### infer i64 from large number

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 1000000
check(x == 1000000)
```

</details>

#### infer from arithmetic expression

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 3 + 4
check(x == 7)
```

</details>

### Float Type Inference

#### infer f64 from float literal

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 3.14
check(x > 3.0)
```

</details>

#### infer f64 from negative float

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = -2.5
check(x < 0.0)
```

</details>

#### infer f64 from float arithmetic

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 1.5 + 2.5
check(x > 3.9 and x < 4.1)
```

</details>

### Boolean Type Inference

#### infer bool from true

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = true
check(x)
```

</details>

#### infer bool from false

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = false
check(not x)
```

</details>

#### infer bool from comparison

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 5 > 3
check(x)
```

</details>

#### infer bool from logical

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = true and false
check(not x)
```

</details>

### String Type Inference

#### infer text from string literal

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = "hello"
check(x == "hello")
```

</details>

#### infer text from interpolation

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "world"
val x = "hello {name}"
check(x.contains("world"))
```

</details>

#### infer text from concatenation

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = "a" + "b"
check(x == "ab")
```

</details>

### Array Type Inference

#### infer array of i64

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3]
check(arr.len() == 3)
```

</details>

#### infer array of text

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = ["a", "b", "c"]
check(arr.len() == 3)
```

</details>

#### infer empty array

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [i64] = []
check(arr.len() == 0)
```

</details>

#### infer nested array

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [[1, 2], [3, 4]]
check(arr.len() == 2)
```

</details>

### Option Type Inference

#### infer Some variant

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = Some(42)
check(x.? == true)
```

</details>

#### infer nil

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = nil
check(x.?() == false)
```

</details>

#### infer from optional chaining

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = Some(42)
val y = x ?? 0
check(y == 42)
```

</details>

#### nil coalescing with default

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = nil
val y = x ?? 99
check(y == 99)
```

</details>

### Function Return Type Inference

#### infer return type from body

1. fn double
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn double(x: i64) -> i64:
    x * 2
check(double(21) == 42)
```

</details>

#### infer return type from if-else

1. fn sign
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn sign(x: i64) -> i64:
    if x > 0:
        1
    elif x < 0:
        -1
    else:
        0
check(sign(5) == 1)
check(sign(-3) == -1)
check(sign(0) == 0)
```

</details>

#### infer return type from match

1. fn describe num
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn describe_num(x: i64) -> text:
    match x:
        0: "zero"
        1: "one"
        _: "other"
check(describe_num(0) == "zero")
check(describe_num(1) == "one")
check(describe_num(99) == "other")
```

</details>

### Generic Type Inference

#### infer generic from usage

1. fn first
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn first(arr: [i64]) -> i64:
    arr[0]
check(first([10, 20]) == 10)
```

</details>

#### infer generic map result

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3]
val doubled = arr.map(_1 * 2)
check(doubled[0] == 2)
check(doubled[1] == 4)
```

</details>

#### infer generic filter result

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3, 4, 5]
val evens = arr.filter(_1 % 2 == 0)
check(evens.len() == 2)
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
