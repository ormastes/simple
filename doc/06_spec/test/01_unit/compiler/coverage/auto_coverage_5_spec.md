# Auto-Generated Coverage Test

> 1. check

<!-- sdn-diagram:id=auto_coverage_5_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=auto_coverage_5_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

auto_coverage_5_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=auto_coverage_5_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Auto-Generated Coverage Test

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #AUTO |
| Category | Testing |
| Status | Implemented |
| Source | `test/01_unit/compiler/coverage/auto_coverage_5_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### Auto Coverage

#### test 1

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(1 == 1)
```

</details>

#### test 2

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check("a" == "a")
```

</details>

#### test 3

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 5
check(x > 0)
```

</details>

#### test 4

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = -1
check(x < 0)
```

</details>

#### test 5

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

#### test 6

1. fn run for
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run_for() -> i64:
    var sum = 0
    for i in 0..10:
        sum = sum + 1
    sum
check(run_for() == 10)
```

</details>

#### test 7

1. Some
2. nil: check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some(99)
match opt:
    Some(x): check(x == 99)
    nil: check(false)
```

</details>

#### test 8

1. Some
2. nil: check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = nil
match opt:
    Some(x): check(false)
    nil: check(true)
```

</details>

#### test 9

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello world"
check(s.len() == 11)
```

</details>

#### test 10

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if true:
    check(true)
else:
    check(false)
```

</details>

#### test 11

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if false:
    check(false)
else:
    check(true)
```

</details>

#### test 12

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 10
val b = 20
check(a < b)
```

</details>

#### test 13

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dict = {"key": "value"}
check(dict["key"] == "value")
```

</details>

#### test 14

1. fn run while
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run_while() -> i64:
    var count = 0
    while count < 5:
        count = count + 1
    count
check(run_while() == 5)
```

</details>

#### test 15

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 100
if x > 50:
    if x > 75:
        check(true)
    else:
        check(false)
else:
    check(false)
```

</details>

#### test 16

1. fn run sum
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run_sum() -> i64:
    val nums = [10, 20, 30, 40, 50]
    var total = 0
    for n in nums:
        total = total + n
    total
check(run_sum() == 150)
```

</details>

#### test 17

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42
val result = if x > 40: "big" else: "small"
check(result == "big")
```

</details>

#### test 18

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = []
check(items.len() == 0)
```

</details>

#### test 19

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = "hello"
val s2 = "world"
val combined = s1 + " " + s2
check(combined == "hello world")
```

</details>

#### test 20

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 10
val y = x * 2
check(y == 20)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
