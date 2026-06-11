# LIB Extended Coverage Test

> 1. check

<!-- sdn-diagram:id=execution_thread_unit_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=execution_thread_unit_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

execution_thread_unit_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=execution_thread_unit_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LIB Extended Coverage Test

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/extended/execution_thread_unit_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### LIB Extended Test

#### lib function 1

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
```

</details>

#### lib function 2

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(1 + 1 == 2)
```

</details>

#### lib function 3

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = [1,2,3]
check(x.len() == 3)
```

</details>

#### lib function 4

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = {"k": "v"}
check(d["k"] == "v")
```

</details>

#### error path 1

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var err = nil
check(err == nil)
```

</details>

#### error path 2

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = nil
check(not opt.?)
```

</details>

#### branch 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if true: check(true)
else: check(false)
```

</details>

#### branch 2

1. Some
2. nil: check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match Some(1):
    Some(x): check(x == 1)
    nil: check(false)
```

</details>

<details>
<summary>Advanced: loop 1</summary>

#### loop 1

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var c = 0
for i in 0..5: c = c + 1
check(c == 5)
```

</details>


</details>

<details>
<summary>Advanced: loop 2</summary>

#### loop 2

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = 0
for i in [1,2,3]: s = s + i
check(s == 6)
```

</details>


</details>

#### edge empty

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check([].len() == 0)
```

</details>

#### edge single

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check([1].len() == 1)
```

</details>

#### complex

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1,2,3,4,5]
var evens = []
for x in arr: if x % 2 == 0: evens = evens.append(x)
check(evens.len() == 2)
```

</details>

#### integration

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = "test"
val stage1 = input + "_1"
val stage2 = stage1 + "_2"
check(stage2 == "test_1_2")
```

</details>

#### validation

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(5 > 0)
check(-1 < 0)
check(0 == 0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
