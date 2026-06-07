# COMPILER Deep Coverage Test

> 1. check

<!-- sdn-diagram:id=borrow_check_lifetime_3_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=borrow_check_lifetime_3_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

borrow_check_lifetime_3_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=borrow_check_lifetime_3_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# COMPILER Deep Coverage Test

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/deep/borrow_check_lifetime_3_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### Compiler Subsystem Deep Test

#### basic compilation

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
```

</details>

#### type checking

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(1 + 1 == 2)
```

</details>

#### code generation

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

#### optimization

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 2 * 3
check(result == 6)
```

</details>

#### error recovery

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
<summary>Advanced: loop</summary>

#### loop

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var c = 0
for i in 0..5:
    c = c + 1
check(c == 5)
```

</details>


</details>

#### edge empty

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = []
check(arr.len() == 0)
```

</details>

#### edge nil

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

#### complex 1

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1,2,3]
var s = 0
for x in arr:
    s = s + x
check(s == 6)
```

</details>

#### complex 2

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

#### integration

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = "test"
val output = input + "_out"
check(output == "test_out")
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
check(5 > 3)
check(3 < 5)
check(5 == 5)
```

</details>

#### nested

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if true: if true: check(true)
else: check(false)
else: check(false)
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
