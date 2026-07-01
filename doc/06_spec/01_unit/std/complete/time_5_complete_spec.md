# STDLIB Module Complete Test

> 1. verify

<!-- sdn-diagram:id=time_5_complete_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=time_5_complete_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

time_5_complete_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=time_5_complete_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# STDLIB Module Complete Test

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/complete/time_5_complete_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### STDLIB Complete Coverage

#### public API 1

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
verify(true)
```

</details>

#### public API 2

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
verify(1 + 1 == 2)
```

</details>

#### public API 3

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = "test"
verify(x.len() == 4)
```

</details>

#### public API 4

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3]
verify(arr.len() == 3)
```

</details>

#### public API 5

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
for i in 0..5:
    verify(i >= 0)
```

</details>

#### error path 1

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = nil
verify(not opt.?)
```

</details>

#### error path 2

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = []
verify(arr.len() == 0)
```

</details>

#### edge case 1

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
verify(0 == 0)
```

</details>

#### edge case 2

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = ""
verify(s.len() == 0)
```

</details>

#### branch 1

1. verify
2. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if true:
    verify(true)
else:
    verify(false)
```

</details>

#### branch 2

1. Some
2. nil: verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match Some(1):
    Some(x): verify(x == 1)
    nil: verify(false)
```

</details>

<details>
<summary>Advanced: loop 1</summary>

#### loop 1

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sum = 0
for i in 0..5:
    sum = sum + i
verify(sum == 10)
```

</details>


</details>

#### nested 1

1. verify
2. verify
3. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if true:
    if true:
        verify(true)
    else:
        verify(false)
else:
    verify(false)
```

</details>

#### complex 1

1. evens = evens append
2. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3, 4, 5]
var evens = []
for x in arr:
    if x % 2 == 0:
        evens = evens.append(x)
verify(evens.len() == 2)
```

</details>

#### integration 1

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = {"key": "value"}
verify(data["key"] == "value")
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
