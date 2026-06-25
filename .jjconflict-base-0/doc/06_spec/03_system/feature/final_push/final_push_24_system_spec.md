# Final System Test

> <details>

<!-- sdn-diagram:id=final_push_24_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=final_push_24_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

final_push_24_system_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=final_push_24_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Final System Test

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #FINAL |
| Category | Testing |
| Status | Implemented |
| Source | `test/03_system/feature/final_push/final_push_24_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### Final System Test

<details>
<summary>Advanced: complete system check 1</summary>

#### complete system check 1 _(slow)_

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 1 + 1
verify(result == 2)
```

</details>


</details>

<details>
<summary>Advanced: complete system check 2</summary>

#### complete system check 2 _(slow)_

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3, 4, 5]
var sum = 0
for x in arr:
    sum = sum + x
verify(sum == 15)
```

</details>


</details>

<details>
<summary>Advanced: complete system check 3</summary>

#### complete system check 3 _(slow)_

1. Some
2. nil: verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some(100)
match opt:
    Some(x): verify(x == 100)
    nil: verify(false)
```

</details>


</details>

<details>
<summary>Advanced: complete system check 4</summary>

#### complete system check 4 _(slow)_

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = "start"
if state == "start":
    state = "processing"
if state == "processing":
    state = "done"
verify(state == "done")
```

</details>


</details>

<details>
<summary>Advanced: complete system check 5</summary>

#### complete system check 5 _(slow)_

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dict = {"a": 1, "b": 2, "c": 3}
val keys = dict.keys()
verify(keys.len() == 3)
```

</details>


</details>

<details>
<summary>Advanced: complete system check 6</summary>

#### complete system check 6 _(slow)_

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = 0
for i in 0..20:
    if i % 2 == 0:
        count = count + 1
verify(count == 10)
```

</details>


</details>

<details>
<summary>Advanced: complete system check 7</summary>

#### complete system check 7 _(slow)_

1. verify
2. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nested = [[1, 2], [3, 4], [5, 6]]
verify(nested.len() == 3)
verify(nested[0].len() == 2)
```

</details>


</details>

<details>
<summary>Advanced: complete system check 8</summary>

#### complete system check 8 _(slow)_

1. verify
2. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "test string"
verify(s.len() == 11)
verify(s.contains("test"))
```

</details>


</details>

<details>
<summary>Advanced: complete system check 9</summary>

#### complete system check 9 _(slow)_

1. verify
2. verify
3. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 10
val b = 20
verify(a < b)
verify(b > a)
verify(a + b == 30)
```

</details>


</details>

<details>
<summary>Advanced: complete system check 10</summary>

#### complete system check 10 _(slow)_

1. results = results append
2. verify
3. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var results = []
for i in 0..5:
    results = results.append(i * i)
verify(results.len() == 5)
verify(results[4] == 16)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 10 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
