# Performance & Stress Test

> <details>

<!-- sdn-diagram:id=large_dict_small_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=large_dict_small_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

large_dict_small_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=large_dict_small_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Performance & Stress Test

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PERFORMANCE |
| Category | Performance Testing |
| Status | Implemented |
| Source | `test/05_perf/stress/large_dict_small_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### Performance Test

<details>
<summary>Advanced: stress test 1</summary>

#### stress test 1 _(slow)_

1. arr = arr append
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = []
for i in 0..100:
    arr = arr.append(i)
check(arr.len() == 100)
```

</details>


</details>

<details>
<summary>Advanced: stress test 2</summary>

#### stress test 2 _(slow)_

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sum = 0
for i in 0..1000:
    sum = sum + i
check(sum == 499500)
```

</details>


</details>

<details>
<summary>Advanced: stress test 3</summary>

#### stress test 3 _(slow)_

1. data = data append
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = []
for i in 0..50:
    data = data.append([i, i * 2, i * 3])
check(data.len() == 50)
```

</details>


</details>

<details>
<summary>Advanced: stress test 4</summary>

#### stress test 4 _(slow)_

1. dict = dict set
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dict = {}
for i in 0..100:
    dict = dict_set(dict, "key_" + str(i), i)
check(dict_keys(dict).len() == 100)
```

</details>


</details>

<details>
<summary>Advanced: stress test 5</summary>

#### stress test 5 _(slow)_

1. inner = inner append
2. nested = nested append
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var nested = []
for i in 0..20:
    var inner = []
    for j in 0..20:
        inner = inner.append(i * j)
    nested = nested.append(inner)
check(nested.len() == 20)
```

</details>


</details>

<details>
<summary>Advanced: stress test 6</summary>

#### stress test 6 _(slow)_

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = ""
for i in 0..100:
    result = result + "x"
check(result.len() == 100)
```

</details>


</details>

<details>
<summary>Advanced: stress test 7</summary>

#### stress test 7 _(slow)_

1. processed = processed append
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var processed = []
for i in 0..200:
    if i % 2 == 0:
        processed = processed.append(i)
check(processed.len() == 100)
```

</details>


</details>

<details>
<summary>Advanced: stress test 8</summary>

#### stress test 8 _(slow)_

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = 0
for i in 0..10:
    for j in 0..10:
        for k in 0..10:
            count = count + 1
check(count == 1000)
```

</details>


</details>

<details>
<summary>Advanced: memory stress</summary>

#### memory stress _(slow)_

1. data = data append
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = []
for i in 0..100:
    data = data.append({"id": i, "data": [1, 2, 3, 4, 5]})
check(data.len() == 100)
```

</details>


</details>

<details>
<summary>Advanced: combined stress</summary>

#### combined stress _(slow)_

1. temp = temp append
2. final = final append
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var final = []
for i in 0..50:
    var temp = []
    for j in 0..50:
        temp = temp.append(i + j)
    var sum = 0
    for x in temp:
        sum = sum + x
    final = final.append(sum)
check(final.len() == 50)
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
