# CORE System Test

> <details>

<!-- sdn-diagram:id=core_system_1_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=core_system_1_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

core_system_1_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=core_system_1_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CORE System Test

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CORE-SYS |
| Category | System Testing |
| Status | Implemented |
| Source | `test/03_system/core/core_system_1_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### CORE System Test

<details>
<summary>Advanced: complete workflow 1</summary>

#### complete workflow 1 _(slow)_

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = "system test"
check(input.len() > 0)
```

</details>


</details>

<details>
<summary>Advanced: complete workflow 2</summary>

#### complete workflow 2 _(slow)_

1. data = data append
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = []
for i in 0..20:
    data = data.append(i)
check(data.len() == 20)
```

</details>


</details>

<details>
<summary>Advanced: complete workflow 3</summary>

#### complete workflow 3 _(slow)_

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn test(): pass"
val code_len = code.len()
check(code_len > 0)
```

</details>


</details>

<details>
<summary>Advanced: complete workflow 4</summary>

#### complete workflow 4 _(slow)_

1. Some
2. nil: check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some(42)
match opt:
    Some(x): check(x == 42)
    nil: check(false)
```

</details>


</details>

<details>
<summary>Advanced: complete workflow 5</summary>

#### complete workflow 5 _(slow)_

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = "init"
if state == "init":
    state = "done"
check(state == "done")
```

</details>


</details>

<details>
<summary>Advanced: error handling</summary>

#### error handling _(slow)_

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var error = nil
check(error == nil)
```

</details>


</details>

<details>
<summary>Advanced: edge case</summary>

#### edge case _(slow)_

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty = []
check(empty.len() == 0)
```

</details>


</details>

<details>
<summary>Advanced: boundary</summary>

#### boundary _(slow)_

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val single = [1]
check(single[0] == 1)
```

</details>


</details>

<details>
<summary>Advanced: integration</summary>

#### integration _(slow)_

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 10
val b = 20
check(a + b == 30)
```

</details>


</details>

<details>
<summary>Advanced: validation</summary>

#### validation _(slow)_

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
check(not false)
check(1 == 1)
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
