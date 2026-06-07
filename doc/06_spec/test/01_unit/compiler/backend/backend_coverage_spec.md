# Coverage Test

> 1. check

<!-- sdn-diagram:id=backend_coverage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_coverage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_coverage_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_coverage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Coverage Test

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #9000 |
| Category | Testing |
| Status | Implemented |
| Source | `test/01_unit/compiler/backend/backend_coverage_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### Coverage

#### basic test

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
```

</details>

#### branch 1

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 1
if x > 0:
    check(true)
else:
    check(false)
```

</details>

#### branch 2

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = -1
if x > 0:
    check(false)
else:
    check(true)
```

</details>

<details>
<summary>Advanced: loop coverage</summary>

#### loop coverage

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = 0
for i in 0..10:
    count = count + 1
check(count == 10)
```

</details>


</details>

#### match coverage

1. Some
2. nil: check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = Some(42)
match v:
    Some(x): check(x == 42)
    nil: check(false)
```

</details>

#### match nil

1. Some
2. nil: check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = nil
match v:
    Some(x): check(false)
    nil: check(true)
```

</details>

#### nested branch

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = true
val b = true
if a:
    if b:
        check(true)
    else:
        check(false)
else:
    check(false)
```

</details>

#### array operations

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3]
check(arr.len() == 3)
check(arr[0] == 1)
check(arr[2] == 3)
```

</details>

#### string operations

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello"
check(s.len() == 5)
check(s.contains("ell"))
check(s.starts_with("hel"))
```

</details>

#### dict operations

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = {"key": "value"}
check(d["key"] == "value")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
