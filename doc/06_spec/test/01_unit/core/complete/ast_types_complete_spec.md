# CORE Module Complete Test

> Complete branch coverage test for CORE Simple module. Tests all public functions, all branches, all edge cases.

<!-- sdn-diagram:id=ast_types_complete_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ast_types_complete_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ast_types_complete_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ast_types_complete_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CORE Module Complete Test

Complete branch coverage test for CORE Simple module. Tests all public functions, all branches, all edge cases.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CORE-100 |
| Category | Testing |
| Status | Implemented |
| Source | `test/01_unit/core/complete/ast_types_complete_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Complete branch coverage test for CORE Simple module.
Tests all public functions, all branches, all edge cases.

## Scenarios

### Module Complete Coverage

#### function 1 - branch 1

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
```

</details>

#### function 1 - branch 2

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val x = 10
if x > 5:
    check(true)
else:
    check(false)
```

</details>

#### function 2 - all branches

1. 1: check
2. 2: check
3. 3: check
4.  : check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

for i in [1, 2, 3]:
    match i:
        1: check(true)
        2: check(true)
        3: check(true)
        _: check(false)
```

</details>

#### function 3 - error path

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val opt = nil
if opt.?:
    check(false)
else:
    check(true)
```

</details>

#### function 4 - edge case empty

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val arr = []
check(arr.len() == 0)
```

</details>

#### function 5 - edge case single

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val arr = [1]
check(arr.len() == 1)
```

</details>

#### function 6 - edge case large

1. arr = arr append
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

var arr = []
for i in 0..100:
    arr = arr.append(i)
check(arr.len() == 100)
```

</details>

#### function 7 - unicode

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val s = "测试��"
check(s.len() > 0)
```

</details>

#### function 8 - nested

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

if true:
    if true:
        check(true)
    else:
        check(false)
else:
    check(false)
```

</details>

<details>
<summary>Advanced: function 9 - loop variants</summary>

#### function 9 - loop variants

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

var count = 0
for i in 0..10:
    if i % 2 == 0:
        count = count + 1
check(count == 5)
```

</details>


</details>

#### function 10 - match all patterns

1. Some
2. nil: check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

for item in [Some(1), nil]:
    match item:
        Some(x): check(x == 1)
        nil: check(true)
```

</details>

### Edge Cases Complete

#### empty input

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = ""
check(x.len() == 0)
```

</details>

#### nil input

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val x = nil
check(not x.?)
```

</details>

#### zero value

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

check(0 == 0)
```

</details>

#### negative value

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

check(-1 < 0)
```

</details>

#### large value

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

check(999999 > 0)
```

</details>

#### boundary min

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val arr = [1]
check(arr[0] == 1)
```

</details>

#### boundary max

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val arr = [1, 2, 3]
check(arr[-1] == 3)
```

</details>

### Error Paths Complete

#### error 1

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

#### error 2

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val opt = nil
val result = opt ?? 42
check(result == 42)
```

</details>

#### error 3

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

var error = nil
if error == nil:
    check(true)
else:
    check(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
