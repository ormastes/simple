# Option Utils Inline Specification

> <details>

<!-- sdn-diagram:id=option_utils_inline_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=option_utils_inline_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

option_utils_inline_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=option_utils_inline_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Option Utils Inline Specification

## Scenarios

### unwrap_or

#### returns value when present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = unwrap_or(42, 0)
expect(result).to_equal(42)
```

</details>

#### returns default when nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = unwrap_or(nil, 10)
expect(result).to_equal(10)
```

</details>

#### returns zero value when present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = unwrap_or(0, 99)
expect(result).to_equal(0)
```

</details>

#### returns negative value when present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = unwrap_or(-5, 0)
expect(result).to_equal(-5)
```

</details>

#### returns default with negative default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = unwrap_or(nil, -1)
expect(result).to_equal(-1)
```

</details>

#### returns large value when present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = unwrap_or(999999, 0)
expect(result).to_equal(999999)
```

</details>

### is_some

#### returns true for non-nil value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = is_some(42)
expect(result).to_equal(true)
```

</details>

#### returns false for nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = is_some(nil)
expect(result).to_equal(false)
```

</details>

#### returns true for zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = is_some(0)
expect(result).to_equal(true)
```

</details>

#### returns true for negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = is_some(-1)
expect(result).to_equal(true)
```

</details>

#### returns true for string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = is_some("hello")
expect(result).to_equal(true)
```

</details>

#### returns true for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = is_some("")
expect(result).to_equal(true)
```

</details>

### is_none

#### returns true for nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = is_none(nil)
expect(result).to_equal(true)
```

</details>

#### returns false for non-nil value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = is_none(42)
expect(result).to_equal(false)
```

</details>

#### returns false for zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = is_none(0)
expect(result).to_equal(false)
```

</details>

#### returns false for negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = is_none(-1)
expect(result).to_equal(false)
```

</details>

#### returns false for string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = is_none("hello")
expect(result).to_equal(false)
```

</details>

#### returns false for empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = is_none([])
expect(result).to_equal(false)
```

</details>

### option_utils combined patterns

#### unwrap_or with is_some check

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = 42
if is_some(opt):
    val val_result = unwrap_or(opt, 0)
    expect(val_result).to_equal(42)
```

</details>

#### unwrap_or with is_none check

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = nil
if is_none(opt):
    val val_result = unwrap_or(opt, -1)
    expect(val_result).to_equal(-1)
```

</details>

#### chain of option operations

1. sum = sum + unwrap or
   - Expected: sum equals `148`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var values = [42, nil, 7, nil, 99]
var sum = 0
for v in values:
    sum = sum + unwrap_or(v, 0)
expect(sum).to_equal(148)
```

</details>

#### count non-nil values

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var values = [1, nil, 3, nil, 5]
var count = 0
for v in values:
    if is_some(v):
        count = count + 1
expect(count).to_equal(3)
```

</details>

#### count nil values

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var values = [1, nil, 3, nil, 5]
var count = 0
for v in values:
    if is_none(v):
        count = count + 1
expect(count).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/shared/types/option_utils_inline_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- unwrap_or
- is_some
- is_none
- option_utils combined patterns

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
