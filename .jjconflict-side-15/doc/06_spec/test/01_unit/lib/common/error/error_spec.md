# Error Specification

> <details>

<!-- sdn-diagram:id=error_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=error_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

error_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=error_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Error Specification

## Scenarios

### std.error.error

#### rt_error_value

#### returns 27 (RT_ERROR = (SPECIAL_ERROR=3 << 3) | TAG_SPECIAL=3)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = rt_error_value()
expect v == 27
```

</details>

#### is consistent across calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = rt_error_value()
val b = rt_error_value()
expect a == b
```

</details>

#### rt_method_not_found

#### returns RT_ERROR value (27)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = rt_method_not_found("MyType", "some_method")
expect res == 27
```

</details>

#### returns RT_ERROR for empty strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = rt_method_not_found("", "")
expect res == 27
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/error/error_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- std.error.error

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
