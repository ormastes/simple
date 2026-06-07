# No Paren Specification

> <details>

<!-- sdn-diagram:id=no_paren_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=no_paren_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

no_paren_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=no_paren_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# No Paren Specification

## Scenarios

### No-paren method calls

#### list.len works without parens

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val list = [1, 2, 3]
expect(list.len == 3)
```

</details>

#### string.len works without parens

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val str = "hello"
expect(str.len == 5)
```

</details>

#### comparison with no-paren method call

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = [1, 2, 3, 4, 5]
if items.len > 3:
    expect(true)
else:
    fail("items.len should be greater than 3")
```

</details>

#### works in nested expressions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [[1, 2], [3, 4, 5]]
val total = data[0].len + data[1].len
expect(total == 5)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/shared/control_flow/no_paren_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- No-paren method calls

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
