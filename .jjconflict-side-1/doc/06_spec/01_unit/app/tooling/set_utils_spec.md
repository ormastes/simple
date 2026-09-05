# Set Utils Specification

> 1. expect set size

<!-- sdn-diagram:id=set_utils_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=set_utils_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

set_utils_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=set_utils_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Set Utils Specification

## Scenarios

### Set Utils

#### deduplicates array input

1. expect set size
2. expect set contains
3. expect set contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = set_from_array(["alpha", "beta", "alpha"])
expect set_size(s) == 2
expect set_contains(s, "alpha") == true
expect set_contains(s, "gamma") == false
```

</details>

#### adds a missing item without duplicating existing items

1. var s = set from array
2. s = set add
3. s = set add
4. expect set size
5. expect set contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = set_from_array(["alpha"])
s = set_add(s, "beta")
s = set_add(s, "beta")
expect set_size(s) == 2
expect set_contains(s, "beta") == true
```

</details>

#### computes union intersection and difference

1. expect set size
2. expect set contains
3. expect set contains
4. expect set contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left = set_from_array(["alpha", "beta"])
val right = set_from_array(["beta", "gamma"])
val unioned = set_union(left, right)
val common = set_intersection(left, right)
val only_left = set_difference(left, right)

expect set_size(unioned) == 3
expect set_contains(common, "beta") == true
expect set_contains(only_left, "alpha") == true
expect set_contains(only_left, "gamma") == false
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/tooling/set_utils_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Set Utils

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
