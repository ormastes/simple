# Freeze and Unfreeze Collections for Immutability

> The `freeze()` function converts mutable collections (arrays and dicts) into immutable snapshots that support read operations but prevent modification. Frozen collections retain full access to non-mutating operations like indexing, iteration, `map`, `filter`, `reduce`, `keys`, `values`, and `contains`. This spec validates freeze behavior on arrays and dicts, confirms idempotence (freezing an already-frozen collection is a no-op), and verifies that functional operations produce correct results on frozen data.

<!-- sdn-diagram:id=freeze_unfreeze_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=freeze_unfreeze_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

freeze_unfreeze_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=freeze_unfreeze_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Freeze and Unfreeze Collections for Immutability

The `freeze()` function converts mutable collections (arrays and dicts) into immutable snapshots that support read operations but prevent modification. Frozen collections retain full access to non-mutating operations like indexing, iteration, `map`, `filter`, `reduce`, `keys`, `values`, and `contains`. This spec validates freeze behavior on arrays and dicts, confirms idempotence (freezing an already-frozen collection is a no-op), and verifies that functional operations produce correct results on frozen data.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LANG-025 |
| Category | Language |
| Status | Active |
| Source | `test/03_system/feature/usage/freeze_unfreeze_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The `freeze()` function converts mutable collections (arrays and dicts) into immutable
snapshots that support read operations but prevent modification. Frozen collections
retain full access to non-mutating operations like indexing, iteration, `map`, `filter`,
`reduce`, `keys`, `values`, and `contains`. This spec validates freeze behavior on arrays
and dicts, confirms idempotence (freezing an already-frozen collection is a no-op),
and verifies that functional operations produce correct results on frozen data.

## Syntax

```simple
var arr = [1, 2, 3]
val frozen = freeze(arr)           # immutable snapshot
frozen.map(_1 * 2)                # [2, 4, 6] - functional ops work
frozen.filter(_1 % 2 == 0)        # filtering works on frozen

var dict = {"a": 1, "b": 2}
val frozen_dict = freeze(dict)     # frozen dict
frozen_dict.keys()                 # read-only access to keys
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| `freeze()` | Converts a mutable collection into an immutable copy |
| Idempotence | Calling `freeze()` on an already-frozen collection returns an equivalent value |
| Read-only access | Frozen collections support indexing, `len`, `first`, `last`, negative indexing |
| Functional operations | `map`, `filter`, `reduce`, `contains` all work on frozen collections |
| Dict freeze | Frozen dicts support `keys`, `values`, `contains_key`, and key-based access |

## Scenarios

### Freeze and Unfreeze

#### Freeze Function

#### freezes mutable array

1. expect frozen len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3]
val frozen = freeze(arr)
expect frozen[0] == 1
expect frozen.len() == 3
```

</details>

#### freezes mutable dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dict = {"a": 1}
val frozen = freeze(dict)
expect frozen["a"] == 1
```

</details>

#### is idempotent

1. expect frozen again len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = freeze([1, 2, 3])
val frozen_again = freeze(arr)
expect frozen_again[0] == arr[0]
expect frozen_again.len() == arr.len()
```

</details>

#### freezes empty array

1. expect frozen len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frozen = freeze([])
expect frozen.len() == 0
```

</details>

#### freezes empty dict

1. expect frozen len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frozen = freeze({})
expect frozen.len() == 0
```

</details>

#### Frozen Array Operations

#### allows reads on frozen array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frozen = freeze([1, 2, 3])
expect frozen[0] == 1
expect frozen[2] == 3
```

</details>

#### allows len on frozen array

1. expect frozen len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frozen = freeze([1, 2, 3])
expect frozen.len() == 3
```

</details>

#### allows iteration on frozen array

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frozen = freeze([1, 2, 3])
var sum = 0
for x in frozen:
    sum = sum + x
expect sum == 6
```

</details>

#### allows first and last on frozen array

1. expect frozen first
2. expect frozen last


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frozen = freeze([1, 2, 3])
expect frozen.first() == 1
expect frozen.last() == 3
```

</details>

#### allows negative indexing on frozen array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frozen = freeze([1, 2, 3])
expect frozen[-1] == 3
expect frozen[-2] == 2
```

</details>

#### Functional Operations on Frozen

#### allows map on frozen array

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frozen = freeze([1, 2, 3])
val doubled = frozen.map(_1 * 2)
expect doubled[0] == 2
expect doubled[1] == 4
expect doubled[2] == 6
```

</details>

#### allows filter on frozen array

1. expect evens len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frozen = freeze([1, 2, 3, 4, 5])
val evens = frozen.filter(_1 % 2 == 0)
expect evens[0] == 2
expect evens.len() == 2
expect evens[1] == 4
```

</details>

#### allows reduce on frozen array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frozen = freeze([1, 2, 3, 4])
val sum = frozen.reduce(0, \acc, x: acc + x)
expect sum == 10
```

</details>

#### allows contains on frozen array

1. expect frozen contains
2. expect not frozen contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frozen = freeze([1, 2, 3])
expect frozen.contains(2)
expect not frozen.contains(5)
```

</details>

#### Frozen Dict Operations

#### allows reads on frozen dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frozen = freeze({"a": 1, "b": 2})
expect frozen["a"] == 1
expect frozen["b"] == 2
```

</details>

#### allows len on frozen dict

1. expect frozen len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frozen = freeze({"a": 1, "b": 2})
expect frozen.len() == 2
```

</details>

#### allows keys on frozen dict

1. expect keys len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frozen = freeze({"a": 1, "b": 2})
val keys = frozen.keys()
expect keys.len() == 2
```

</details>

#### allows values on frozen dict

1. expect values len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frozen = freeze({"a": 1, "b": 2})
val values = frozen.values()
expect values.len() == 2
```

</details>

#### allows contains_key on frozen dict

1. expect frozen has
2. expect not frozen has


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frozen = freeze({"a": 1})
expect frozen.has("a")
expect not frozen.has("b")
```

</details>

#### Type Behavior

#### treats frozen arrays as arrays

1. expect frozen len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frozen = freeze([1, 2, 3])
expect frozen[0] == 1
expect frozen.len() == 3
```

</details>

#### treats frozen dicts as dicts

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frozen = freeze({"a": 1})
expect frozen["a"] == 1
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
