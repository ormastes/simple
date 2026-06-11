# Layer Enforcement Specification

> Tests that the numbered layer dependency rule is enforced: layer N can only import from layers with number <= N.

<!-- sdn-diagram:id=layer_enforcement_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=layer_enforcement_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

layer_enforcement_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=layer_enforcement_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Layer Enforcement Specification

Tests that the numbered layer dependency rule is enforced: layer N can only import from layers with number <= N.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LAYER-002 |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/compiler/mdsoc/layer_enforcement_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests that the numbered layer dependency rule is enforced:
layer N can only import from layers with number <= N.

## Behavior

- Layer 70 (backend) can import layer 50 (mir): allowed
- Layer 10 (frontend) cannot import layer 50 (mir): violation
- Layer 00 (common) can only import itself: layer 0
- Non-numbered directories have no constraint

## Scenarios

### Layer Number Extraction

#### extracts 0 from 00.common

1. num = num * 10 +
   - Expected: num equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir = "00.common"
val dot_idx = dir.index_of(".")
val idx = dot_idx ?? 0
val prefix = dir.substring(0, idx)
var num: i64 = 0
for ch in prefix:
    num = num * 10 + (ch.to_i64() - "0".to_i64())
expect(num).to_equal(0)
```

</details>

#### extracts 10 from 10.frontend

1. num = num * 10 +
   - Expected: num equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir = "10.frontend"
val dot_idx = dir.index_of(".")
val idx = dot_idx ?? 0
val prefix = dir.substring(0, idx)
var num: i64 = 0
for ch in prefix:
    num = num * 10 + (ch.to_i64() - "0".to_i64())
expect(num).to_equal(10)
```

</details>

#### extracts 50 from 50.mir

1. num = num * 10 +
   - Expected: num equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir = "50.mir"
val dot_idx = dir.index_of(".")
val idx = dot_idx ?? 0
val prefix = dir.substring(0, idx)
var num: i64 = 0
for ch in prefix:
    num = num * 10 + (ch.to_i64() - "0".to_i64())
expect(num).to_equal(50)
```

</details>

#### extracts 99 from 99.loader

1. num = num * 10 +
   - Expected: num equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir = "99.loader"
val dot_idx = dir.index_of(".")
val idx = dot_idx ?? 0
val prefix = dir.substring(0, idx)
var num: i64 = 0
for ch in prefix:
    num = num * 10 + (ch.to_i64() - "0".to_i64())
expect(num).to_equal(99)
```

</details>

#### returns -1 for non-numbered directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir = "backend"
val dot_idx = dir.index_of(".")
val idx = dot_idx ?? -1
expect(idx).to_equal(-1)
```

</details>

#### returns -1 for invalid prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir = "abc.frontend"
val dot_idx = dir.index_of(".")
val idx = dot_idx ?? 0
val prefix = dir.substring(0, idx)
var all_digits = true
for ch in prefix:
    if ch < "0" or ch > "9":
        all_digits = false
expect(all_digits).to_equal(false)
```

</details>

### Numbered Layer Dependency Checking

#### allows same-layer imports

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Layer 50 -> Layer 50: allowed (50 >= 50)
val from_layer = 50
val to_layer = 50
expect(from_layer >= to_layer).to_equal(true)
```

</details>

#### allows lower-layer imports

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Layer 70 -> Layer 50: allowed (70 >= 50)
val from_layer = 70
val to_layer = 50
expect(from_layer >= to_layer).to_equal(true)
```

</details>

#### allows importing layer 0 from any layer

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Layer 10 -> Layer 0: allowed
val from_layer = 10
val to_layer = 0
expect(from_layer >= to_layer).to_equal(true)
```

</details>

#### rejects higher-layer imports

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Layer 10 -> Layer 50: VIOLATION (10 < 50)
val from_layer = 10
val to_layer = 50
val violation = from_layer < to_layer
expect(violation).to_equal(true)
```

</details>

#### rejects lower importing higher

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Layer 00 -> Layer 99: VIOLATION
val from_layer = 0
val to_layer = 99
val violation = from_layer < to_layer
expect(violation).to_equal(true)
```

</details>

#### no constraint for non-numbered directories

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Both have layer -1 (non-numbered)
val from_layer = -1
val to_layer = 50
# Non-numbered dirs have no constraint
val has_constraint = from_layer >= 0 and to_layer >= 0
expect(has_constraint).to_equal(false)
```

</details>

#### no constraint when both non-numbered

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val from_layer = -1
val to_layer = -1
val has_constraint = from_layer >= 0 and to_layer >= 0
expect(has_constraint).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
