# Custom Collection Backends

> Tests custom collection backend implementations including ArrayList and HashMap. Validates that array literals can be typed as ArrayList with push/pop/get operations, and that dictionary literals can be typed as HashMap with key-based access and insertion.

<!-- sdn-diagram:id=custom_backend_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=custom_backend_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

custom_backend_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=custom_backend_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Custom Collection Backends

Tests custom collection backend implementations including ArrayList and HashMap. Validates that array literals can be typed as ArrayList with push/pop/get operations, and that dictionary literals can be typed as HashMap with key-based access and insertion.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #COLL-001 |
| Category | Runtime |
| Status | Active |
| Source | `test/03_system/feature/usage/custom_backend_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests custom collection backend implementations including ArrayList and HashMap.
Validates that array literals can be typed as ArrayList with push/pop/get
operations, and that dictionary literals can be typed as HashMap with
key-based access and insertion.

## Syntax

```simple
val arr: ArrayList = [1, 2, 3]
arr.push(3)
val map: HashMap = {"a": 1, "b": 2}
map["b"] = 2
```
Custom Collection Backends - SPipe Tests

## Scenarios

### Custom Collection Backends

#### ArrayList Implementation

#### should create ArrayList from array literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: ArrayList = [1, 2, 3]
expect(arr.len()).to_equal(3)
```

</details>

#### should support push

1. arr push
   - Expected: arr.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr: ArrayList = [1, 2]
arr.push(3)
expect(arr.len()).to_equal(3)
```

</details>

#### should support pop

1. expect arr len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr: ArrayList = [1, 2, 3]
val last = arr.pop()
expect last == 3
expect arr.len() == 2
```

</details>

#### should support get

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: ArrayList = [10, 20, 30]
expect(arr.get(0)).to_equal(10)
expect(arr.get(2)).to_equal(30)
```

</details>

#### HashMap Implementation

#### should create HashMap from dict literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val map: HashMap = {"a": 1, "b": 2}
expect(map.len()).to_equal(2)
```

</details>

#### should support get

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val map: HashMap = {"a": 1, "b": 2}
expect map["a"] == 1
expect map["b"] == 2
```

</details>

#### should support insert

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var map: HashMap = {"a": 1}
map["b"] = 2
expect map["b"] == 2
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
