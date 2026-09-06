# Dataset Bounds Specification

> <details>

<!-- sdn-diagram:id=dataset_bounds_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dataset_bounds_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dataset_bounds_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dataset_bounds_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dataset Bounds Specification

## Scenarios

### Dataset Bounds

### ArrayDataset

#### returns empty for negative index

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [[1.0, 2.0], [3.0, 4.0]]
val ds = ArrayDataset(data: data)
val result = ds.get_item(-1)
expect(result.len()).to_equal(0)
```

</details>

#### returns empty for out-of-bounds index

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [[1.0, 2.0], [3.0, 4.0]]
val ds = ArrayDataset(data: data)
val result = ds.get_item(5)
expect(result.len()).to_equal(0)
```

</details>

#### returns valid item for in-bounds index

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [[1.0, 2.0], [3.0, 4.0]]
val ds = ArrayDataset(data: data)
val result = ds.get_item(0)
expect(result.len()).to_equal(2)
```

</details>

#### returns correct len

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [[1.0], [2.0], [3.0]]
val ds = ArrayDataset(data: data)
expect(ds.len()).to_equal(3)
```

</details>

### LabeledDataset

#### returns default sample for negative index

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features = [[1.0, 2.0]]
val labels = [0.0]
val ds = LabeledDataset(features: features, labels: labels)
val result = ds.get_item(-1)
expect(result.feature.len()).to_equal(0)
expect(result.label).to_equal(0.0)
```

</details>

#### returns default sample for out-of-bounds index

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features = [[1.0, 2.0]]
val labels = [0.0]
val ds = LabeledDataset(features: features, labels: labels)
val result = ds.get_item(10)
expect(result.feature.len()).to_equal(0)
expect(result.label).to_equal(0.0)
```

</details>

#### returns valid sample for in-bounds index

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features = [[1.0, 2.0], [3.0, 4.0]]
val labels = [0.0, 1.0]
val ds = LabeledDataset(features: features, labels: labels)
val result = ds.get_item(1)
expect(result.label).to_equal(1.0)
```

</details>

#### returns correct len

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features = [[1.0], [2.0]]
val labels = [0.0, 1.0]
val ds = LabeledDataset(features: features, labels: labels)
expect(ds.len()).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/pure/data/dataset_bounds_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Dataset Bounds
- ArrayDataset
- LabeledDataset

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
