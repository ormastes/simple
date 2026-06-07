# Dataset Specification

> <details>

<!-- sdn-diagram:id=dataset_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dataset_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dataset_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dataset_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dataset Specification

## Scenarios

### Dataset

#### sequential sampler

#### creates sequential sampler

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sampler = MockSequentialSampler.new(100)
expect sampler.dataset_size == 100
```

</details>

#### returns indices in order

1. var sampler = MockSequentialSampler new
2. expect sampler is sequential


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sampler = MockSequentialSampler.new(10)
val idx1 = sampler.next_index()
val idx2 = sampler.next_index()
expect idx2 == idx1 + 1
expect sampler.is_sequential()
```

</details>

#### handles large datasets

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sampler = MockSequentialSampler.new(10000)
expect sampler.dataset_size == 10000
```

</details>

### DataLoader

#### sampler

#### creates random sampler

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sampler = MockRandomSampler.new(50)
expect sampler.dataset_size == 50
```

</details>

#### returns all indices

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sampler = MockRandomSampler.new(100)
expect sampler.dataset_size == 100
```

</details>

#### shuffles differently each time

1. expect sampler shuffle


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sampler = MockRandomSampler.new(20)
expect sampler.shuffle()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/ml/dataset_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Dataset
- DataLoader

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
