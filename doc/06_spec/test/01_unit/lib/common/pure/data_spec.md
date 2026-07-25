# Data Specification

> <details>

<!-- sdn-diagram:id=data_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=data_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

data_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=data_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Data Specification

## Scenarios

### Data

#### keeps training batch prefetching available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = data_pipeline_source()

expect(source).to_contain("fn prefetch_batches(dataset: ArrayDataset, batch_size: i64, num_batches: i64) -> [[f64]]")
expect(source).to_contain("val dataset_len = dataset.len()")
expect(source).to_contain("val sample = dataset.get_item(i)")
expect(source).to_contain("batches.push(batch)")
```

</details>

#### keeps deterministic index shuffling available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = data_pipeline_source()

expect(source).to_contain("fn shuffle_indices(length: i64, seed: i64) -> [i64]")
expect(source).to_contain("Fisher-Yates shuffle")
expect(source).to_contain("current_seed = (a * current_seed + c) % m")
expect(source).to_contain("indices[i] = indices[j]")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/pure/data_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Data

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
