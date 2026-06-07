# Data Loader Specification

> <details>

<!-- sdn-diagram:id=data_loader_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=data_loader_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

data_loader_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=data_loader_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Data Loader Specification

## Scenarios

### DataLoader

#### keeps batch prefetching over ArrayDataset available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = data_pipeline_source()

expect(source).to_contain("use std.pure.data.dataset.{ArrayDataset}")
expect(source).to_contain("fn prefetch_batches(dataset: ArrayDataset, batch_size: i64, num_batches: i64) -> [[f64]]")
expect(source).to_contain("var batches: [[f64]] = []")
expect(source).to_contain("for v in sample:")
```

</details>

#### keeps deterministic shuffled index generation available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = data_pipeline_source()

expect(source).to_contain("fn shuffle_indices(length: i64, seed: i64) -> [i64]")
expect(source).to_contain("var indices: [i64] = []")
expect(source).to_contain("val temp = indices[i]")
expect(source).to_contain("indices[j] = temp")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/pure/data_loader_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DataLoader

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
