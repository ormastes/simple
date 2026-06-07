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

#### defines dataset and tensor dataset contracts

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = pure_data_source()

expect(src).to_contain("trait Dataset:")
expect(src).to_contain("fn len() -> i64")
expect(src).to_contain("fn get(idx: i64) -> (GpuTensor, GpuTensor)")
expect(src).to_contain("class TensorDataset:")
expect(src).to_contain("inputs: [f64]")
expect(src).to_contain("targets: [f64]")
expect(src).to_contain("input_shape: [i64]")
expect(src).to_contain("target_shape: [i64]")
expect(src).to_contain("static fn from_arrays(inputs: [f64], targets: [f64], input_shape: [i64], target_shape: [i64]) -> TensorDataset:")
expect(src).to_contain("val sample_count = inputs.len() / input_numel")
```

</details>

#### defines batched loader iteration and final partial batch behavior

<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = pure_data_source()

expect(src).to_contain("class DataLoader:")
expect(src).to_contain("batch_size: i64")
expect(src).to_contain("shuffle: bool")
expect(src).to_contain("current_idx: i64")
expect(src).to_contain("static fn new(dataset: TensorDataset, batch_size: i64, shuffle: bool) -> DataLoader:")
expect(src).to_contain("fn reset():")
expect(src).to_contain("fn has_next() -> bool:")
expect(src).to_contain("fn next_batch() -> (GpuTensor, GpuTensor):")
expect(src).to_contain("if end > n:")
expect(src).to_contain("val actual_batch_size = end - self.current_idx")
expect(src).to_contain("fn num_batches() -> i64:")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/pure/data_spec.spl` |
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
