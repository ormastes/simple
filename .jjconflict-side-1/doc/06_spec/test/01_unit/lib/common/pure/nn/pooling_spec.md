# Pooling Specification

> <details>

<!-- sdn-diagram:id=pooling_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pooling_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pooling_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pooling_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pooling Specification

## Scenarios

### Pooling

#### keeps max-pooling layer construction and forward path available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = torch_mod_source()

expect(source).to_contain("class MaxPool2d:")
expect(source).to_contain("static fn create(kernel_size: i64, stride: i64) -> MaxPool2d")
expect(source).to_contain("MaxPool2d(kernel_size: kernel_size, stride: stride)")
expect(source).to_contain("rt_torch_nn_max_pool2d(x.handle, k_arr, s_arr, p_arr)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/pure/nn/pooling_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Pooling

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
