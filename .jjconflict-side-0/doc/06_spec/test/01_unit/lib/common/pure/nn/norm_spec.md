# Norm Specification

> <details>

<!-- sdn-diagram:id=norm_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=norm_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

norm_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=norm_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Norm Specification

## Scenarios

### Norm

#### keeps batch normalization layer available

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = torch_mod_source()

expect(source).to_contain("class BatchNorm2d:")
expect(source).to_contain("static fn create(num_features: i64) -> BatchNorm2d")
expect(source).to_contain("rt_torch_nn_batch_norm(x.handle, self.running_mean.handle, self.running_var.handle, self.weight.handle, self.bias.handle, true, 0.1, 1e-5)")
```

</details>

#### keeps RMS norm composed operation available

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = torch_ops_source()

expect(source).to_contain("fn rms_norm(x: i64, weight: i64, eps: f64) -> i64")
expect(source).to_contain("val variance = rt_torch_torchtensor_mean_dim(x_sq, -1, true)")
expect(source).to_contain("val result = rt_torch_torchtensor_mul(normed, weight)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/pure/nn/norm_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Norm

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
