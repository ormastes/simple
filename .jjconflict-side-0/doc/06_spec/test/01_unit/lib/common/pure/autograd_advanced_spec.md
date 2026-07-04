# Autograd Advanced Specification

> <details>

<!-- sdn-diagram:id=autograd_advanced_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=autograd_advanced_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

autograd_advanced_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=autograd_advanced_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Autograd Advanced Specification

## Scenarios

### Autograd Advanced

#### keeps differentiable composed tensor operations available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = torch_ops_source()

expect(source).to_contain("fn compute_mse_loss_tensor(pred: i64, target: i64) -> i64")
expect(source).to_contain("fn cross_entropy_loss_tensor(logits: i64, targets: i64) -> i64")
expect(source).to_contain("fn rms_norm(x: i64, weight: i64, eps: f64) -> i64")
expect(source).to_contain("fn clip_grad_norm(param_handles: [i64], max_norm: f64) -> f64")
```

</details>

#### keeps explicit temporary tensor cleanup in composed operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = torch_ops_source()

expect(source).to_contain("rt_torch_torchtensor_free(diff)")
expect(source).to_contain("rt_torch_torchtensor_free(gathered)")
expect(source).to_contain("rt_torch_torchtensor_free(var_sqrt)")
expect(source).to_contain("rt_torch_autograd_no_grad_end()")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/pure/autograd_advanced_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Autograd Advanced

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
