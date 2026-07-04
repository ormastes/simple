# Autograd Specification

> <details>

<!-- sdn-diagram:id=autograd_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=autograd_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

autograd_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=autograd_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Autograd Specification

## Scenarios

### Autograd

#### keeps tensor gradient controls available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = torch_mod_source()

expect(source).to_contain("fn backward():")
expect(source).to_contain("fn zero_grad():")
expect(source).to_contain("fn requires_grad(value: bool) -> Tensor")
expect(source).to_contain("fn detach() -> Tensor")
```

</details>

#### keeps no-grad and gradient clipping helpers available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = torch_ops_source()

expect(source).to_contain("rt_torch_autograd_no_grad_begin")
expect(source).to_contain("rt_torch_autograd_no_grad_end")
expect(source).to_contain("fn clip_grad_norm(param_handles: [i64], max_norm: f64) -> f64")
expect(source).to_contain("val g = rt_torch_autograd_grad(h)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/pure/autograd_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Autograd

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
