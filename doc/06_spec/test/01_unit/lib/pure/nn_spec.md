# Nn Specification

> <details>

<!-- sdn-diagram:id=nn_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nn_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nn_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nn_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nn Specification

## Scenarios

### Nn

#### defines module trait and linear layer parameter contracts

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = pure_nn_source()

expect(src).to_contain("trait Module:")
expect(src).to_contain("fn forward(input: GpuTensor, graph: ComputeGraph) -> i64")
expect(src).to_contain("fn parameters() -> [GradTensor]")
expect(src).to_contain("class GpuLinear:")
expect(src).to_contain("weight: GradTensor")
expect(src).to_contain("bias: GradTensor?")
expect(src).to_contain("in_features: i64")
expect(src).to_contain("out_features: i64")
expect(src).to_contain("static fn new(graph: ComputeGraph, in_features: i64, out_features: i64, use_bias: bool) -> GpuLinear:")
expect(src).to_contain("val weight_shape: [i64] = [out_features, in_features]")
```

</details>

#### defines activation sequential container and parameter collection

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = pure_nn_source()

expect(src).to_contain("class GpuReLU:")
expect(src).to_contain("static fn new() -> GpuReLU:")
expect(src).to_contain("graph.relu(input_idx)")
expect(src).to_contain("fn parameters() -> [GradTensor]:")
expect(src).to_contain("ReLU has no trainable parameters")
expect(src).to_contain("class GpuSequential:")
expect(src).to_contain("layers: [Module]")
expect(src).to_contain("static fn new(layers: [Module]) -> GpuSequential:")
expect(src).to_contain("for layer in self.layers:")
expect(src).to_contain("params.push(p)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/pure/nn_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Nn

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
