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

#### defines tape entries and gradient operation tags

<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = pure_autograd_source()

expect(src).to_contain("enum GradOp:")
expect(src).to_contain("Leaf")
expect(src).to_contain("Add(left: i64, right: i64)")
expect(src).to_contain("Mul(left: i64, right: i64)")
expect(src).to_contain("MatMul(left: i64, right: i64)")
expect(src).to_contain("ReLU(input: i64)")
expect(src).to_contain("Sigmoid(input: i64)")
expect(src).to_contain("struct TapeEntry:")
expect(src).to_contain("tensor: GpuTensor")
expect(src).to_contain("grad: GpuTensor?")
expect(src).to_contain("requires_grad: bool")
```

</details>

#### defines compute graph forward ops and reverse walk

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = pure_autograd_source()

expect(src).to_contain("class ComputeGraph:")
expect(src).to_contain("tape: [TapeEntry]")
expect(src).to_contain("static fn new() -> ComputeGraph:")
expect(src).to_contain("fn variable(data: GpuTensor, requires_grad: bool) -> i64:")
expect(src).to_contain("fn add(a: i64, b: i64) -> i64:")
expect(src).to_contain("fn mul(a: i64, b: i64) -> i64:")
expect(src).to_contain("fn matmul(a: i64, b: i64) -> i64:")
expect(src).to_contain("fn relu(x: i64) -> i64:")
expect(src).to_contain("fn backward(loss_idx: i64):")
expect(src).to_contain("while i >= 0:")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/pure/autograd_spec.spl` |
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
