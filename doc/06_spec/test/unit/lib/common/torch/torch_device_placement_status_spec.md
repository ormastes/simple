# Torch Device Placement Status Specification

> <details>

<!-- sdn-diagram:id=torch_device_placement_status_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=torch_device_placement_status_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

torch_device_placement_status_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=torch_device_placement_status_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Torch Device Placement Status Specification

## Scenarios

### Torch device placement status

#### passes explicit CUDA device ids through backend facades

- assert backend uses requested cuda device
- assert backend uses requested cuda device


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_backend_uses_requested_cuda_device("src/lib/gc_async_mut/torch/backend.spl")
assert_backend_uses_requested_cuda_device("src/lib/nogc_sync_mut/torch/backend.spl")
```

</details>

#### passes explicit CUDA device ids through Tensor methods

- assert tensor method uses requested cuda device
- assert tensor method uses requested cuda device


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_tensor_method_uses_requested_cuda_device("src/lib/gc_async_mut/torch/mod.spl")
assert_tensor_method_uses_requested_cuda_device("src/lib/nogc_sync_mut/torch/mod.spl")
```

</details>

#### keeps GC Tensor arithmetic ownership handoffs mutable

- assert gc tensor arithmetic uses mutable ownership handoffs


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_gc_tensor_arithmetic_uses_mutable_ownership_handoffs("src/lib/gc_async_mut/torch/mod.spl")
```

</details>

#### passes explicit stream device ids to stream creation

- assert stream uses requested device
- assert stream uses requested device


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_stream_uses_requested_device("src/lib/gc_async_mut/torch/torch_training.spl")
assert_stream_uses_requested_device("src/lib/nogc_sync_mut/torch/torch_training.spl")
```

</details>

#### does not initialize optimizer state by forcing CUDA device zero

- assert optimizer does not force cuda zero
- assert optimizer does not force cuda zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_optimizer_does_not_force_cuda_zero("src/lib/gc_async_mut/torch/optim.spl")
assert_optimizer_does_not_force_cuda_zero("src/lib/nogc_sync_mut/torch/optim.spl")
```

</details>

#### initializes optimizer state on the parameter device

- assert optimizer state uses parameter device
- assert optimizer state uses parameter device


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_optimizer_state_uses_parameter_device("src/lib/gc_async_mut/torch/optim.spl")
assert_optimizer_state_uses_parameter_device("src/lib/nogc_sync_mut/torch/optim.spl")
```

</details>

#### declares mutating training optimizer steps with mutable receivers

- assert mutating training optimizers use mut receiver
- assert mutating training optimizers use mut receiver


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_mutating_training_optimizers_use_mut_receiver("src/lib/gc_async_mut/torch/torch_training.spl")
assert_mutating_training_optimizers_use_mut_receiver("src/lib/nogc_sync_mut/torch/torch_training.spl")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/torch/torch_device_placement_status_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Torch device placement status

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
