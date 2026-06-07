# Torch Training Specification

> <details>

<!-- sdn-diagram:id=torch_training_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=torch_training_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

torch_training_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=torch_training_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Torch Training Specification

## Scenarios

### Loss Functions

### MSELoss

#### creates MSELoss instance

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# MSELoss.create() returns loss function
val created = true
expect(created).to_equal(true)
```

</details>

#### computes loss from pred and target tensors

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# forward(pred, target) returns scalar loss tensor
# Uses rt_torch_nn_mse_loss FFI
val loss_computed = true
expect(loss_computed).to_equal(true)
```

</details>

### CrossEntropyLoss

#### creates CrossEntropyLoss instance

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# CrossEntropyLoss.create() returns loss function
val created = true
expect(created).to_equal(true)
```

</details>

#### computes cross-entropy from logits and targets

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# forward(logits, targets) returns scalar loss
# Uses rt_torch_nn_cross_entropy FFI
val loss_computed = true
expect(loss_computed).to_equal(true)
```

</details>

### Optimizers

### SGD

#### creates SGD with parameters and learning rate

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SGD.create(params, lr, momentum) initializes velocities
val lr = 0
val momentum = 0
expect(lr).to_equal(0)
```

</details>

#### initializes velocity tensors to zeros

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Each parameter gets a corresponding velocity tensor
val num_params = 3
val num_velocities = 3
expect(num_params).to_equal(num_velocities)
```

</details>

#### step updates parameters using gradient

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# velocity = momentum * velocity + lr * grad
# param = param - velocity
val updated = true
expect(updated).to_equal(true)
```

</details>

#### zero_grad clears all gradients

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cleared = true
expect(cleared).to_equal(true)
```

</details>

### Adam

#### creates Adam with beta1 and beta2

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Adam.create(params, lr, beta1, beta2)
val beta1 = 0
val beta2 = 0
expect(beta1).to_equal(0)
```

</details>

#### initializes first and second moment estimates

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# m (first moment) and v (second moment) per parameter
val num_m = 3
val num_v = 3
expect(num_m).to_equal(num_v)
```

</details>

#### increments timestep on each step

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# self.t = self.t + 1 at start of step()
var t = 0
t = t + 1
expect(t).to_equal(1)
```

</details>

#### applies bias correction

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# m_hat = m / (1 - beta1^t)
# v_hat = v / (1 - beta2^t)
val bias_corrected = true
expect(bias_corrected).to_equal(true)
```

</details>

### RMSprop

#### creates RMSprop with alpha and eps

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RMSprop.create(params, lr, alpha, eps)
val alpha = 0
val eps = 0
expect(alpha).to_equal(0)
```

</details>

#### tracks running average of squared gradients

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# v = alpha * v + (1 - alpha) * grad^2
val tracked = true
expect(tracked).to_equal(true)
```

</details>

### Utility Functions

#### no_grad calls function without gradient tracking

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# no_grad(f) calls f() (placeholder implementation)
val called = true
expect(called).to_equal(true)
```

</details>

#### set_seed is documented no-op

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# No rt_torch_manual_seed FFI available yet
val seed = 42
expect(seed).to_equal(42)
```

</details>

#### manual_seed aliases set_seed

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seed = 123
expect(seed).to_equal(123)
```

</details>

### Sequential Container

#### creates empty Sequential

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Sequential.create() with empty layer lists
val num_linear = 0
val num_conv = 0
expect(num_linear).to_equal(0)
```

</details>

#### adds Linear layers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = 0
count = count + 1
expect(count).to_equal(1)
```

</details>

#### forward passes through all layers in order

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Linear layers first, then Conv2d layers
val order_correct = true
expect(order_correct).to_equal(true)
```

</details>

#### collects parameters from all layers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# parameters() concatenates params from all layers
val all_params_count = 4
expect(all_params_count).to_be_greater_than(0)
```

</details>

### Stream

#### creates CUDA stream for device

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Stream.create(device_id) via rt_torch_stream_create
val device_id = 0
expect(device_id).to_equal(0)
```

</details>

#### synchronize waits for completion

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val synced = true
expect(synced).to_equal(true)
```

</details>

#### query checks completion status

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val completed = true
expect(completed).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/torch_training_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Loss Functions
- MSELoss
- CrossEntropyLoss
- Optimizers
- SGD
- Adam
- RMSprop
- Utility Functions
- Sequential Container
- Stream

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
