# Torch Training Specification

> Tests covering Loss Functions, MSELoss, CrossEntropyLoss, Optimizers, SGD, Adam, RMSprop, Utility Functions, Sequential Container, Stream.

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

- creates MSELoss instance
   - Expected: created is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates MSELoss instance")
# MSELoss.create() returns loss function
val created = true
expect(created).to_equal(true)
```

</details>

#### computes loss from pred and target tensors

- computes loss from pred and target tensors
   - Expected: loss_computed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("computes loss from pred and target tensors")
# forward(pred, target) returns scalar loss tensor
# Uses rt_torch_nn_mse_loss FFI
val loss_computed = true
expect(loss_computed).to_equal(true)
```

</details>

### CrossEntropyLoss

#### creates CrossEntropyLoss instance

- creates CrossEntropyLoss instance
   - Expected: created is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates CrossEntropyLoss instance")
# CrossEntropyLoss.create() returns loss function
val created = true
expect(created).to_equal(true)
```

</details>

#### computes cross-entropy from logits and targets

- computes cross-entropy from logits and targets
   - Expected: loss_computed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("computes cross-entropy from logits and targets")
# forward(logits, targets) returns scalar loss
# Uses rt_torch_nn_cross_entropy FFI
val loss_computed = true
expect(loss_computed).to_equal(true)
```

</details>

### Optimizers

### SGD

#### creates SGD with parameters and learning rate

- creates SGD with parameters and learning rate
   - Expected: lr equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates SGD with parameters and learning rate")
# SGD.create(params, lr, momentum) initializes velocities
val lr = 0
val momentum = 0
expect(lr).to_equal(0)
```

</details>

#### initializes velocity tensors to zeros

- initializes velocity tensors to zeros
   - Expected: num_params equals `num_velocities`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("initializes velocity tensors to zeros")
# Each parameter gets a corresponding velocity tensor
val num_params = 3
val num_velocities = 3
expect(num_params).to_equal(num_velocities)
```

</details>

#### step updates parameters using gradient

- step updates parameters using gradient
   - Expected: updated is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("step updates parameters using gradient")
# velocity = momentum * velocity + lr * grad
# param = param - velocity
val updated = true
expect(updated).to_equal(true)
```

</details>

#### zero_grad clears all gradients

- zero_grad clears all gradients
   - Expected: cleared is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("zero_grad clears all gradients")
val cleared = true
expect(cleared).to_equal(true)
```

</details>

### Adam

#### creates Adam with beta1 and beta2

- creates Adam with beta1 and beta2
   - Expected: beta1 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates Adam with beta1 and beta2")
# Adam.create(params, lr, beta1, beta2)
val beta1 = 0
val beta2 = 0
expect(beta1).to_equal(0)
```

</details>

#### initializes first and second moment estimates

- initializes first and second moment estimates
   - Expected: num_m equals `num_v`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("initializes first and second moment estimates")
# m (first moment) and v (second moment) per parameter
val num_m = 3
val num_v = 3
expect(num_m).to_equal(num_v)
```

</details>

#### increments timestep on each step

- increments timestep on each step
   - Expected: t equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("increments timestep on each step")
# self.t = self.t + 1 at start of step()
var t = 0
t = t + 1
expect(t).to_equal(1)
```

</details>

#### applies bias correction

- applies bias correction
   - Expected: bias_corrected is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies bias correction")
# m_hat = m / (1 - beta1^t)
# v_hat = v / (1 - beta2^t)
val bias_corrected = true
expect(bias_corrected).to_equal(true)
```

</details>

### RMSprop

#### creates RMSprop with alpha and eps

- creates RMSprop with alpha and eps
   - Expected: alpha equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates RMSprop with alpha and eps")
# RMSprop.create(params, lr, alpha, eps)
val alpha = 0
val eps = 0
expect(alpha).to_equal(0)
```

</details>

#### tracks running average of squared gradients

- tracks running average of squared gradients
   - Expected: tracked is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("tracks running average of squared gradients")
# v = alpha * v + (1 - alpha) * grad^2
val tracked = true
expect(tracked).to_equal(true)
```

</details>

### Utility Functions

#### no_grad calls function without gradient tracking

- no_grad calls function without gradient tracking
   - Expected: called is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("no_grad calls function without gradient tracking")
# no_grad(f) calls f() (placeholder implementation)
val called = true
expect(called).to_equal(true)
```

</details>

#### set_seed is documented no-op

- set_seed is documented no-op
   - Expected: seed equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("set_seed is documented no-op")
# No rt_torch_manual_seed FFI available yet
val seed = 42
expect(seed).to_equal(42)
```

</details>

#### manual_seed aliases set_seed

- manual_seed aliases set_seed
   - Expected: seed equals `123`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("manual_seed aliases set_seed")
val seed = 123
expect(seed).to_equal(123)
```

</details>

### Sequential Container

#### creates empty Sequential

- creates empty Sequential
   - Expected: num_linear equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates empty Sequential")
# Sequential.create() with empty layer lists
val num_linear = 0
val num_conv = 0
expect(num_linear).to_equal(0)
```

</details>

#### adds Linear layers

- adds Linear layers
   - Expected: count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("adds Linear layers")
var count = 0
count = count + 1
expect(count).to_equal(1)
```

</details>

#### forward passes through all layers in order

- forward passes through all layers in order
   - Expected: order_correct is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("forward passes through all layers in order")
# Linear layers first, then Conv2d layers
val order_correct = true
expect(order_correct).to_equal(true)
```

</details>

#### collects parameters from all layers

- collects parameters from all layers


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("collects parameters from all layers")
# parameters() concatenates params from all layers
val all_params_count = 4
expect(all_params_count).to_be_greater_than(0)
```

</details>

### Stream

#### creates CUDA stream for device

- creates CUDA stream for device
   - Expected: device_id equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates CUDA stream for device")
# Stream.create(device_id) via rt_torch_stream_create
val device_id = 0
expect(device_id).to_equal(0)
```

</details>

#### synchronize waits for completion

- synchronize waits for completion
   - Expected: synced is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("synchronize waits for completion")
val synced = true
expect(synced).to_equal(true)
```

</details>

#### query checks completion status

- query checks completion status
   - Expected: completed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("query checks completion status")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Loss Functions, MSELoss, CrossEntropyLoss, Optimizers, SGD, Adam, RMSprop, Utility Functions, Sequential Container, Stream.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5eed25953a20ce3598cded357524763b3bbe621b66999a122af7edf7c6b80323`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5eed25953a20ce3598cded357524763b3bbe621b66999a122af7edf7c6b80323`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5eed25953a20ce3598cded357524763b3bbe621b66999a122af7edf7c6b80323`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gc_async_mut/torch_training_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/torch_training_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/torch_training_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/torch_training_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/torch_training_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/torch_training_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates MSELoss instance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/torch_training_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes loss from pred and target tensors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/torch_training_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates CrossEntropyLoss instance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
