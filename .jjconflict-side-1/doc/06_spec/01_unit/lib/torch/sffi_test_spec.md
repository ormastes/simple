# Sffi Test Specification

> <details>

<!-- sdn-diagram:id=sffi_test_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sffi_test_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sffi_test_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sffi_test_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 40 | 40 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sffi Test Specification

## Scenarios

### SFFI Integration Tests

### Tensor Operations

#### creates tensor with data and shape

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = MockTensor.create([1.0, 2.0, 3.0, 4.0], [2, 2])
expect(t.data.len()).to_equal(4)
expect(t.shape).to_equal([2, 2])
```

</details>

#### returns correct numel

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = MockTensor.create([1.0, 2.0, 3.0], [3])
expect(t.numel()).to_equal(3)
```

</details>

#### accesses elements by index

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = MockTensor.create([10.0, 20.0, 30.0], [3])
expect(t.get(0)).to_equal(10.0)
expect(t.get(1)).to_equal(20.0)
expect(t.get(2)).to_equal(30.0)
```

</details>

#### returns correct dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = MockTensor.create([1.0, 2.0, 3.0, 4.0, 5.0, 6.0], [2, 3])
expect(t.dim()).to_equal(2)
expect(t.size(0)).to_equal(2)
expect(t.size(1)).to_equal(3)
```

</details>

#### adds two tensors element-wise

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = MockTensor.create([1.0, 2.0, 3.0], [3])
val b = MockTensor.create([4.0, 5.0, 6.0], [3])
val c = a.add_tensor(b)
expect(c.data[0]).to_equal(5.0)
expect(c.data[1]).to_equal(7.0)
expect(c.data[2]).to_equal(9.0)
```

</details>

#### multiplies tensor by scalar

1. var result = t mul scalar
   - Expected: result.data[0] equals `4.0`
   - Expected: result.data[1] equals `6.0`
   - Expected: result.data[2] equals `8.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = MockTensor.create([2.0, 3.0, 4.0], [3])
var result = t.mul_scalar(2.0)
expect(result.data[0]).to_equal(4.0)
expect(result.data[1]).to_equal(6.0)
expect(result.data[2]).to_equal(8.0)
```

</details>

#### subtracts two tensors element-wise

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = MockTensor.create([5.0, 8.0, 3.0], [3])
val b = MockTensor.create([1.0, 2.0, 3.0], [3])
val c = a.sub_tensor(b)
expect(c.data[0]).to_equal(4.0)
expect(c.data[1]).to_equal(6.0)
expect(c.data[2]).to_equal(0.0)
```

</details>

#### computes mean value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = MockTensor.create([2.0, 4.0, 6.0], [3])
expect(t.mean_val()).to_equal(4.0)
```

</details>

#### computes sum value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = MockTensor.create([1.0, 2.0, 3.0], [3])
expect(t.sum_val()).to_equal(6.0)
```

</details>

#### creates tensor with gradient tracking

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = MockTensor.create_with_grad([1.0, 2.0], [2])
expect(t.requires_grad).to_equal(true)
expect(t.grad_data.len()).to_equal(2)
```

</details>

#### creates tensor without gradient tracking

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = MockTensor.create([1.0, 2.0], [2])
expect(t.requires_grad).to_equal(false)
```

</details>

#### has string representation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = MockTensor.create([1.0], [1])
val s = t.to_string()
expect(s).to_contain("MockTensor")
```

</details>

### Linear Layer

#### creates linear layer with correct dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = MockLinear.create(3, 2)
expect(layer.in_features).to_equal(3)
expect(layer.out_features).to_equal(2)
```

</details>

#### initializes weights with correct count

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = MockLinear.create(4, 3)
expect(layer.weight_data.len()).to_equal(12)
```

</details>

#### initializes bias to zeros

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = MockLinear.create(3, 2)
expect(layer.bias_data[0]).to_equal(0.0)
expect(layer.bias_data[1]).to_equal(0.0)
```

</details>

#### computes forward pass

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = MockLinear.create(2, 1)
# weight = [0.1, 0.2], bias = [0.0]
val input = MockTensor.create([1.0, 1.0], [2])
val output = layer.forward(input)
# y = 1.0*0.1 + 1.0*0.2 + 0.0 = 0.3
expect(output.data[0]).to_be_greater_than(0.29)
expect(output.data[0]).to_be_less_than(0.31)
```

</details>

#### produces output with correct shape

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = MockLinear.create(3, 2)
val input = MockTensor.create([1.0, 2.0, 3.0], [3])
val output = layer.forward(input)
expect(output.shape).to_equal([2])
expect(output.data.len()).to_equal(2)
```

</details>

#### counts parameters correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = MockLinear.create(4, 3)
# weights: 4*3=12, bias: 3, total: 15
expect(layer.parameter_count()).to_equal(15)
```

</details>

#### has correct output values for known weights

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = MockLinear.create(2, 2)
# W = [[0.1, 0.2], [0.3, 0.4]], b = [0, 0]
val input = MockTensor.create([1.0, 0.0], [2])
val output = layer.forward(input)
# out[0] = 1.0*0.1 + 0.0*0.2 = 0.1
# out[1] = 1.0*0.3 + 0.0*0.4 = 0.3
expect(output.data[0]).to_be_greater_than(0.09)
expect(output.data[0]).to_be_less_than(0.11)
expect(output.data[1]).to_be_greater_than(0.29)
expect(output.data[1]).to_be_less_than(0.31)
```

</details>

#### has string representation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = MockLinear.create(3, 2)
val s = layer.to_string()
expect(s).to_contain("MockLinear")
```

</details>

### SGD Optimizer

#### creates optimizer with learning rate

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = MockSGD.create([1.0, 2.0], 0.01, 0.0)
expect(opt.lr).to_equal(0.01)
expect(opt.momentum).to_equal(0.0)
```

</details>

#### updates parameters with gradient step

1. opt step


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = MockSGD.create([1.0, 2.0], 0.1, 0.0)
opt.step([1.0, 1.0])
# param = param - lr * grad = [1.0 - 0.1, 2.0 - 0.1] = [0.9, 1.9]
expect(opt.get_param(0)).to_be_greater_than(0.89)
expect(opt.get_param(0)).to_be_less_than(0.91)
expect(opt.get_param(1)).to_be_greater_than(1.89)
expect(opt.get_param(1)).to_be_less_than(1.91)
```

</details>

#### updates with momentum

1. opt step
2. opt step


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = MockSGD.create([1.0], 0.1, 0.9)
# Step 1: vel = 0.9*0 + 0.1*1.0 = 0.1, param = 1.0 - 0.1 = 0.9
opt.step([1.0])
expect(opt.get_param(0)).to_be_greater_than(0.89)
expect(opt.get_param(0)).to_be_less_than(0.91)
# Step 2: vel = 0.9*0.1 + 0.1*1.0 = 0.19, param = 0.9 - 0.19 = 0.71
opt.step([1.0])
expect(opt.get_param(0)).to_be_greater_than(0.70)
expect(opt.get_param(0)).to_be_less_than(0.72)
```

</details>

#### applies zero gradient with no change

1. opt step
   - Expected: opt.get_param(0) equals `5.0`
   - Expected: opt.get_param(1) equals `3.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = MockSGD.create([5.0, 3.0], 0.1, 0.0)
opt.step([0.0, 0.0])
expect(opt.get_param(0)).to_equal(5.0)
expect(opt.get_param(1)).to_equal(3.0)
```

</details>

#### handles large learning rate

1. opt step
   - Expected: opt.get_param(0) equals `7.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = MockSGD.create([10.0], 1.0, 0.0)
opt.step([3.0])
# param = 10.0 - 1.0*3.0 = 7.0
expect(opt.get_param(0)).to_equal(7.0)
```

</details>

#### handles negative gradients

1. opt step


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = MockSGD.create([0.0], 0.1, 0.0)
opt.step([-2.0])
# param = 0.0 - 0.1*(-2.0) = 0.2
expect(opt.get_param(0)).to_be_greater_than(0.19)
expect(opt.get_param(0)).to_be_less_than(0.21)
```

</details>

#### zero_grad does not crash

1. opt zero grad
   - Expected: opt.lr equals `0.01`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = MockSGD.create([1.0], 0.01, 0.0)
opt.zero_grad()
expect(opt.lr).to_equal(0.01)
```

</details>

#### has string representation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = MockSGD.create([1.0], 0.01, 0.9)
val s = opt.to_string()
expect(s).to_contain("MockSGD")
```

</details>

### MSE Loss

#### creates loss function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loss_fn = MockMSELoss.create()
expect(loss_fn.reduction).to_equal("mean")
```

</details>

#### computes zero loss for identical inputs

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loss_fn = MockMSELoss.create()
val pred = MockTensor.create([1.0, 2.0, 3.0], [3])
val target = MockTensor.create([1.0, 2.0, 3.0], [3])
val loss = loss_fn.forward(pred, target)
expect(loss).to_equal(0.0)
```

</details>

#### computes correct MSE

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loss_fn = MockMSELoss.create()
val pred = MockTensor.create([1.0, 2.0], [2])
val target = MockTensor.create([2.0, 4.0], [2])
# MSE = ((1-2)^2 + (2-4)^2) / 2 = (1+4)/2 = 2.5
val loss = loss_fn.forward(pred, target)
expect(loss).to_equal(2.5)
```

</details>

#### computes loss for single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loss_fn = MockMSELoss.create()
val pred = MockTensor.create([3.0], [1])
val target = MockTensor.create([1.0], [1])
# MSE = (3-1)^2 / 1 = 4.0
val loss = loss_fn.forward(pred, target)
expect(loss).to_equal(4.0)
```

</details>

#### computes correct gradients

1. var grads = loss fn backward grad
   - Expected: grads[0] equals `2.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loss_fn = MockMSELoss.create()
val pred = MockTensor.create([2.0], [1])
val target = MockTensor.create([1.0], [1])
var grads = loss_fn.backward_grad(pred, target)
# grad = 2*(2-1)/1 = 2.0
expect(grads[0]).to_equal(2.0)
```

</details>

#### computes gradients for multi-element

1. var grads = loss fn backward grad
   - Expected: grads[0] equals `-1.0`
   - Expected: grads[1] equals `2.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loss_fn = MockMSELoss.create()
val pred = MockTensor.create([1.0, 3.0], [2])
val target = MockTensor.create([2.0, 1.0], [2])
var grads = loss_fn.backward_grad(pred, target)
# grad[0] = 2*(1-2)/2 = -1.0
# grad[1] = 2*(3-1)/2 = 2.0
expect(grads[0]).to_equal(-1.0)
expect(grads[1]).to_equal(2.0)
```

</details>

#### produces zero gradient for perfect predictions

1. var grads = loss fn backward grad
   - Expected: grads[0] equals `0.0`
   - Expected: grads[1] equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loss_fn = MockMSELoss.create()
val pred = MockTensor.create([5.0, 3.0], [2])
val target = MockTensor.create([5.0, 3.0], [2])
var grads = loss_fn.backward_grad(pred, target)
expect(grads[0]).to_equal(0.0)
expect(grads[1]).to_equal(0.0)
```

</details>

#### has string representation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loss_fn = MockMSELoss.create()
val s = loss_fn.to_string()
expect(s).to_contain("MockMSELoss")
```

</details>

### Training Loop

#### simulates a single training step

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Setup: simple linear function y = 2x
val layer = MockLinear.create(1, 1)
val loss_fn = MockMSELoss.create()
val opt = MockSGD.create(layer.weight_data, 0.01, 0.0)

# Input and target
val input = MockTensor.create([1.0], [1])
val target = MockTensor.create([2.0], [1])

# Forward pass
val output = layer.forward(input)
val loss = loss_fn.forward(output, target)

# Loss should be non-negative
expect(loss).to_be_greater_than(-0.01)
```

</details>

#### reduces loss over multiple steps

1. opt step
2. opt step


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loss_fn = MockMSELoss.create()
# Simulate param trying to reach target value 3.0
val opt = MockSGD.create([0.0], 0.1, 0.0)

# Step 1: pred=0, target=3, loss=9, grad=2*(0-3)/1=-6
val pred1 = MockTensor.create([opt.get_param(0)], [1])
val target = MockTensor.create([3.0], [1])
val loss1 = loss_fn.forward(pred1, target)
val grads1 = loss_fn.backward_grad(pred1, target)
opt.step(grads1)

# Step 2
val pred2 = MockTensor.create([opt.get_param(0)], [1])
val loss2 = loss_fn.forward(pred2, target)
val grads2 = loss_fn.backward_grad(pred2, target)
opt.step(grads2)

# Step 3
val pred3 = MockTensor.create([opt.get_param(0)], [1])
val loss3 = loss_fn.forward(pred3, target)

# Loss should decrease over training steps
expect(loss2).to_be_less_than(loss1)
expect(loss3).to_be_less_than(loss2)
```

</details>

#### converges toward target with enough steps

1. fn run training
2. var grads = loss fn backward grad
3. opt step
4. opt get param


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run_training() -> f64:
    val loss_fn = MockMSELoss.create()
    val opt = MockSGD.create([0.0], 0.05, 0.0)
    val target = MockTensor.create([2.0], [1])
    # Run 20 steps
    var step = 0
    while step < 20:
        val pred = MockTensor.create([opt.get_param(0)], [1])
        var grads = loss_fn.backward_grad(pred, target)
        opt.step(grads)
        step = step + 1
    opt.get_param(0)

# After 20 steps with lr=0.05, should be close to 2.0
val final_pred = run_training()
expect(final_pred).to_be_greater_than(1.5)
expect(final_pred).to_be_less_than(2.5)
```

</details>

#### computes end-to-end forward and backward

1. var grads = loss fn backward grad
   - Expected: grads.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = MockLinear.create(2, 1)
val loss_fn = MockMSELoss.create()

# Forward
val input = MockTensor.create([1.0, 2.0], [2])
val target = MockTensor.create([1.0], [1])
val output = layer.forward(input)
val loss = loss_fn.forward(output, target)

# Backward
var grads = loss_fn.backward_grad(output, target)

# Verify gradient shape matches output
expect(grads.len()).to_equal(1)
# Loss should be computable
expect(loss).to_be_greater_than(-0.01)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/torch/sffi_test_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SFFI Integration Tests
- Tensor Operations
- Linear Layer
- SGD Optimizer
- MSE Loss
- Training Loop

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 40 |
| Active scenarios | 40 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
