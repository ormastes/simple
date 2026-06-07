# Math Blocks Autograd Runtime

> Compiled-mode proof tests for m{}, loss{}, and nograd{} runtime semantics. Verifies that MIR lowering emits real runtime calls and the torch autograd backend produces correct gradient behavior, including scalar math evaluation, loss backward with automatic gradient computation, nograd gradient suppression, and loss/nograd interaction.

<!-- sdn-diagram:id=math_autograd_runtime_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=math_autograd_runtime_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

math_autograd_runtime_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=math_autograd_runtime_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Math Blocks Autograd Runtime

Compiled-mode proof tests for m{}, loss{}, and nograd{} runtime semantics. Verifies that MIR lowering emits real runtime calls and the torch autograd backend produces correct gradient behavior, including scalar math evaluation, loss backward with automatic gradient computation, nograd gradient suppression, and loss/nograd interaction.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | In Progress |
| Source | `test/03_system/feature/usage/math_autograd_runtime_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Compiled-mode proof tests for m{}, loss{}, and nograd{} runtime semantics. Verifies
that MIR lowering emits real runtime calls and the torch autograd backend produces
correct gradient behavior, including scalar math evaluation, loss backward with
automatic gradient computation, nograd gradient suppression, and loss/nograd interaction.

## Scenarios

### Math Blocks Autograd Runtime

### m{} evaluation

#### evaluates scalar math expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 3.0
val result = m{ x^2 + 1 }
expect(result).to_equal(10.0)
```

<details>
<summary>Rendered scenario source</summary>

> val x = 3.0<br>
> val result = $x^{2} + 1$<br>
> expect(result).to_equal(10.0)

</details>

</details>

#### evaluates with implicit multiplication

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 2.0
val y = 3.0
val result = m{ 2x + 3y }
expect(result).to_equal(13.0)
```

<details>
<summary>Rendered scenario source</summary>

> val x = 2.0<br>
> val y = 3.0<br>
> val result = $2$<br>
> expect(result).to_equal(13.0)

</details>

</details>

### loss{} backward semantics

#### simple quadratic loss

#### computes gradients on requires_grad parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = Tensor.from_data([2.0], requires_grad: true)
val target = Tensor.from_data([5.0])

val loss_val = loss{ (w - target)^2 }

# After loss{} exits, backward() has been called automatically.
# The gradient of (w - target)^2 w.r.t. w is 2*(w - target) = 2*(2-5) = -6
val grad = w.grad()
expect(grad.?.to_equal(true))
expect(grad.item()).to_equal(-6.0)
```

</details>

#### repeated loss evaluation

#### accumulates gradients across loss blocks

1. loss{
   - Expected: grad1 equals `2.0`
2. loss{
   - Expected: grad2 equals `4.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = Tensor.from_data([1.0], requires_grad: true)
val target = Tensor.from_data([0.0])

# First loss: grad = 2*(1-0) = 2.0
loss{ (w - target)^2 }
val grad1 = w.grad().item()
expect(grad1).to_equal(2.0)

# Second loss without zero_grad: grad accumulates
loss{ (w - target)^2 }
val grad2 = w.grad().item()
expect(grad2).to_equal(4.0)
```

</details>

#### detached input and escape-path restore

#### keeps detached values out of autograd and restores gradient tracking after escaped nograd

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = Tensor.from_data([2.0], requires_grad: true)
val detached = source.detach()
expect(detached.requires_grad()).to_equal(false)

val restore_w = Tensor.from_data([1.0], requires_grad: true)
val restore_x = Tensor.from_data([3.0], requires_grad: true)
val outcome = escaped_nograd(restore_w, restore_x)
match outcome:
    case Err(msg):
        expect(msg).to_equal("nograd escape")
    case Ok(_):
        expect(false)

val restored = restore_w * restore_x
expect(restored.requires_grad()).to_equal(true)
```

</details>

### nograd{} suppression semantics

#### basic suppression

#### prevents gradient recording

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = Tensor.from_data([3.0], requires_grad: true)
val x = Tensor.from_data([2.0])

val result = nograd{ w * x }

# Result should be computed (3*2 = 6)
expect(result.item()).to_equal(6.0)
# But no gradient graph was built
expect(result.requires_grad()).to_equal(false)
```

</details>

#### nesting

#### nested nograd does not leak state

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = Tensor.from_data([1.0], requires_grad: true)
val x = Tensor.from_data([2.0])

# Outer nograd
val outer = nograd{
    val inner = nograd{ w * x }
    inner + w
}
# After both nograd blocks exit, grad tracking is restored
# The result inside nograd should not require grad
expect(outer.requires_grad()).to_equal(false)

# But operations after nograd{} resume tracking
val tracked = w * x
expect(tracked.requires_grad()).to_equal(true)
```

</details>

### loss{} and nograd{} interaction

#### nograd inside loss

#### only tracks gradient-enabled parts

1.
   - Expected: w.grad().item() equals `-2.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = Tensor.from_data([2.0], requires_grad: true)
val bias = Tensor.from_data([1.0], requires_grad: true)
val target = Tensor.from_data([4.0])

# The nograd part does not contribute to gradient computation
# loss = (nograd{bias} + w - target)^2
# = (1 + 2 - 4)^2 = 1.0
# d(loss)/dw = 2*(1+2-4) = -2
# d(loss)/dbias = 0 (bias inside nograd, detached)
val loss_val = loss{
    val const_part = nograd{ bias }
    (const_part + w - target)^2
}

expect(w.grad().item()).to_equal(-2.0)
# bias gradient should be nil or zero (not tracked through nograd)
```

</details>

#### loss after nograd

#### resumes normal gradient behavior

1. loss{
   - Expected: grad.item() equals `4.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = Tensor.from_data([3.0], requires_grad: true)
val target = Tensor.from_data([1.0])

# nograd block — no gradient ops
val _ = nograd{ w * w }

# loss block after nograd — should work normally
loss{ (w - target)^2 }

# grad = 2*(3-1) = 4.0
val grad = w.grad()
expect(grad.?.to_equal(true))
expect(grad.item()).to_equal(4.0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
