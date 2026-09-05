# `std.pure.nn` layers mix the autograd `Tensor` and the raw `PureTensor`

- **Date:** 2026-07-25
- **Area:** `src/lib/gc_async_mut/pure/nn.spl` /
  `src/lib/gc_async_mut/pure/autograd.spl`
- **Severity:** high — `Linear.forward()` cannot be called at all.
- **Status:** OPEN. Newly *visible* (not newly introduced): it was masked until
  2026-07-25 by the `src/lib/pure/*` stub facades, which meant nothing could
  reach these layers to begin with. See
  `doc/08_tracking/bug/pure_module_stub_facades_shadow_real_impl_2026-07-25.md`.

## Symptom

```
use std.pure.autograd (Tensor, backward, tensor_mean)
use std.pure.nn (Linear)

it "Linear weight shape":
    val l = Linear.create(10, 5, bias: true)
    assert_equal(l.weight.shape(), [5, 10])

it "forward pass":
    val l = Linear.create(3, 2, bias: true)
    val i = Tensor.from_data([1.0, 2.0, 3.0], [1, 3], requires_grad: false)
    assert_equal(l.forward(i).shape(), [1, 2])
```

```
✓ Tensor.from_data static
✓ Linear.create static
✗ Linear weight shape
    semantic: method `shape` not found on type `PureTensor`
✗ forward pass
    semantic: class `Tensor` has no field named `data`
```

## Analysis

Two distinct type-surface mismatches:

1. `Linear.weight` is a raw `PureTensor`, but callers (and
   `pure/test/nn_spec.spl`) expect the autograd `Tensor`, which is the type
   that exposes `.shape()`. `PureTensor` exposes a `shape` *field* and a
   `numel()` method, but no `shape()` accessor.
2. `Linear.forward()` accepts an autograd `Tensor` and then reads `.data` off
   it. `Tensor` has no `data` field — that is `PureTensor`'s field. So the
   forward path is written against `PureTensor` while its callers pass
   `Tensor`.

## Blocks

`src/lib/gc_async_mut/pure/test/nn_spec.spl` and
`src/lib/gc_async_mut/pure/test/training_spec.spl` remain parked on this — both
build models out of `Linear`/`Sequential` and run forward/backward.

## Fix direction (not attempted here)

Decide one owner for layer parameters — almost certainly the autograd `Tensor`,
since layers need gradients — then make `Linear`/`Conv2d`/`BatchNorm1d`/etc.
store `Tensor` parameters and route their forward passes through the autograd
ops in `std.pure.autograd` rather than the raw ops in `std.pure.tensor_ops`.
Adding a `shape()` accessor to `PureTensor` alone would not fix the
`forward()` failure.
