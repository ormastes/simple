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

## 2026-11-03 bounded source candidate (not resolved)

Claim session: `p2-nn-tensor-20261103`. `Linear` now owns trainable autograd
`Tensor` parameters and delegates to a tracked affine operation. The operation
preserves every leading batch dimension and the vector case, validates the
contract, and propagates input, weight and batch-reduced bias gradients.
`ReLU`, `Sigmoid`, `Tanh` and `Sequential` retain that graph. Parameter counting
uses `numel()` and gradient clearing uses the Tensor owner. The previously
missing `tensor_f64_ops` owner delegates value operations below the tape to
existing raw kernels; no Tensor-to-PureTensor conversion crosses a tape node.

The seven exact/adjacent scenarios in `pure/test/nn_spec.spl` assert values,
batch shapes, all three derivatives, nonlinear chains, frozen operands, empty
batches, repeated backward accumulation, parameter enumeration and clearing.
These replace the former bridge tests which detached gradients and weakened the
original `[1, 2]` expected output to `[2]`.

**TEST_BLOCKED:** no admitted pure-Simple self-hosted CLI is available. The
tracked `bin/simple.exe` is a prohibited Rust seed for ordinary verification.
Authored scenarios have not executed; no behavioral PASS or positive test count
is claimed. Required core/lib/MCP/LSP checks and runtime/native smoke remain
unrun. This candidate must remain a draft until those gates run.

The umbrella remains OPEN: Conv2d, pooling, BatchNorm1d, LayerNorm, Embedding,
Softmax, Dropout, LeakyReLU, ELU and GELU still use raw values. They must not be
silently bridged into tracked Sequential. Their graph-aware migration is not
included in this bounded candidate. The broad parked training suite is not
unparked or represented as passing.
