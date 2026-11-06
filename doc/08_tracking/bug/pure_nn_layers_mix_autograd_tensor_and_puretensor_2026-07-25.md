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

## 2026-11-05 first real execution + bounded backward fix (partial)

Session: `work/libbug-std-purenn-20261105` (worktree off `origin/release/1.0.0`).
Test CLI: phase-1 snapshot binary (Rust seed; `bin/simple` unavailable in the
worktree) on aarch64 Linux, both `--mode=interpreter` and default compiled
mode. Neighboring pure specs were baselined green before and after
(`tensor_spec` 27 pass / 3 skip, `tensor_ops_spec` 16 pass, `autograd_spec` and
`data_spec` 1 pass / 1 pending each — unchanged).

What the first real run of `pure/test/nn_spec.spl` showed:

1. The original type-surface symptom is resolved in this snapshot:
   `Linear`/`ReLU`/`Sigmoid`/`Tanh`/`Sequential` are uniformly autograd
   `Tensor`, `Linear.forward` runs, and 2/7 scenarios pass (batch-axis
   contract; frozen-operand no-graph contract).
2. `backward(tensor_sum(output))` crashed with
   `array index out of bounds: index is 1 but length is 1`. Root cause:
   `OpType.Sum`/`OpType.Mean` in `propagate_grads`
   (`src/lib/gc_async_mut/pure/autograd.spl`) passed the length-1 reduced
   gradient through unchanged to a multi-element input. Fixed by broadcasting
   the reduced gradient to the input shape (`broadcast_reduced_grad`). After
   the fix the crash is gone in both interpreter and compiled modes.
3. The remaining 5 scenarios fail with `unwrap() on None`: leaf gradients
   never reach caller-held tensors. Probed extensively (P1–P17): class
   instances are shared only through direct variables/parameters and `me`
   methods on them; list slots deep-copy class values at store time, class
   field reads copy, and closures capture by value. The autograd tape stores
   `inputs: [Tensor]`, so every `backward_step` during propagation mutates a
   throwaway copy and `layer.weight.grad` / `input.grad` stay `nil`. No
   std-lib-only redesign can bridge this: gradient write-back through a stored
   graph requires shared references the current runtime does not provide
   (`src/lib/gc_async_mut/pure/training.spl:627` already notes
   "backward(loss) call would go here when autograd is available"). This is a
   compiler/runtime semantics gap (aggregate slots copy), not fixable inside
   `std.pure.*`; recorded here so the parked suites are not re-diagnosed from
   scratch.

Status: remains OPEN. Sum/Mean backward broadcast fixed; leaf-gradient
propagation blocked on runtime shared-reference semantics.

## 2026-11-06 re-verification (lane fx-ml-db)

Seed `simple-ref`: `nn_spec` still 2/7. `nn.spl` already uses autograd `Tensor`
uniformly (no type mixing remains), so there is no layer-side change left to
make. Re-probed the 5 failures: class values stored in an array literal,
`push`, a class field, or an `Option` payload are copies (`val l = [a];
l[0].inc()` leaves `a` unchanged; direct parameter passing aliases). Hence
`tensor_linear`'s `inputs = [x, weight]` holds copies and
`propagate_linear_grads` writes grads to throwaways (`x.grad`/`weight.grad`
stay nil). No std-lib-only fix preserves the spec's `input.grad` contract;
needs runtime shared-reference semantics for stored class values. Status: OPEN,
runtime-blocked. Related: interp_list_class_element_read_returns_copy_mutation_loss_2026-08-17.md.

## 2026-11-06 re-verification (seed-class-reference lane): 7/7, runtime gap closed

Seed built from `origin/release/1.0.0` `f1390d48254` (worktree
`simple-seed-class-reference`): `src/lib/gc_async_mut/pure/test/nn_spec.spl`
is **7 passed / 0 failed** by default, and 2/7 (the 5 `unwrap() on None`
gradient cases) with `SIMPLE_INTERP_CLASS_REF=0`. The runtime shared-reference
semantics this record waited on landed as `6c7b4db3d39` ("fix(interp): class
reference semantics by default", merged to release/1.0.0 2026-11-04 via
`7e3b0244cc3`); the `simple-ref` binary used for the earlier 2026-11-06 note
predates it. `training_spec` 1 pass / 1 skip either way. No library change.
Owner decision 2026-11-06: classes are reference types everywhere, structs
are value types. Coordinator owns the bug_db status change.
