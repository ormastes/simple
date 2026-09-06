# `src/lib/pure/*` stub facades shadowed the real `pure` implementations

- **Date:** 2026-07-25
- **Area:** module resolution / `src/lib/pure/` vs `src/lib/gc_async_mut/pure/`
- **Severity:** high — shipped code silently bound to no-op placeholders.
- **Status:** FIXED for tensor / tensor_ops / autograd / training (this change).
  Remaining follow-on defects tracked separately.

## What was wrong

`src/std` is a symlink to `lib`, so `use std.pure.X` resolves to
`src/lib/pure/X.spl`. Four files there were **stubs** that shadowed the real,
complete implementations in `src/lib/gc_async_mut/pure/`:

| module | stub | real |
|---|---|---|
| `tensor` | 14 lines, `PureTensor` with no strides / no `get`/`set`/`numel` | 166 lines |
| `tensor_ops` | 16 lines, only `tensor_sum`, `tensor_mul_scalar` | 340 lines |
| `autograd` | 5 lines, a field-only `Variable`, **no `Tensor`** | full autograd |
| `training` | 36 lines of placeholders | 650 lines |

The `training` stub is the worst of them — these are the shipped bodies:

```
fn mse_loss(pred: any, target: any) -> f64:  0.0
fn train_step(batch_x: any, batch_y: any) -> f64:  0.0
class SGD:  fn zero_grad(): ()   fn step(): ()
class Adam: fn zero_grad(): ()   fn step(): ()
```

## Impact on shipped (non-test) code

- `src/lib/nogc_async_mut/ml/async_training.spl:6` imports
  `std.pure.training.{mse_loss, SGD, Adam, TrainingHistory}` — it was training
  with a no-op optimiser and a loss that always reported `0.0`.
- `src/lib/gc_async_mut/pure/training.spl:11` does `use std.pure.autograd
  (Tensor)`, but the autograd stub exported no `Tensor` at all.
- `src/lib/gc_async_mut/pure/{tensor_ops,training,nn}.spl` all import
  `std.pure.tensor` / `std.pure.tensor_ops`, so the real implementations were
  wired to the stubs rather than to each other.

## Impact on tests

It is the root cause of the note
"pre-existing test failures - functions/imports not available" that had all six
`src/lib/gc_async_mut/pure/test/*_spec.spl` files commented out wholesale.
Those files did not even skip cleanly — they called `skip(...)`/`pending(...)`
without importing `std.spec`, so they **failed** with
"semantic: function `skip` not found".

## Evidence

```
use std.pure.tensor.{PureTensor, compute_strides, tensor_zeros}
✗ semantic: function `compute_strides` not found
✗ semantic: function `tensor_zeros` not found
✗ semantic: method `get` not found on type `PureTensor`
```
versus the identical probe against `std.gc_async_mut.pure.tensor`: 4/4 pass.

After converting the four stubs to real re-export facades:

```
bin/simple test src/lib/gc_async_mut/pure/test/tensor_spec.spl
Results: 30 total, 30 passed, 0 failed
bin/simple test src/lib/gc_async_mut/pure/test/tensor_ops_spec.spl
Results: 16 total, 16 passed, 0 failed
```

and `mse_loss` now returns a real MSE (1.333… for `[1,2,3]` vs `[1,2,5]`)
instead of the stub's constant `0.0`.

## Follow-ups still open

- `doc/08_tracking/bug/pure_nn_layers_mix_autograd_tensor_and_puretensor_2026-07-25.md`
  — blocks `nn_spec.spl` and `training_spec.spl`.
- `src/lib/pure/data/` still contains a second copy of `dataset.spl` /
  `dataloader.spl` alongside `src/lib/gc_async_mut/pure/data/`. Not converted
  here because `test/01_unit/lib/pure/data/dataset_bounds_spec.spl` passes
  against the current resolution and the two copies were not diffed.
- `src/lib/gc_async_mut/pure/data.spl` exports only `normalize`/`standardize`;
  `pure/test/data_spec.spl` additionally needs `one_hot_encode`, `IrisDataset`,
  `MNISTDataset`, `BatchIterator`, `create_xor_dataset`,
  `create_linear_dataset`, and a 3-argument `normalize(data, min, max)` — none
  of which exist. That is new feature work, not a shadowing problem.
