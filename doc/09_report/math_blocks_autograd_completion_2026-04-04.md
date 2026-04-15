# Math Blocks Autograd Completion Report

**Date:** 2026-04-04
**Feature:** Math Blocks (m{}, loss{}, nograd{}) Autograd Pipeline
**Support Matrix:** [doc/04_architecture/math_blocks_backend_support_matrix.md](../04_architecture/math_blocks_backend_support_matrix.md)

## Summary

Math blocks autograd is **implemented for the promoted torch-backed backend scope**.

The compiler now provides:
- `m{}` math expression blocks with operator overloading for tensor types
- `loss{}` blocks with automatic backward pass (calls `rt_torch_autograd_backward`)
- `nograd{}` blocks with gradient suppression (begin/end with escape-path cleanup)
- Function-level `no_grad(callback)` API across all three runtime families
- Parser -> HIR -> MIR lowering -> C/LLVM codegen -> FFI runtime pipeline for the promoted torch-backed lanes
- MIR rejection for `loss{}` bodies that lower to no value

## Implementation

### MIR Lowering (compiler)
- `lower_loss_block()` in `mir_lowering_ml.spl` evaluates the body (loss expression),
  emits `rt_torch_autograd_backward(handle)`, and returns the loss value.
- `lower_nograd_block()` in `mir_lowering_ml.spl` emits `rt_torch_autograd_no_grad_begin()`,
  lowers the body, then emits `rt_torch_autograd_no_grad_end()`. Escape paths
  (early return, break, continue) are patched with cleanup calls. The runtime
  maintains an internal counter for nested nograd scopes.
- `mir_lowering_expr.spl` dispatches `LossBlock` and `NogradBlock` variants to the
  ML lowering methods.

### Block Definition System (compiler)
- `BlockValue` enum in `blocks/value.spl` defines `LossBlock(block: Any)` and
  `NogradBlock(block: Any)` variants alongside the existing `Expr` variant for `m{}`.

### Runtime FFI
- `torch_ffi.h` declares: `rt_torch_autograd_backward`, `rt_torch_autograd_no_grad_begin`,
  `rt_torch_autograd_no_grad_end`
- `torch_ffi.cpp` implements these using libtorch C++ API

### Standard Library (no_grad function-level API)
- `nogc_sync_mut/torch/torch_training.spl` -- full implementation with `NogradGuard`
  RAII struct (enter/drop pattern) and `no_grad(callback)` wrapper
- `gc_async_mut/torch/torch_training.spl` -- updated from placeholder to real FFI
  calls (`rt_torch_autograd_no_grad_begin/end`)
- `nogc_async_mut/torch/torch_training.spl` -- updated from placeholder to real FFI
  calls (`rt_torch_autograd_no_grad_begin/end`)

## Files Changed

### Modified (2)
| File | Change |
|------|--------|
| `src/lib/gc_async_mut/torch/torch_training.spl` | `no_grad()` placeholder -> real FFI begin/end calls, added imports |
| `src/lib/nogc_async_mut/torch/torch_training.spl` | `no_grad()` placeholder -> real FFI begin/end calls, added imports |

### Created (2)
| File | Purpose |
|------|---------|
| `doc/04_architecture/math_blocks_backend_support_matrix.md` | Backend support matrix |
| `doc/09_report/math_blocks_autograd_completion_2026-04-04.md` | This completion report |

### Pre-existing Key Files (unchanged)
| File | Role |
|------|------|
| `src/compiler/50.mir/mir_lowering_ml.spl` | lower_loss_block (backward call), lower_nograd_block (begin/end + escape cleanup) |
| `src/compiler/15.blocks/blocks/value.spl` | BlockValue enum with LossBlock/NogradBlock |
| `src/compiler/50.mir/mir_lowering_expr.spl` | Dispatch to lowering methods |
| `src/runtime/torch_ffi.h` | FFI declarations |
| `src/runtime/torch_ffi.cpp` | rt_torch_autograd_backward, no_grad_begin/end implementations |
| `src/lib/gc_async_mut/torch/mod.spl` | backward(), requires_grad(), zero_grad(), detach() |
| `src/lib/nogc_sync_mut/torch/torch_training.spl` | NogradGuard RAII + no_grad() (already complete) |

## Tests

| File | Tests | Coverage |
|------|-------|----------|
| `test/feature/usage/math_blocks_spec.spl` | 28 | m{} evaluation, operator precedence, nested blocks |
| `test/feature/usage/loss_nograd_blocks_spec.spl` | 27 | loss{}/nograd{} parsing, lowering, rendering parity |
| `test/feature/usage/math_autograd_runtime_spec.spl` | 9 | Real autograd semantics: backward, gradient flow, detached negative case, no_grad escape cleanup |

**Total: 64 tests** covering the promoted math blocks autograd pipeline.

## Known Limitations

- Cranelift, WASM, and CUDA backends do not support loss{}/nograd{} yet (deferred)
- Many torch operations beyond basic autograd (Conv2d, BatchNorm, Dropout, etc.)
  remain stubs requiring FFI extension
- `set_seed()`/`manual_seed()` are no-ops pending `rt_torch_manual_seed` FFI
- The `gc_async_mut` and `nogc_async_mut` `no_grad()` functions use direct
  begin/end calls rather than RAII guard -- panics during the callback will
  not restore gradient state (same limitation as the `nograd{}` block MIR lowering
  documents for unrecoverable panics)
