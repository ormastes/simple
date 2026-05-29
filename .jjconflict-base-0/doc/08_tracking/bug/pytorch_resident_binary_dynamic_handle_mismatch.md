# PyTorch Resident Binary Dynamic Handle Mismatch

Date: 2026-05-05
Status: Resolved in the exposed `TorchNDArray` binary surface.

## Summary

`TorchNDArray` resident subtraction, multiplication, and division were not exposed through `std.linalg` because an earlier Simple interpreter dynamic-call path produced inconsistent tensor handles after successful C++ execution.

The focused repro was rerun with fresh owners per resident binary operation. `TorchNDArray.sub_f64`, `mul_f64`, and `div_f64` now pass both no-shim fallback and available-shim PyTorch interpreter specs.

## Evidence

- Direct `ctypes` calls against `build/scilib/libspl_torch.so` verified `rt_dyn_torch_tensor_binary_op(handle, other, op)` returns correct add/sub/mul/div tensor contents.
- The focused Simple spec now uses independent `TorchNDArray` owners for sub, mul, and div, then checks both explicit host copies and resident scalar reductions.
- `SIMPLE_BLAS_BACKEND=mock bin/simple test test/feature/scilib/linalg_torch_backend_spec.spl --mode=interpreter --no-cache` passed: 22 examples, 0 failures.
- `SIMPLE_SFFI_PATH=build/scilib SIMPLE_BLAS_BACKEND=pytorch bin/simple test test/feature/scilib/linalg_torch_backend_spec.spl --mode=interpreter --no-cache` passed: 22 examples, 0 failures.

## Remaining Follow-Up

Do not reuse this issue as evidence for broad PyTorch backend completion. Zero-copy/DLPack ownership, CUDA tensor routing, and a general ndarray backend selector remain separate Phase C gaps.
