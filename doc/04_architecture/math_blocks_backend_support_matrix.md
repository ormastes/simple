# Math Blocks Backend Support Matrix

**Date:** 2026-04-04
**Feature:** Math Blocks (m{}, loss{}, nograd{}) Autograd Pipeline
**Related:** [math_blocks_runtime_contract.md](math_blocks_runtime_contract.md)

## Overview

Math blocks are domain-specific block expressions for ML/tensor workloads.
The compiler pipeline is: Parser -> BlockValue -> HIR -> MIR lowering -> Backend codegen.

- `m{}` lowers to a standard expression (BlockValue::Expr) -- no special backend support needed.
- `loss{}` lowers to MIR that calls `rt_torch_autograd_backward()` after evaluating the body.
- `nograd{}` lowers to MIR that wraps the body in `rt_torch_autograd_no_grad_begin()`/`end()` with escape-path cleanup.

Since `loss{}` and `nograd{}` lower to standard extern FFI calls in MIR, any backend
that handles extern function calls supports them.

## Support Matrix

| Block | Interpreter | C Backend | LLVM Backend | Cranelift | WASM | CUDA |
|-------|-------------|-----------|--------------|-----------|------|------|
| `m{}` | Implemented | Implemented | Implemented | Implemented | Deferred | Deferred |
| `loss{}` | Implemented | Implemented (backward call) | Implemented (backward call) | Deferred | Deferred | Deferred |
| `nograd{}` | Implemented | Implemented (begin/end) | Implemented (begin/end) | Deferred | Deferred | Deferred |

### Legend

- **Implemented** -- Block is parsed, lowered to MIR, and the backend emits working code.
  The runtime FFI (`torch_ffi.cpp`) provides the native implementations.
- **Deferred** -- Block parsing and MIR lowering work, but the backend does not yet
  link against the torch FFI runtime or the platform is not yet supported.

## Backend Details

### Interpreter (95.interp)
- `m{}` evaluates as a normal expression via the MIR interpreter.
- `loss{}`/`nograd{}` MIR instructions are interpreted; FFI calls go through the
  runtime's dynamic dispatch.

### C Backend (70.backend)
- All three blocks emit standard C function calls to the `rt_torch_*` FFI functions.
- The generated C source links against `torch_ffi.cpp` at native-build time.

### LLVM Backend (70.backend)
- MIR is lowered to LLVM IR. Extern calls to `rt_torch_*` are emitted as
  standard LLVM `call` instructions with C calling convention.
- Linked against `torch_ffi.cpp` via the linker.

### Cranelift (Rust bootstrap)
- The Rust bootstrap compiler uses Cranelift for JIT. Math expression (`m{}`)
  support depends on operator lowering, which is functional.
- `loss{}`/`nograd{}` require torch FFI linkage, which is not wired in the
  bootstrap Cranelift backend. These blocks are deferred until the self-hosted
  compiler is used for ML workloads.

### WASM / CUDA
- Not yet targeted. WASM would need a WASI-compatible torch shim.
- CUDA backend focuses on kernel codegen; autograd is host-side and would
  use the C or LLVM backend for the host portion.

## Key Files

| File | Role |
|------|------|
| `src/compiler/15.blocks/blocks/value.spl` | BlockValue enum (LossBlock, NogradBlock) |
| `src/compiler/50.mir/mir_lowering_ml.spl` | MIR lowering: lower_loss_block, lower_nograd_block |
| `src/compiler/50.mir/mir_lowering_expr.spl` | Dispatch to ML lowering methods |
| `src/runtime/torch_ffi.h` | FFI declarations |
| `src/runtime/torch_ffi.cpp` | FFI implementations (backward, no_grad_begin/end) |
