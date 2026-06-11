# Codegen Runtime Helper Reuse Crash

Status: closed
Date: 2026-06-11

## Summary

Reusing a Cranelift `CodegenBackend` across modules could leave the runtime
helper map incomplete for later modules. The observed crash was:

```text
no entry found for key
compiler/src/codegen/instr/basic_ops.rs:56
```

## Root Cause

Runtime helper declarations were only populated when `runtime_funcs` was empty.
If an earlier module initialized the backend without needing `rt_value_as_int`,
a later module that did need `rt_value_as_int` reused the incomplete map.

## Fix

`ensure_runtime_functions_declared` now declares missing runtime helpers
incrementally for each compile, so backend reuse cannot leave later module
helpers undeclared.

## Verification

- `cargo test --manifest-path src/compiler_rust/Cargo.toml -p simple-compiler reused_backend_declares_runtime_helpers_needed_by_later_modules -- --nocapture`
