<<<<<<< Conflict 1 of 1
%%%%%%% Changes from base to side #1
+# Codegen Runtime Helper Reuse Crash
+
+Status: closed
+Date: 2026-06-11
+
+## Summary
+
+Reusing a Cranelift `CodegenBackend` across modules could leave the runtime
+helper map incomplete for later modules. The observed crash was:
+
+```text
+no entry found for key
+compiler/src/codegen/instr/basic_ops.rs:56
+```
+
+## Root Cause
+
+Runtime helper declarations were only populated when `runtime_funcs` was empty.
+If an earlier module initialized the backend without needing `rt_value_as_int`,
+a later module that did need `rt_value_as_int` reused the incomplete map.
+
+## Fix
+
+`ensure_runtime_functions_declared` now declares missing runtime helpers
+incrementally for each compile, so backend reuse cannot leave later module
+helpers undeclared.
+
+## Verification
+
+- `cargo test --manifest-path src/compiler_rust/Cargo.toml -p simple-compiler reused_backend_declares_runtime_helpers_needed_by_later_modules -- --nocapture`
+++++++ Contents of side #2
# Codegen Runtime Helper Reuse Crash

Status: closed
Date: 2026-06-11

## Summary

Reusing a Cranelift `CodegenBackend` across modules could crash during an
`Any` to integer cast with:

```text
no entry found for key
compiler/src/codegen/instr/basic_ops.rs:56
```

## Root Cause

Runtime helper declarations were only populated when `runtime_funcs` was empty.
If an earlier module initialized the backend without needing `rt_value_as_int`,
a later module that did need `rt_value_as_int` reused the incomplete map.
`compile_cast` then indexed `ctx.runtime_funcs["rt_value_as_int"]` and panicked.

## Fix

`ensure_runtime_functions_declared` now declares missing runtime helpers
incrementally for each compile. `compile_cast` also guards the lookup and
returns a normal codegen error if the helper is unexpectedly unavailable.

## Verification

- `cargo test --manifest-path src/compiler_rust/Cargo.toml -p simple-compiler reused_backend_declares_runtime_helpers_needed_by_later_modules -- --nocapture`
- `cargo test --manifest-path src/compiler_rust/Cargo.toml -p simple-compiler codegen::instr::basic_ops -- --nocapture`
>>>>>>> Conflict 1 of 1 ends
