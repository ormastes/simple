# Codegen Runtime Helper Reuse Crash

## Closed 2026-09-13 — already fixed; entry self-records the repair

- **inferred** Entry's own `Status: closed` line plus its recorded fix stands unchallenged;
  no later June-September entry reopens the runtime-helper-reuse crash.
- **measured** The Rust seed built from this tree (`bin/simple --version` → v1.0.0-rc.1)
  runs codegen repros (function-value array, brace literal, List generics) without the
  helper-reuse crash signature.


Status: closed 2026-09-13 (was: Status: closed)
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
