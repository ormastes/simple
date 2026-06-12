# Multicore Green Handle Array Join Native Blocker

Date: 2026-06-11
Status: closed
Owner: multicore-green lane

## Summary

Closed. Hosted-native code now keeps the reduced helper path native and returns
the expected worker result:

- a helper creates `var handles = []`
- it appends `multicore_green_spawn(worker)`
- it iterates `for handle in handles`
- it calls `handle.join()`
- native run prints `result=7`
- native exit is `0`

The root cause was seed-side, not Pure Simple API design. `var handles = []`
was inferred with the default empty-array element type, so later indexed or
iterated values could lose the appended handle type. The helper also crossed an
obsolete compilability gate that forced non-range collection `for` loops through
`InterpCall` even though MIR/codegen supports array iteration.

## Fix

- HIR lowering refines a local zero-length inferred array when `append(x)` or
  `push(x)` is first seen, changing the local element type to `type(x)`.
- Compilability no longer blanket-fallbacks non-range `for` loops to the
  interpreter; nested unsupported constructs are still analyzed normally.
- Cranelift struct values now use the same tagged heap-object ABI as LLVM, and
  Cranelift field get/set masks the heap tag before field access.

## Executable Evidence

- `test/03_system/feature/usage/multicore_green_handle_array_join_native_blocker_spec.spl`
- `cargo test -p simple-compiler test_empty_array_append_refines_indexed_element_type -- --nocapture`
- `cargo test -p simple-compiler test_empty_handle_array_for_join_helper_compilable -- --nocapture`
- `cargo test -p simple-compiler test_function_value_loop_return_helper_compilable -- --nocapture`
