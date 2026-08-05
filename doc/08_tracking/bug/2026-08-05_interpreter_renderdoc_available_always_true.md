# `rt_renderdoc_available()` lies `true` under the interpreter (out of N2 scope)

- **Date:** 2026-08-05
- **Status:** OPEN (filed, not fixed -- outside `dlopen_conversion_lanes.md` Lane N2's owns-list)
- **Severity:** Medium — one honesty-contract symbol out of ten, interpreter engine only
- **Area:** `src/compiler_rust/compiler/src/interpreter_extern/gpu.rs` (`renderdoc_dlopen` module)

## Summary

`rt_renderdoc_available_fn` (gpu.rs:4845-4852) reports RenderDoc as available
whenever `renderdoc_dlopen::num_captures() != u32::MAX`:

```rust
pub fn rt_renderdoc_available_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(if renderdoc_dlopen::num_captures() != u32::MAX {
        1
    } else {
        0
    }))
}
```

But `renderdoc_dlopen::num_captures()` (gpu.rs:4831-4842) returns the plain
default `0` — not `u32::MAX` — whenever the RenderDoc API failed to resolve:

```rust
pub fn num_captures() -> u32 {
    if let Some(api) = api_ptr() {
        unsafe { /* ... call the real GetNumCaptures ... */ }
    }
    0
}
```

So on any host without a resident RenderDoc (i.e. the normal case, including
this dev host), `num_captures()` is `0`, `0 != u32::MAX` is `true`, and
`rt_renderdoc_available()` reports **1 (available)** even though
`RENDERDOC_GetAPI` was never resolved. Confirmed empirically:

```
$ SIMPLE_EXECUTION_MODE=interpret bin/simple test test/01_unit/runtime/renderdoc_honesty_spec.spl --no-cache --no-cover-check
✗ rt_renderdoc_available reports 0 -- RENDERDOC_GetAPI never resolved here
    expected 1 to equal 0
```

## Scope note

Discovered while implementing Task #62 Lane N2
(`doc/03_plan/runtime/native_binding/dlopen_conversion_lanes.md`), which adds
the honest, dlopen-based `rt_renderdoc_*` C shim
(`src/runtime/runtime_renderdoc.c`) for the native/compiled-code path. That
shim's `rt_renderdoc_available()` is correctly honest (verified via
`native-build`, sabotage-tested). This bug is in a **separate** code path
(the Rust interpreter's own dlopen-based `renderdoc_dlopen` module in
`gpu.rs`, used only when the tree-walk interpreter executes the extern call)
that Lane N2's owns-list does not include, so it is filed here rather than
fixed inline.

## Suggested fix

Expose a small `pub fn available() -> bool { api_ptr().is_some() }` in the
`renderdoc_dlopen` module and have `rt_renderdoc_available_fn` use it instead
of the `num_captures() != u32::MAX` sentinel comparison. Requires a Rust seed
rebuild (`cargo build`) to take effect in `bin/simple test`'s interpreter
engine — not done here per `.claude/rules/bootstrap.md` ("no bootstrap unless
essential"; budget rebuilds deliberately rather than as a side effect of an
unrelated lane).

## Evidence

- `test/01_unit/runtime/renderdoc_honesty_spec.spl` — the "available reports
  0" example is RED against the deployed seed today; all seven other
  `rt_renderdoc_*` honesty examples pass under the interpreter (they don't
  route through the buggy comparison).
