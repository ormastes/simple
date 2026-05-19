# State: method-dispatch-recursion fix

**Status:** DONE — fix implemented, not yet bootstrap-deployed.

## Bug

`codegen_method_dispatch_self_recursion_2026-05-18.md`: when a free function
`fn foo(s: text, ...)` emits `MethodCallStatic` with bare `func_name = "foo"`,
`compile_method_call_static` in `closures_structs.rs` called
`ctx.func_ids.get("foo")` and received the `FuncId` of the currently-compiling
function itself → infinite recursion at runtime (GDB: 1500+ self-call frames).

## Root cause

`compile_method_call_static` (Cranelift backend, Rust seed) had no self-exclusion
on the **exact-match** path (lines 251-254 pre-fix). The suffix-scan path
(lines 285-298) already excluded the current function, but the prior `get(lookup_name)`
call could silently resolve `"ends_with"` → FuncId of `ends_with`, etc.

The self-hosted compiler (`src/compiler/`) resolves methods at HIR type-inference
time (MethodResolution enum), not in the Cranelift backend, so this specific
path does not exist there. No parallel fix needed.

## Fix applied

### `src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs`

Added `is_self()` closure before the `func_id` chain. The exact-match
`func_ids.get(lookup_name)` and `func_ids.get(&sanitized_name)` now carry a
`.filter(|_| !is_self(lookup_name))` guard that rejects any candidate whose key
matches the currently-compiling function (raw name, sanitized `_dot_` form, or
`module__name` mangled suffix).

This is the narrowest fix — it leaves the suffix-scan path and cross-module
fallback untouched. The existing suffix-scan self-exclusion (the `current_fn_tail_dot`
/ `current_fn_tail_sanitized` filter) is preserved.

### `src/lib/text.spl`

`last_index_of` still called `s.last_index_of(needle)` (not yet fixed by the
prior workaround wave). Changed to call `rt_string_rfind` directly, consistent
with the `ends_with` pattern. Added `extern fn rt_string_rfind` declaration.

## Workarounds already in place (left untouched)

In `src/compiler/10.frontend/core/types.spl` (6 functions) and `src/lib/text.spl::ends_with`,
the prior workaround of calling `rt_string_*` externs directly is preserved.
Those workarounds are now redundant for calls inside those modules, but they are
harmless and not reverted in this commit.

## Follow-up

- Bootstrap rebuild needed to deploy fix to `bin/release/simple` (self-hosted binary).
  Run `scripts/bootstrap/bootstrap-from-scratch.sh --deploy` after all externs land.
- Verify: restore `s.last_index_of(needle)` in `text.spl` and run a smoke test
  to confirm no stack-overflow; then re-apply the extern call.
