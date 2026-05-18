# BUG: Codegen method-dispatch self-recursion

**Date:** 2026-05-18
**Severity:** High (silent stack overflow at runtime)
**Status:** Workaround applied; root cause unfixed

## Summary

When a module-level function `fn foo(s: text, ...) -> T` calls `s.foo(...)` (a
method with the same name as the function), Cranelift codegen resolves the method
call back to the enclosing function, causing infinite recursion and stack overflow.

## Reproduction

```spl
fn str_ends_with(s: text, suffix: text) -> bool:
    s.ends_with(suffix)   # resolves to str_ends_with(s, suffix) -> infinite loop
```

GDB backtrace shows 1500+ frames of `frontend.core.types.str_ends_with` calling
itself.

## Affected functions

Any free function whose name matches `str_<method>` and calls `s.<method>(...)`:
- `str_ends_with` -> `s.ends_with()`
- `str_starts_with` -> `s.starts_with()`
- `str_contains` -> `s.contains()`
- `str_index_of` -> `s.index_of()`
- `str_trim` -> `s.trim()`
- `str_replace` -> `s.replace()`
- `ends_with` (in text.spl) -> `s.ends_with()`

Also affects `last_index_of` in `src/lib/text.spl` (no runtime extern available).

## Root cause

The Cranelift backend's method-call lowering finds a module-level function whose
name suffix matches the method name and whose first parameter type matches the
receiver. It prefers this over the built-in method on the `text` type.

## Workaround applied

Replaced method calls with direct `rt_string_*` extern calls in:
- `src/compiler/10.frontend/core/types.spl` (6 functions)
- `src/lib/text.spl` (1 function)

## Proposed fix

Method-call resolution in the codegen layer should exclude the currently-compiling
function from candidates, or prioritize built-in type methods over module-level
free functions with matching signatures.

Relevant codegen: `src/compiler_rust/compiler/src/codegen/` (method dispatch logic).
