# Module Loader Resolve Vec i64

**Date:** 2026-04-22
**Todo:** `doc/08_tracking/todo/todo_db.sdn` row 176
**Status:** Closed

## Research

- `resolve_generic()` mangles type arguments with `type_to_string()` and routes to `resolve_symbol()`.
- `make_named_type("i64")` formats as `i64`, so `Vec<i64>` maps to the mangled name `Vec$i64`.
- The existing spec checked generic mangling for an unresolved multi-arg type, but not successful `Vec<i64>` resolution.

## Plan

- Add JIT metadata for `Vec$i64`.
- Resolve `Vec` with `[make_named_type("i64")]` through `resolve_generic()`.
- Assert the result is `SymbolResult.JitCompiled`, the global symbol table contains `Vec$i64`, and the JIT compile count increments once.
- Close row 176 after lint and focused spec verification.

## Fix

- Added a successful `Vec<i64>` generic resolution test to `module_loader_spec.spl`.
- Closed `todo_db.sdn` row 176.

## Verification

```sh
bin/simple lint test/unit/compiler/loader/module_loader_spec.spl
bin/simple test test/unit/compiler/loader/module_loader_spec.spl
```
