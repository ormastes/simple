# Module Loader Global Symbol Cache

**Date:** 2026-04-22
**Todo:** `doc/08_tracking/todo/todo_db.sdn` row 178
**Status:** Closed

## Research

- `test/unit/compiler/loader/module_loader_spec.spl` already verifies that resolving `vec_runtime_i64` can JIT-compile a symbol.
- `ModuleLoader.resolve_symbol()` stores JIT-compiled symbols in `global_symbols` before returning `SymbolResult.JitCompiled`.
- The missing assertion was that the mangled name is present in `global_symbols` and a subsequent lookup uses the global cache.

## Plan

- Extend the existing JIT-backed symbol test rather than adding a separate setup.
- Assert `loader.global_symbols.contains_key("vec_runtime_i64")` after first resolution.
- Resolve the same symbol again and require `SymbolResult.Found` with empty code payload.
- Close row 178 after lint and focused spec verification.

## Fix

- Added global-symbol table and cache-hit assertions to `module_loader_spec.spl`.
- Closed `todo_db.sdn` row 178.

## Verification

```sh
bin/simple lint test/unit/compiler/loader/module_loader_spec.spl
bin/simple test test/unit/compiler/loader/module_loader_spec.spl
```
