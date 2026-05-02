# Module Loader JIT Cache Hit

**Date:** 2026-04-22
**Todo:** `doc/08_tracking/todo/todo_db.sdn` row 175
**Status:** Closed

## Research

- `module_loader_spec.spl` already resolves `vec_runtime_i64` twice.
- First resolution returns `SymbolResult.JitCompiled` and inserts the symbol into `global_symbols`.
- Second resolution returns `SymbolResult.Found`, but the spec did not assert that the JIT compile count stayed stable.

## Plan

- Extend the existing JIT-backed symbol test.
- Require `loader.jit.stats().compile_count == 1` after the second lookup.
- Require `loader.jit.stats().cached_count == 1` to prove the JIT cache contains one compiled symbol.
- Close row 175 after lint and focused spec verification.

## Fix

- Added JIT compile/cache count assertions to `module_loader_spec.spl`.
- Closed `todo_db.sdn` row 175.

## Verification

```sh
bin/simple lint test/unit/compiler/loader/module_loader_spec.spl
bin/simple test test/unit/compiler/loader/module_loader_spec.spl
```
