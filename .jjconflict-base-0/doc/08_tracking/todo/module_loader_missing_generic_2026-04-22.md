# Module Loader Missing Generic

**Date:** 2026-04-22
**Todo:** `doc/08_tracking/todo/todo_db.sdn` row 174
**Status:** Closed

## Research

- `ModuleLoader.with_defaults()` enables JIT by default.
- `resolve_generic()` mangles generic type arguments and resolves the mangled name through the public symbol API.
- The existing spec checked the unresolved mangled name, but did not assert that JIT was enabled or that a missing generic leaves symbol and JIT caches unchanged.

## Plan

- Extend the unresolved generic test instead of adding a separate setup.
- Assert JIT is enabled before resolving `Vec<Int, String>`.
- Assert the missing generic returns `NotFound("Vec$Int_String")`.
- Assert no global symbol, compile count, cached count, or symbol count is created.
- Close row 174 after focused lint and spec verification.

## Fix

- Added missing-generic no-side-effect assertions to `module_loader_spec.spl`.
- Closed `todo_db.sdn` row 174.

## Verification

```sh
bin/simple lint test/unit/compiler/loader/module_loader_spec.spl
bin/simple test test/unit/compiler/loader/module_loader_spec.spl
```
