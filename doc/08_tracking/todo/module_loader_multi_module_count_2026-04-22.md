# Module Loader Multi-Module Count

**Date:** 2026-04-22
**Todo:** `doc/08_tracking/todo/todo_db.sdn` row 179
**Status:** Closed

## Research

- `ModuleLoader.load()` inserts every existing module path into `self.modules`.
- `ModuleLoader.stats().module_count` reports `self.modules.len()`.
- The existing spec covered one loaded module but did not prove multi-module counting.

## Plan

- Add a focused test that loads two existing spec files.
- Assert both loads succeed and both paths are tracked.
- Assert `loaded_modules().len()` and `stats().module_count` both report `2`.
- Close row 179 after lint and focused spec verification.

## Fix

- Added a multi-module count test to `module_loader_spec.spl`.
- Closed `todo_db.sdn` row 179.

## Verification

```sh
bin/simple lint test/unit/compiler/loader/module_loader_spec.spl
bin/simple test test/unit/compiler/loader/module_loader_spec.spl
```
