# Module Loader Symbol Count

**Date:** 2026-04-22
**Todo:** `doc/08_tracking/todo/todo_db.sdn` row 180
**Status:** Closed

## Research

- `ModuleLoader.stats().symbol_count` reports `self.global_symbols.len()`.
- Successful JIT-backed `resolve_symbol()` calls insert resolved symbols into `global_symbols`.
- Existing loader specs covered one JIT symbol but did not verify symbol counting after multiple module-backed resolutions.

## Plan

- Load two existing module paths.
- Register one possible JIT symbol per loaded path.
- Resolve both symbols through the public loader API.
- Assert both names are present in `global_symbols` and `stats().symbol_count == 2`.
- Close row 180 after lint and focused spec verification.

## Fix

- Added a multi-symbol count test to `module_loader_spec.spl`.
- Closed `todo_db.sdn` row 180.

## Verification

```sh
bin/simple lint test/unit/compiler/loader/module_loader_spec.spl
bin/simple test test/unit/compiler/loader/module_loader_spec.spl
```
