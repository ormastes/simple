# module_loader_loaded_symbol_resolution

Date: 2026-04-22
TODO row: 173
Status: fixed

## Research

Row 173 requested coverage for loading a module with a symbol and resolving it. The compatibility loader does not need real SMF symbol parsing for this behavior: `ModuleLoader.resolve_symbol` first checks `global_symbols` and returns `SymbolResult.Found` with empty code for module-owned symbols already present in the table.

## Plan

Add a focused loader spec that loads an existing module path, records a non-JIT `LoadedSymbol` owned by that module in `global_symbols`, resolves it through the public `resolve_symbol` API, and verifies the returned metadata and symbol count.

## Fix

Added `loads a module with a symbol and resolves it from globals` to `test/unit/compiler/loader/module_loader_spec.spl`. The test covers module load success, symbol metadata preservation, non-JIT resolution, empty resolved code payload, and stats accounting.

## Verification

- `bin/simple lint test/unit/compiler/loader/module_loader_spec.spl`
- `timeout 120s bin/simple test test/unit/compiler/loader/module_loader_spec.spl`
