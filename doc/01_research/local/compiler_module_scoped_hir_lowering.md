# Compiler Module-Scoped HIR Lowering - Local Research

## Scope

Feature request: `FR-COMPILER-004` in `doc/08_tracking/feature_request/compiler_requests.md`.

## Findings

- `Driver.lower_and_check_impl` created one `HirLowering` before iterating all parsed modules.
- `Driver.lower_to_hir_impl` had the same shared-lowerer pattern.
- `SymbolTable.define` intentionally uses first-write-wins for type-level symbols so explicit imports pre-registered by `resolve_import_symbols` are not overwritten inside one module.
- Reusing the same `HirLowering.symbols` across modules turns that module-local protection into cross-module contamination: a type registered while lowering module A remains in the root scope when lowering a later consumer module.
- `HirLowering.modules_by_name` is read-only import context and can be copied onto each fresh lowerer.

## Selected Fix

Create a fresh `HirLowering` inside each module loop in the driver, then set:

- `lowering.modules_by_name = ctx.modules`
- `lowering.module_filename = source_path_map[name]`

This gives each module its own symbol table while preserving access to all parsed modules for import pre-registration.

## Regression Surface

- System SSpec: `test/system/compiler_module_scoped_hir_lowering_spec.spl`
- Existing import resolver SSpec: `test/unit/compiler/hir/resolve_import_symbols_spec.spl`
