# Compiler Import Alias Resolution - Local Research

## Scope

Feature request: `FR-COMPILER-002` in `doc/08_tracking/feature_request/compiler_requests.md`.

## Findings

- The self-hosted HIR lowerer already has `resolve_import_symbols` in `src/compiler/20.hir/hir_lowering/items.spl`.
- The pass pre-registers imported class, struct, enum, and trait names before local symbol declaration, which fixes explicit imports for same-named types.
- Named imports ignored `ImportItem.has_alias` and always registered the original imported name. This left `use a.{CompileOptions as DriverOptions}` unresolved under `DriverOptions`.
- The parser and HIR import structures already preserve aliases, so the fix is local to the pre-registration pass.

## Selected Fix

For named imports, register the imported symbol under `item.alias` when `item.has_alias` is true; otherwise keep registering under `item.name`.

## Regression Surface

- Unit SPipe: `test/unit/compiler/hir/resolve_import_symbols_spec.spl`
- System SPipe: `test/system/compiler_import_alias_resolution_spec.spl`
