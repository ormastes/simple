# Compiler Import Alias Resolution - Design

## Problem

`FR-COMPILER-002` requires explicit imports to win over global module load order when multiple modules export the same short type name. The remaining alias gap was in HIR import pre-registration: aliases were preserved in the parsed import item but ignored when defining the local symbol.

## Design

`HirLowering.resolve_import_symbols` remains the single pre-registration point for imported type-level symbols. For named imports:

- Use `item.name` to look up the exported declaration in the imported module.
- Use `item.alias` as the local symbol name when `item.has_alias` is true.
- Preserve `defining_module` as the imported module path so visibility and diagnostics still point to the true source.

Glob imports are unchanged because they have no per-item alias.

## Test Strategy

Add a unit SSpec on the import resolver that parses two modules exporting
`CompileOptions`, imports both under distinct aliases, and asserts each alias
resolves to the expected defining module. Add a compiled system SSpec for the
pure local-name selection helper used by the resolver, because the full synthetic
symbol-table fixture currently trips an unrelated compiled `SymbolTable` issue.
