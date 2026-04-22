# Compiler Module-Scoped HIR Lowering - Design

## Problem

`FR-COMPILER-004` reports that the self-hosted driver reuses one `HirLowering` instance while lowering every parsed module. Because each `HirLowering` owns a `SymbolTable`, type names registered for one module remain visible while lowering the next module. This breaks explicit import resolution when two modules export the same short type name.

## Design

Use one `HirLowering` per module lowering operation.

The driver still shares parse context through `ctx.modules`; each fresh lowerer receives that map as `modules_by_name` so `resolve_import_symbols` can locate imported ASTs. The lowerer also receives only the current module's source path as `module_filename`.

This preserves first-write-wins inside a single module but prevents symbols from prior modules from occupying the next module's root scope.

## Test Strategy

Add a system SSpec that lowers a module defining `CompileOptions`, then lowers a separate consumer that explicitly imports `b.CompileOptions`. The consumer must resolve to `b`, proving prior module symbols did not leak.
