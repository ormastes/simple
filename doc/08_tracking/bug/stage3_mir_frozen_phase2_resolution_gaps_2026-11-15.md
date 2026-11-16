# Stage 3 MIR: frozen Phase 2 resolution gaps (2026-11-15)

Frozen Phase 2 compiler (pin 18a1f28937c2) compiling the Stage 3 closure from tip
source rejects three modules that the Rust seed accepts. Source workarounds,
tagged `# @workaround bug=stage3_mir_frozen_phase2_resolution_gaps_2026-11-15`.

## Class A: SymbolTable receiver methods unresolved (owner empty)
- `compiler.hir.hir_lowering._Expressions.union_narrow_arms` (7 fatals, first
  `get_symbol_type_raw`), `..._Expressions.call_arity` (`lookup_or_invalid`).
- `self.symbols` is `SymbolTable` (field of HirLowering); its methods live in
  `hir_symbol_table_methods.spl`. Every other hir_lowering file that calls
  SymbolTable methods through narrow imports imports `SymbolTable` and
  `hir_symbol_table_methods.*` directly (binding_types.spl, etc.); these two
  imported only `HirLowering`/`SymbolId`, so the old compiler never registers the
  method owner. Workaround: add those two imports. Confidence: medium (inferred
  from the import pattern; not run on the frozen compiler).

## Class B: missing exact struct construction layout 'ParserErrorRecord'
- `compiler.driver.driver_parse_diagnostic` constructed `ParserErrorRecord`
  (added 4c89fd116a7, 2026-11-12) across a module boundary. Workaround: construct
  it in its defining module via `parser_error_record_make` (parser.spl) and call
  that. Confidence: medium.

Verified only with the Rust seed `check` (no new errors); not on the frozen compiler.
