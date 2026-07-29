# Bug: `SymbolKind` enum-variant patterns never match across the cross-module path — `rt_enum_discriminant` returns -1

- **Date:** 2026-07-29
- **Severity:** medium (silent — any `case SymbolKind.X:` gate on symbols built by module_lowering silently never fires)
- **Area:** interpreter enum discriminants across modules / 20.hir
- **Found by:** lane IMP2 (qualified-import-call fix) via isolated probes + in-place instrumentation (reverted).

## Symptom

In `20.hir/hir_lowering/expressions.spl`, gating on
`receiver_symbol.kind == SymbolKind.Module` (or `case SymbolKind.Module:`)
never succeeds for symbols constructed in `module_lowering.spl`:
`rt_enum_discriminant` returns `-1` for the `kind` value, so no variant arm
ever matches. Any pass filtering symbols by kind through this path is
silently dead — the same "structurally dead via pattern mismatch" family as:

- naked-struct-pattern-vs-Option always-wildcard
  (`naked_struct_pattern_vs_option_always_wildcard_2026-07-29.md`, lane SYM0)
- interp struct name-collision global registry (memory:
  `feedback_interp_struct_name_collision_global_registry`)

## Workaround (landed in commit for lane IMP2)

Drop the kind filter; key on `(defining_module, name)` instead — local
variables/params never carry `defining_module`, so module-qualified callable
detection stays safe and falls through silently when no match exists.
Sites: `field_module_callable` and the new MethodCall module-call check in
`expressions.spl` (both commented in-line).

## Repro sketch

Build a symbol via HirLowering/module_lowering in module A, pass it to a
matcher in module B, `match sym.kind: case SymbolKind.Module:` → wildcard;
`rt_enum_discriminant(sym.kind)` → -1. (IMP2 instrumented then reverted;
re-instrument from its report if needed.)

## Fix direction

Root-cause why enum values built in another module lose their discriminant
under the interpreter (likely the same enum-registry/name-collision family).
Until fixed, avoid `SymbolKind` pattern gates on cross-module symbols;
audit other `case SymbolKind.` sites for the same dead-gate shape.
