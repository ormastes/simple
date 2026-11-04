# match_variant_pattern_shadowed_by_struct_name

Status: workaround applied, root fix open. Phase-3 run-11 (8ab7cd693d8) MIR stage.

Symptom: enum match: unsupported arm pattern (Struct) in poll_generator.spl: bare case Expr(e) resolves to struct Expr rather than StmtKind.Expr.

Workaround (tagged `@workaround bug=match_variant_pattern_shadowed_by_struct_name_2026-10-24`): qualify as StmtKind.Expr / StmtKind.Return (src/compiler/10.frontend/desugar/poll_generator.spl).

Root fix location: src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl: resolve bare variant patterns against the subject enum before struct names.

### 2026-11-04 triage (c28-w1b) — not reproducible on the interpreter, stays open
`test/01_unit/compiler/mir/bare_variant_vs_struct_name_spec.spl` (4/4 pass, seed interpreter) lowers
parse -> HIR -> MIR for `struct Expr` + `enum Kind { Expr(e: Expr) ... }` and `case Expr(e):` over a field
subject, a typed parameter, and a qualified spelling: no "unsupported arm pattern". The HIR positional-struct
reinterpretation (`expression_components.spl` ~line 800) is gated on `not enum_variant_names.contains(variant)`
and the subject-typed path resolves the variant first, so single-module shadowing is handled. The original failure
had `StmtKind` and `Expr` in DIFFERENT modules (poll_generator imports both), so the likely trigger is
`enum_variant_names` not yet holding the imported enum's variants. Verification needs a stage3/native compile with the
workaround at `poll_generator.spl:~182` reverted to bare `case Expr(e):`. Workaround kept. Spec kept as regression coverage.
