# match_variant_pattern_shadowed_by_struct_name

Status: workaround applied, root fix open. Phase-3 run-11 (8ab7cd693d8) MIR stage.

Symptom: enum match: unsupported arm pattern (Struct) in poll_generator.spl: bare case Expr(e) resolves to struct Expr rather than StmtKind.Expr.

Workaround (tagged `@workaround bug=match_variant_pattern_shadowed_by_struct_name_2026-10-24`): qualify as StmtKind.Expr / StmtKind.Return (src/compiler/10.frontend/desugar/poll_generator.spl).

Root fix location: src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl: resolve bare variant patterns against the subject enum before struct names.
