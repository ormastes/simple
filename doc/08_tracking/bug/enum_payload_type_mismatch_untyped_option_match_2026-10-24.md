# enum_payload_type_mismatch_untyped_option_match

Status: workaround applied, root fix open. Found in Phase-3 run-11 (8ab7cd693d8) MIR stage.

Symptom: enum construction 'HirExprKind.If/IfChain/Return/Yield/Range/Break/EnumLit': payload type mismatch (semantics.resolve resolve_expr); 'val x = match o: Some(e): Some(f(e)) / nil: nil' has no resolved optional type.

Workaround (tagged `@workaround bug=enum_payload_type_mismatch_untyped_option_match_2026-10-24`): explicit T? annotations on the match locals (src/compiler/35.semantics/resolve.spl).

Root fix location: src/compiler/50.mir/_MirLoweringExpr/enum_constructor_payload.spl and match-expression result type unification (Some(T)/nil arms -> T?).
