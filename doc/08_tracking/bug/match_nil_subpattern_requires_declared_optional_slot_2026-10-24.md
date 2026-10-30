# match_nil_subpattern_requires_declared_optional_slot

Status: workaround applied, root fix open. Phase-3 run-11 (8ab7cd693d8) MIR stage.

Symptom: enum match: nil sub-pattern requires a declared optional payload slot (plugins/backend_lean/lean_mir_translate.spl Ok(nil) arms).

Workaround (tagged `@workaround bug=match_nil_subpattern_requires_declared_optional_slot_2026-10-24`): case Ok(_) after Ok(Some(code)) (src/plugins/backend_lean/lean_mir_translate.spl).

Root fix location: src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl: accept nil sub-pattern when payload type is T? of generic Result.
