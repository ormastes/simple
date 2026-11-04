# match_nil_subpattern_requires_declared_optional_slot

Status: workaround applied, root fix open. Phase-3 run-11 (8ab7cd693d8) MIR stage.

Symptom: enum match: nil sub-pattern requires a declared optional payload slot (plugins/backend_lean/lean_mir_translate.spl Ok(nil) arms).

Workaround (tagged `@workaround bug=match_nil_subpattern_requires_declared_optional_slot_2026-10-24`): case Ok(_) after Ok(Some(code)) (src/plugins/backend_lean/lean_mir_translate.spl).

Root fix location: src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl: accept nil sub-pattern when payload type is T? of generic Result.

## Triage 2026-11-04 (MIR slice B)
Root fix is on origin/release/1.0.0: 606bf9986ac (nil patterns for proven optional enum payloads) and 17f3f27959e (`Ok(nil)` over `Result<T?,E>` proves its Optional slot from the subject type); `nil_optional_slot` in `switch_operators_calls.spl` (~3396-3420). Status: fix-implemented-verification-pending. Verify with a stage3-built compiler: remove the `case Ok(_)` workaround in lean_mir_translate.spl and rebuild.
