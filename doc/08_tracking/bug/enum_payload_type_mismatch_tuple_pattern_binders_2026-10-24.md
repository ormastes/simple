# enum_payload_type_mismatch_tuple_pattern_binders

Status: workaround applied, root fix open. Phase-3 run-11 (8ab7cd693d8) MIR stage.

Symptom: HirTypeKind.Function/Layer/Tensor/Tuple payload mismatch in type_infer/inference_control.spl (infer_compose/parallel/layer_connect/matmul/broadcast_op) plus for-in over I64: binders from tuple-pattern 'case (Function(a,b,_), Function(c,d,_))' carry no static type.

Workaround (tagged `@workaround bug=enum_payload_type_mismatch_tuple_pattern_binders_2026-10-24`): rebind each binder to a typed local (src/compiler/30.types/type_infer/inference_control.spl).

Root fix location: src/compiler/50.mir/_MirLoweringExpr/enum_constructor_payload.spl and tuple-subject variant-pattern binder typing in src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl: derive binder types from the variant payload declaration.

### 2026-11-04 triage (c28-w1b) — not reproducible on the interpreter, stays open
`test/01_unit/compiler/mir/tuple_pattern_binder_and_if_match_type_spec.spl` (tuple-binder cases, 3/3 pass) lowers
`match (x, y): case (Ty.Function(a,b,_), Ty.Function(c,d,_))` in qualified, bare and mixed spellings through HIR+MIR
with binders used as typed values (`a.len() + b`): no fatal MIR error. The failure needs the native stage2/3 build
(HirTypeKind payloads from another module in `inference_control.spl`). Verification: revert the typed-local rebinds
in `inference_control.spl` and run a stage3 compile. Workaround kept.
