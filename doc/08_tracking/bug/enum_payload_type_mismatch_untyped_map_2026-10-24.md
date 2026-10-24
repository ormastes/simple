# enum_payload_type_mismatch_untyped_map

Status: workaround applied, root fix open. Run-11 MIR.

Symptom: HirTypeKind.Function payload mismatch at 0 (type_infer/traits collect_function_bounds_from_module): hir_fn.params.map(_.type_) has no resolved [HirType] type.

Workaround (@workaround bug=enum_payload_type_mismatch_untyped_map_2026-10-24): explicit typed loop building [HirType] (src/compiler/30.types/type_infer/traits.spl).

Root fix location: src/compiler/50.mir/_MirLoweringExpr/enum_constructor_payload.spl and result typing of .map with a placeholder-lambda projection.
