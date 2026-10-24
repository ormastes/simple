# enum_payload_type_mismatch_dict_elem_untyped

Status: workaround applied, root fix open. Run-11 MIR.

Symptom: enum construction TraitError.Overlapping payload mismatch at 1 (trait_solver check_coherence): elements read from Dict-erased values have no static struct type.

Workaround (@workaround bug=enum_payload_type_mismatch_dict_elem_untyped_2026-10-24): typed locals ImplBlock (src/compiler/25.traits/trait_solver.spl).

Root fix location: src/compiler/50.mir/_MirLoweringExpr/enum_constructor_payload.spl and Dict<K,[V]> index element typing in MIR expression lowering.
