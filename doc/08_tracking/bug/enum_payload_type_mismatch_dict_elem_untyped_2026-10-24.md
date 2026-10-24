# enum_payload_type_mismatch_dict_elem_untyped

Status: compiler fix committed (unverified: producer not rebuilt).

Symptom: TraitError.Overlapping payload mismatch (trait_solver check_coherence): `val impl_list = self.impls[k]`; `val impl1 = impl_list[i]`.

Repro: test/fixtures/compiler/p3fix_mir/dictelem. Trace: remembered='' source=none.

Root causes: (1) lower_dict_runtime_get (expr_dispatch.spl) remembered the declared V on the read only when the builder's MIR type had NOT already fixed the decode, so `self.impls[k]` stayed untyped; (2) the Let arms (mir_lowering_stmts.spl) treated HIR's Infer marker as a declared type and stored it, so remember_untyped_let_nominal_init (which would type `impl_list[i]`) never ran.

Fix: always remember the declared V on a non-Option dict read; treat Infer/Error Let types as absent (mir_let_type_unsettled).

## Workaround record (phase-3 adhoc lane, landed with #4302)

Status: workaround applied, root fix open. Run-11 MIR.

Symptom: enum construction TraitError.Overlapping payload mismatch at 1 (trait_solver check_coherence): elements read from Dict-erased values have no static struct type.

Workaround (@workaround bug=enum_payload_type_mismatch_dict_elem_untyped_2026-10-24): typed locals ImplBlock (src/compiler/25.traits/trait_solver.spl).

Root fix location: src/compiler/50.mir/_MirLoweringExpr/enum_constructor_payload.spl and Dict<K,[V]> index element typing in MIR expression lowering.
