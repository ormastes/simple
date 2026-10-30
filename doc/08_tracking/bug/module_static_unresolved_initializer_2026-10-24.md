# module_static_unresolved_initializer

Status: compiler fix committed (unverified: producer not rebuilt).

Symptom: `compiler.frontend.core.parser: cannot derive module static type from unresolved initializer` for `var par_lexical_bindings = ParserLexicalBindings(authority: 0, scope_authorities: [])` (class imported from parser_lexical_bindings).

Repro: test/fixtures/compiler/p3fix_mir/ms. Red on p2shard-6 stage2.

Root cause: HIR lowered_const_value_type (trait_impl_lowering.spl) settles a constructor-call initializer only for records in nongeneric_record_owners, which only own-module declarations populated; imported records stayed Infer and MIR lower_static failed closed.

Fix: module_import_registration.spl marks an imported class/struct non-generic when its import surface has no type_params, so the HIR const type (the storage ABI for owner and importers) is Named(record), identical to the explicit annotation.

## Workaround record (phase-3 adhoc lane, landed with #4302)

Status: workaround applied, root fix open. Found in Phase-3 run-11 (8ab7cd693d8) MIR stage.

Symptom: cannot derive module static type from unresolved initializer (compiler.frontend.core.parser, par_lexical_bindings).

Workaround (tagged `@workaround bug=module_static_unresolved_initializer_2026-10-24`): explicit annotation (src/compiler/10.frontend/core/parser.spl).

Root fix location: src/compiler/50.mir/_MirLowering/module_lowering.spl: derive static type from a struct-literal constructor of an imported struct.
