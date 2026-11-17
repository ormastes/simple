# native_hir_defining_module_empty_local_decls_2026-11-17 (P1)

Status: fix-implemented-verification-pending (native Stage 2 re-run pending)

## Bug
Stage 2 bootstrap (native-built compiler lowering
`src/compiler/bootstrap_admission/p2_add.spl`): `bind_declaration_origin_v1`
saw `symbol.defining_module` empty for every local fn (main, tag_bool,
tag_i64s, tag_text, tag_texts) while owner = `compiler.bootstrap_admission.p2_add`.
The interpreter is correct.

## Root cause
`declare_module_symbols_with_source_intents_v1`
(`src/compiler/20.hir/hir_lowering/_Items/module_declarations_bootstrap.spl`)
built the option it passes to every `symbols.define(..., mod_name)` as an
UNTYPED join: `val mod_name = if c: Some(self.module_filename) else: nil`.
Native producers older than the MIR optional-arm join fix
(`untyped_optional_arm_join_typed_as_i64_2026-11-06.md`) type that slot as the
first arm's raw word with no option marks, so `define_with_binding` read the
`text?` as absent and stored no defining_module. This is a codegen class
already fixed in source; the producer that built Stage 2 predates it.

## Fix
Annotate and use safe absence:
`val mod_name: text? = if self.module_filename != "": Some(self.module_filename) else: None`.
Spec: `test/01_unit/compiler/hir/declaration_defining_module_typed_option_spec.spl`.

## Workaround
A separate lane is landing a tagged guard in `bind_declaration_origin_v1`
(`src/compiler/20.hir/hir_symbol_table_methods.spl`) that fills an empty
defining_module from owner; it is not in this commit's tree. That guard is REMOVABLE once a native Stage 2 run shows
non-empty defining_module for p2_add's local declarations without it.
