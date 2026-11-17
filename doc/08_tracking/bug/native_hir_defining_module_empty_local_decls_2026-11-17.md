# Native build leaves defining_module empty on local declarations (2026-11-17)

Status: open. A separate lane owns the fix.

## Symptom
The native Stage 2 build of `src/compiler/bootstrap_admission/p2_add.spl` at
`bd61db2fc23` reported 31 `source declaration origin mismatches the symbol owner`
errors. All of them were on the module's own functions: `main`, `tag_bool`,
`tag_i64s`, `tag_text` and `tag_texts`. In every one, `defining_module` was
empty and the owner was `compiler.bootstrap_admission.p2_add`. The interpreter
stamps these symbols correctly.

## Suspect
`declare_module_symbols_with_source_intents_v1` in
`src/compiler/20.hir/hir_lowering/module_declarations_bootstrap.spl` builds
`mod_name` as `if self.module_filename != "": Some(self.module_filename) else: nil`
and passes it to `SymbolTable.define`. The suspicion is that the native lane
drops or miscompiles that Optional. Not confirmed.

## Workaround in place
`bind_declaration_origin_v1` (`src/compiler/20.hir/hir_symbol_table_methods.spl`,
tagged `WORKAROUND(native_hir_defining_module_empty_local_decls_2026-11-17)`)
fills an empty `defining_module` from the declaring owner. It counts every fill
in `hir_unstamped_defining_module_fill_count()`. A non-empty owner that differs
is still an error. Remove the workaround once the native build stamps
`defining_module` and the counter stays at zero.

## Repro and coverage
`test/01_unit/compiler/hir/declaration_origin_symbol_spec.spl` contains two
cases: an unstamped symbol whose binding must be filled and counted, and a
non-empty owner that differs and must still be an error.
