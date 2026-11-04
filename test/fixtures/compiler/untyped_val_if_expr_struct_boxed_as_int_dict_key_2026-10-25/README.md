# untyped_val_if_expr_struct_boxed_as_int_dict_key_2026-10-25

Bug row: `untyped_val_if_expr_struct_boxed_as_int_dict_key_2026-10-25` (P2, workaround
tagged in `src/compiler/20.hir/hir_lowering/_Items/module_build.spl`, `fn_key: SymbolId`).

Native-only repro (Stage 2 miscompile class; seed interpreter passes):

    bin/simple native-build --entry test/fixtures/compiler/untyped_val_if_expr_struct_boxed_as_int_dict_key_2026-10-25/main.spl --output build/uvk && build/uvk

Expected stdout `16` then `7`, exit 0. A SEGV or wrong sum means the untyped
`val x = if c: <struct> else: <struct>` binding is again typed i64.
Interpreter check: `bin/simple.exe run <main.spl>`.
