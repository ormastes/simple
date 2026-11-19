# Compiled HIR does not bind bare names from a module-form `use`

- **Status:** open
- **Found:** 2026-11-19, riscv64 kernel native-build (`syscall_shim.spl`)
- **Repro:** `test/01_unit/compiler/20.hir/compiled_module_form_use_bare_name_spec.spl`
  (`@tag:in-development`, fixture `test/fixtures/compiled_module_form_use/`)

`use pkg.mod` (module form) lets the interpreter resolve a bare `fn` name
defined in `mod`; the compiled HIR path does not. Under `lenient_types` the
unresolved name becomes `HirExprKind::Global` and dies in LLVM codegen as
`llvm global load referenced undeclared symbol`.

## Workaround in tree

`src/os/kernel/abi/syscall_shim.spl` imports the 94 sibling-module keepalive providers by
name (`use os.kernel.abi.syscall_shim_X.{...}`; the 95th is local), tagged
`WORKAROUND(compiled_hir_module_form_use_bare_names_2026-11-19)`. Delete those
lines once the repro spec passes.

Regression test for the workaround shape: `llvm_address_taken_symbol_form_import_compiles` in `src/compiler_rust/compiler/src/pipeline/native_project/tests.rs` (passes on base: symbol-form address-taking already works, so no compiler change was needed).
