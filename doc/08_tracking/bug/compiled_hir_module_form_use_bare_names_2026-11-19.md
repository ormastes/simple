# Compiled HIR does not bind bare names from a module-form `use`

- **Status:** fixed in pure-Simple HIR (`src/compiler/20.hir`, 2026-11-22); seed (`src/compiler_rust`) tracked separately
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

## Resolution (2026-11-22)

- **Pure-Simple HIR root cause fixed:** `_driver_try_entry_import_rel` loads same-directory sibling modules for un-dotted imports (`use provider` in `test/fixtures/compiled_module_form_use/main.spl`), but `module_surface_resolve_relative_key` (`src/compiler/20.hir/hir_lowering/module_surface_registry_index.spl`) and `resolve_module_key_relative` (`src/compiler/20.hir/hir_lowering/_Items/module_import_registration.spl`) previously returned `""` whenever `not name.starts_with(".")` missed root/`src/`/`std.` lookup instead of falling back to the importer's directory sibling (`"." + name`, rejecting self-imports). Both resolvers now fall back to the sibling surface, where `resolve_import_list` (`module_import_resolution.spl:1009`) binds exported callables via `register_glob_imported_symbols`.
- **Specs:** Added in-process HIR+MIR regression `test/01_unit/compiler/hir/hir_module_form_use_bare_name_spec.spl` covering both `use provider` -> `mfu_provider_fn()` and `use os.kernel.abi.syscall_shim_file` -> `spl_shim_file_capability_check as u64` (`@tag:in-development` retained on CLI subprocess spec `test/01_unit/compiler/20.hir/compiled_module_form_use_bare_name_spec.spl` until Phase 4 full-CLI `bin/simple` replaces the Rust bootstrap seed).
- **Note on `syscall_shim.spl`:** The explicit `{...}` keepalive imports in `src/os/kernel/abi/syscall_shim.spl` (and `test/01_unit/os/kernel/abi/syscall_shim_keepalive_spec.spl`) remain in place only while seed-driven kernel builds still traverse `src/compiler_rust/compiler/src/pipeline/native_project/`.
