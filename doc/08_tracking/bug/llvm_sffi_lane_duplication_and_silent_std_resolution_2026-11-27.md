# Duplicated llvm sffi lanes and silent first-lane `std.X` resolution (2026-11-27)

Found while fixing the native-build worker JIT demotion
(native_build_scv_cold_init_runs_interpreted_after_jit_demotion_2026-11-27.md).

1. Forked duplicates: src/lib/nogc_async_mut/sffi/{llvm_types,llvm_codegen,llvm_target}.spl are
   independent copies of src/lib/nogc_sync_mut/sffi/ (same fn names, e.g. llvm_int8_type_in_context).
   Co-compiling both makes every bare call ambiguous (compiler_cross_module_private_symbol_collision) and
   demotes the whole closure to the interpreter. They should become `export use` facades over one owner,
   like the async llvm_loader. Importers of the async copies: src/app/cli/p3_groups/group_1.spl:91-93,
   src/app/cli/p3_groups/group_2.spl:59.
2. Stale src/compiler/70.backend/backend/llvm_lib_backend.spl (imports compiler.backend.llvm_lib_type_mapper,
   llvm_lib_translate, std.sffi.llvm - modules that do not exist at those paths); the live copies are in
   src/plugins/backend_llvm_lib/. Grep shows no module importer (only a comment in backend/__init__.spl:191
   and an unrelated variable name in llvm_capability.spl). Removed in the same change.
3. Resolver: bare `std.X` picks the first lane silently (interpreter_module/path_resolution.rs:948-955,
   lane order nogc_async_mut, nogc_sync_mut, ...). It should warn or error when more than one lane
   provides the module, which would have flagged the llvm collision at its source.
