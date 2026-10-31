# Compiler system specs still RED after relfix (2026-10-31)

Cluster: test/03_system/app/compiler + test/03_system/compiler, run on the Rust seed (Windows).

## Seed bugs (src/compiler_rust not edited)
1. `Dict<i64,V>.keys()` yields keys that print as `7` but compare unequal to the i64 `7`
   (`key == 7` false, `to_text()=="7"` true). Breaks `symbol.id.id != key` in
   src/compiler/50.mir/verification_source_environment_v1.spl:24-25 and the scope loop
   (35 tests each in lean_enum_elimination_spec and compiler_lean_enum_elimination_spec).
   Repro: `var d: Dict<i64,S> = {}; d[7]=...; for k in d.keys(): print "{k == 7}"` -> false.
2. `&mut Struct` parameter writes are not visible to the caller, or fail with
   "cannot assign field on non-object value (obj route, field execution)"
   (artifact_service_bridge.spl:92,143,170; ~9 specs: incremental/*, feature/*_owner_result).
   Repro: struct Route, `fn bump(route: &mut Route)`; caller reads old field value.
3. Module-alias calls `use std.fs` then `fs.exists(p)` / `fs.read_text(p)` fail with
   "expects 1 argument(s), but 2 were provided" (bootstrap_centralized_storage_roots_spec, 4 tests).
4. windows_abi.rs implements CreateFileW/ReadFile only; `GetFileType`, `WriteFile`,
   `FlushFileBuffers`, `SetFilePointerEx` -> "unknown extern function" (item4_linker_file_reader,
   item4_stream_*, item4_bounded_execution, item4_linker_bounded_storage; 7 specs).

## Stale specs / absent product (left RED, owner decision)
- c_parser_spec, import_c_defines_spec, import_c_match_spec: src/lib/common/c_parser was deleted.
- graph_utils_spec, mir_types_spec, symbol_hash_spec: legacy `feature "..."` DSL and
  `std_lib.tooling.compiler.*`, which exists only under src/compiler_rust/lib.
- mcdc_instrumentation_modes_spec: McdcPolicy.StaticOff/emits_manifest() etc. do not exist
  (product has McdcMode only).
- rtl_mdsoc_plugin_stubs_spec, rtl_mdsoc_capsule_boundary_spec: planned vhdl_emit_*_stub.spl
  files and `# capsule:` markers were never added.
- environment_optimized_dynamic_libraries_spec, compiler_semantic_cache_manager_spec: helpers are
  intentionally `fail("unimplemented")` until the production owners land.
- lean_composite_values / compiler_lean_composite_values: depth-129 type is refused by the type
  exporter ("recursive array type depth budget") before the constant exporter's "constant nesting
  limit"; ordering decision needed.
- driver_api_tier_policy_spec: expects literal `export X` lines; product uses `pub fn`/`pub use`.

## ENV-BLOCKED
- Specs that shell out to a self-hosted binary (seed banner "bootstrap seed only"), hard-coded
  /bin/sh or /tmp, `src/compiler_rust/target/debug/simple`, native-build, Linux-only host checks
  (item4_elf_source expects host_os linux), macho/freebsd/riscv link-and-execute lanes.
