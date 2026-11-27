# Backend spec group B: remaining reds after the 2026-11-06 triage

Scope: `test/01_unit/compiler/backend/` group B (runtime_* .. x86_*), run one spec
at a time on the Rust seed (release100-7a0e6fe516f), branch release/1.0.0.

## Fixed in the same change
runtime_timestamp_owner_source, simpleos_forbidden_allocator_guard,
simpleos_native_target_flow, stage4_contracts_provider, stage4_process_provider,
stage4_runtime_legacy_compat_provider, stage4_runtime_native_wiring,
stage4_selected_archive_projection, std_error_no_duplicate_definition_guard.
runtime_owner went from 7/10 to 8/10.

## Still red, by class

1. **Interpreter/JIT divergence in the COFF cede path** (`runtime_owner_spec`, 2 left).
   Under `simple run` (JIT), `runtime_owner_cede_archive_file_v1` on the 374-byte
   fixture returns parsed=1, members=1, undefined=2, demoted=1. Under `simple test`
   (interpreter) the same call returns parsed=1, members=0, undefined=0, so
   `owned.has(_owner_name(...))` never matches. The source is correct. The defect
   is in the seed's `simple test` execution path (u8 to text name build, or dict
   `has` on that name).
2. **Backend source trees deleted by 88aac2ffe28** (also absent on origin/main):
   C, CUDA, Lean, Lua, most of `backend/vhdl/*`, `wasm/*`, `wasm_backend.spl`,
   `*_type_mapper.spl` for wasm/c/cuda/vhdl/vulkan. These specs depend on them:
   type_mapper (WasmTypeMapper), vhdl_backend/builder/clocked_global_state/
   design_catalog/dim_constraints/hardware_call_lowering/metadata_index/testbench/
   trace_hot_path/artifact_manifest/aspect_provenance, vulkan_backend_intensive,
   wasm_codegen, wasm_mir_to_wat (1). Restoring roughly 80 files is an owner decision.
   It is not a spec retarget.
3. **Specs rewound by the transplant, with undefined locals**:
   stage4_final_symbol_closure (13: `barrier_pos` and `macho` undefined, providers
   whose ABI grew) and stage4_native_link_source_contract (6: they read
   `llvm_native_link.spl`, which has been a facade since b81cd5afd72, and should
   use `test/helpers/compiler_native_link_source.spl`).
4. **Behavioural/native**: simpleos_ssp_codegen (IR text), text_extern_abi_ptr_len_divergence
   (marked RED known-bug), text_predicate_argument_shapes_native,
   unresolved_symbol_alias_fails_closed (needs ld.lld objects), vulkan_* source specs.

These were not triaged in this pass: vulkan_compile_endpoint_source, vulkan_entry_abi_source,
vulkan_gep_index_diagnostic_class, vulkan_shared_gep_index_type, vulkan_source_storage_buffer_abi,
and vhdl_backend_spec (it produced no Results line within 300 s).
