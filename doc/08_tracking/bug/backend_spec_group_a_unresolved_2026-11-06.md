# Backend unit specs (group A) still failing on release/1.0.0 — 2026-11-06

Sweep: `bin/simple test <spec>` one file at a time, Rust seed release100-7a0e6fe516f, macOS arm64.

## Specs written ahead of code (module never on release/1.0.0)

These import modules that have never existed on any release/main history
(`git log --all -- <path>` is empty), so they execute 0 examples.
Implementing a RISC-V scalar core to VHDL / Lean IR is out of scope for a spec fix.

- riscv_scalar_decoder_to_vhdl_spec.spl
- riscv_scalar_product_to_vhdl_spec.spl
- riscv_scalar_runtime_alu_pipeline_to_vhdl_spec.spl
- riscv_scalar_runtime_lsu_to_vhdl_spec.spl
- riscv_scalar_runtime_pipeline_v3_to_vhdl_spec.spl
- riscv_scalar_runtime_pipeline_v4_to_vhdl_spec.spl
- riscv_scalar_runtime_pipeline_v5_to_vhdl_spec.spl
- riscv_scalar_runtime_pipeline_v6_flat_to_vhdl_spec.spl
- riscv_scalar_runtime_pipeline_v7_flat_to_vhdl_spec.spl
- riscv_scalar_runtime_pipeline_v8_flat_to_vhdl_spec.spl
- riscv_scalar_runtime_pipeline_v9_flat_to_vhdl_spec.spl
- riscv_scalar_runtime_pipeline_v9_rvfi_formal_spec.spl
- riscv_scalar_runtime_pipeline_v9_rvfi_to_vhdl_spec.spl
- riscv_scalar_runtime_stateful_v2_to_vhdl_spec.spl
- riscv_scalar_rvfi_formal_spec.spl
- riscv_scalar_rvfi_to_vhdl_spec.spl
- lean_ir_spec.spl — `compiler.backend` does not export `lean_ir`

## HAL sealed-binding feature reverted on the release line

`src/compiler/00.common/hal/rt_hal_static_binding.spl`,
`src/lib/nogc_sync_mut/io/hal_device_dispatch.spl` and the
`rt_hal_sealed_prepare_v1` orchestrator wiring exist only on
`origin/chore/merge-share-history` (a8244005f9b / e274cd33719). fcbec1c3b62
restored src/compiler to origin, which removed them. The specs below need that
feature landed through a reviewed PR; until then they fail.

- rt_hal_call_binding_source_contract_spec.spl
- rt_hal_device_exec_binding_source_contract_spec.spl
- rt_hal_auto_link_contract_spec.spl

## Not yet triaged (failing at sweep, no per-expectation discrimination done)

- layout_scanner_spec.spl
- lexer_source_array_release_abi_spec.spl
- llvm_array_value_copy_single_ssa_def_spec.spl
- llvm_bitcast_pointer_bool_spec.spl
- llvm_bootstrap_accumulator_reset_spec.spl
- llvm_codegen_module_scope_default_spec.spl
- llvm_comparison_operand_type_spec.spl
- llvm_copy_move_alloc_spec.spl
- llvm_cross_module_global_symbol_spec.spl
- llvm_cross_module_symbol_mangling_spec.spl
- llvm_direct_extern_abi_spec.spl
- llvm_inline_asm_template_spec.spl
- llvm_ir_builder_target_header_lifetime_spec.spl
- llvm_lib_backend_spec.spl
- llvm_mingw_lld_discovery_spec.spl
- llvm_mutable_global_static_spec.spl
- llvm_narrow_field_load_spec.spl
- llvm_nary_phi_incoming_spec.spl
- llvm_opt_pipeline_spec.spl
- llvm_pointer_return_null_spec.spl
- llvm_simd_array_abi_spec.spl
- llvm_struct_receiver_guard_spec.spl
- llvm_tagged_aggregate_field_spec.spl
- llvm_typed_text_literal_box_spec.spl
- logger_native_probe_spec.spl
- native_ffi_spec.spl
- native_runtime_authority_spec.spl
- native_tool_authority_spec.spl
- numeric_interpolation_abi_spec.spl
- raw_if_chain_backend_consumers_spec.spl
- runtime_compiler_spec.spl
