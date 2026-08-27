# Test Results

**Generated:** 2026-05-19 11:58:31
**Total Tests:** 120809
**Status:** ⚠️ 12328 FAILED

## Summary

| Metric | Count |
|--------|-------|
| Total | 892 |
| Passed | 63 |
| Failed | 42 |
| Skipped | 0 |

---

## 🔄 Recent Status Changes

- test/01_unit/compiler/async/async_desugar_integration_spec.spl
- test/01_unit/compiler/async/async_frame_analysis_spec.spl
- test/01_unit/compiler/async/async_integration_spec.spl
- test/01_unit/compiler/async/async_mir_interpreter_spec.spl
- test/01_unit/compiler/async/async_mir_spec.spl
- test/01_unit/compiler/async/async_pipeline_spec.spl
- test/01_unit/compiler/async/async_reservation_analysis_spec.spl
- test/01_unit/compiler/async/async_spawn_analysis_spec.spl
- test/01_unit/compiler/async/async_state_machine_spec.spl
- test/01_unit/compiler/async/poll_generator_spec.spl
- test/01_unit/compiler/async/state_enum_spec.spl
- test/01_unit/compiler/async/suspension_analysis_spec.spl
- test/02_integration/net/http_content_encoding_spec.spl
- test/01_unit/compiler/verify/baremetal_noalloc_constraints_spec.spl
- test/01_unit/compiler/verification/cache_correctness_spec.spl
- test/01_unit/compiler/verification/deterministic_emission_spec.spl
- test/01_unit/compiler/verification/lean_basic_spec.spl
- test/01_unit/compiler/verification/lean_block_integration_spec.spl
- test/01_unit/compiler/verification/lean_codegen_spec.spl
- test/01_unit/compiler/verification/lean_workflow_spec.spl
- test/01_unit/compiler/verification/memory_capabilities_spec.spl
- test/01_unit/compiler/verification/naming_spec.spl
- test/01_unit/compiler/verification/proof_reference_spec.spl
- test/01_unit/compiler/verification/regeneration_spec.spl
- test/01_unit/compiler/verification/report_rendering_spec.spl
- test/01_unit/compiler/verification/tool_checker_spec.spl
- test/01_unit/compiler/verification/toolchain_detection_spec.spl
- test/01_unit/compiler/verification/unified_attrs_spec.spl
- test/01_unit/compiler/verification/unsupported_construct_spec.spl
- test/01_unit/compiler/verification/verification_diagnostics_spec.spl
- test/01_unit/compiler/assurance/assurance_schemas_spec.spl
- test/01_unit/compiler/assurance/dynamic_composition_spec.spl
- test/01_unit/compiler/assurance/flight_rules_spec.spl
- test/01_unit/compiler/assurance/formal_delivery_gates_spec.spl
- test/01_unit/compiler/assurance/formal_interfaces_spec.spl
- test/01_unit/compiler/assurance/formal_receipt_spec.spl
- test/01_unit/compiler/assurance/formal_status_spec.spl
- test/01_unit/compiler/assurance/nat_normalizer_receipt_spec.spl
- test/01_unit/compiler/assurance/policy_five_site_convergence_spec.spl
- test/01_unit/compiler/assurance/policy_graph_contamination_probe_spec.spl
- test/01_unit/compiler/assurance/proof_dag_spec.spl
- test/01_unit/compiler/assurance/sha512_integrity_receipt_spec.spl
- test/01_unit/compiler/assurance/verified_release_gate_spec.spl
- test/01_unit/compiler/mdsoc/aop_proceed_spec.spl
- test/01_unit/compiler/mdsoc/config_multi_dim_spec.spl
- test/01_unit/compiler/mdsoc/config_spec.spl
- test/01_unit/compiler/mdsoc/construct_checker_spec.spl
- test/01_unit/compiler/mdsoc/construct_types_spec.spl
- test/01_unit/compiler/mdsoc/cross_query_spec.spl
- test/01_unit/compiler/mdsoc/doc_validation_spec.spl
- test/01_unit/compiler/mdsoc/feature_ports_spec.spl
- test/01_unit/compiler/mdsoc/layer_checker_spec.spl
- test/01_unit/compiler/mdsoc/layer_ci_spec.spl
- test/01_unit/compiler/mdsoc/layer_enforcement_spec.spl
- test/01_unit/compiler/mdsoc/pipeline_integration_spec.spl
- test/01_unit/compiler/mdsoc/transform_adapters_spec.spl
- test/01_unit/compiler/mdsoc/types_spec.spl
- test/01_unit/compiler/mdsoc/vc_import_spec.spl
- test/01_unit/compiler/mdsoc/vc_static_spec.spl
- test/02_integration/doctest/discovery_spec.spl
- test/07_security/csprng_salt_iv_spec.spl
- test/01_unit/compiler/visibility_spec.spl
- test/01_unit/compiler/60.mir_opt/general_patterns_spec.spl
- test/01_unit/compiler/60.mir_opt/hwir_opt_spec.spl
- test/01_unit/compiler/60.mir_opt/optimizer_manifest_backend_budget_spec.spl
- test/01_unit/compiler/60.mir_opt/pass_descriptor_budget_spec.spl
- test/01_unit/compiler/vhdl/hardware_spawn_lower_spec.spl
- test/01_unit/compiler/vhdl/vhdl_subprogram_spec.spl
- test/01_unit/compiler/vhdl/vhdl_testbench_spec.spl
- test/01_unit/compiler/vhdl_riscv_gap_spec.spl
- test/01_unit/compiler/vhdl_subprogram_spec.spl
- test/01_unit/compiler/vhdl_testbench_spec.spl
- test/01_unit/app/audit/audit_spec.spl
- test/01_unit/app/arch_check_spec.spl
- test/02_integration/rust/meta/comment_only_spec.spl
- test/01_unit/app/auto_coverage_10_spec.spl
- test/01_unit/app/auto_coverage_1_spec.spl
- test/01_unit/app/auto_coverage_11_spec.spl
- test/01_unit/app/auto_coverage_12_spec.spl
- test/01_unit/app/build/build_targets_spec.spl
- test/01_unit/app/build/feature_flags_spec.spl
- test/01_unit/app/build/repo_hygiene_gate_spec.spl
- test/01_unit/app/build/change_classifier_spec.spl
- test/01_unit/app/build/action_identity_spec.spl
- test/01_unit/app/build/opt_remarks_spec.spl
- test/01_unit/app/build/artifact_receipt_spec.spl
- test/01_unit/app/build/bootstrap_policy_spec.spl
- test/01_unit/app/build/build_explain_spec.spl
- test/01_unit/app/build_coverage_spec.spl
- test/03_system/coverage/coverage_check_api_spec.spl
- test/03_system/coverage/coverage_core_spec.spl
- test/03_system/coverage/coverage_doc_stats_spec.spl
- test/03_system/coverage/coverage_runtime_ffi_spec.spl
- test/03_system/coverage/coverage_test_runner_spec.spl
- test/01_unit/compiler/borrow/borrow_check_spec.spl
- test/01_unit/compiler/borrow/iso_move_assign_field_spec.spl
- test/01_unit/compiler/borrow/iso_move_pipeline_spec.spl
- test/01_unit/compiler/borrow/iso_move_return_spec.spl
- test/01_unit/compiler/borrow/iso_move_sites_spec.spl
- test/01_unit/compiler/borrow/iso_parse_pipeline_spec.spl
- test/01_unit/compiler/borrow/iso_use_after_move_e2e_spec.spl
- test/01_unit/compiler/borrow/lifetime_spec.spl
- test/02_integration/watcher/watcher_backend_validation_spec.spl
- test/02_integration/watcher/watcher_shb_integration_spec.spl
- test/02_integration/watcher/watcher_smf_integration_spec.spl
- test/01_unit/app/auto_coverage_5_spec.spl
- test/02_integration/io/native_ops_dir_create_all_spec.spl
- test/02_integration/io/native_ops_dir_create_spec.spl
- test/02_integration/io/native_ops_dir_recursive_spec.spl
- test/02_integration/io/native_ops_file_copy_spec.spl
- test/02_integration/io/native_ops_file_read_write_spec.spl
- test/02_integration/io/native_ops_file_size_spec.spl
- test/feature/lib/gc_parity/gc_module_loader_spec.spl
- test/feature/lib/gc_parity/nogc_sync_mut_contract_spec.spl
- test/feature/lib/gc_parity/otp_behaviours_spec.spl
- test/feature/lib/mcp/bootstrap_e2e_test.spl
- test/feature/lib/mcp/bootstrap_functions_test.spl
- test/feature/lib/mcp/bootstrap_import_test.spl
- test/feature/lib/mcp/bootstrap_protocol_test.spl
- test/feature/lib/mcp/core_spec.spl
- test/feature/lib/mcp/handler_function_test.spl
- test/feature/lib/mcp/handler_import_test.spl
- test/feature/lib/mcp/handler_registry_spec.spl
- test/feature/lib/mcp/helpers_spec.spl
- test/feature/lib/mcp/integration_spec.spl
- test/feature/lib/mcp/lazy_loading_v2_test.spl
- test/feature/lib/mcp/schema_simple_test.spl
- test/feature/lib/mcp/schema_spec.spl
- test/feature/lib/std/compiler/lexer_ffi_test.spl
- test/feature/lib/std/helpers_example_spec.spl
- test/feature/lib/import_debug_spec.spl
- test/feature/lib/minimal_spec.spl
- test/05_perf/graphics_2d/backend_preference_startup_spec.spl
- test/05_perf/graphics_2d/backend_probe_spec.spl
- test/05_perf/graphics_2d/c_vs_simple_2d_spec.spl
- test/05_perf/graphics_2d/cpu_simd_spec.spl
- test/05_perf/graphics_2d/cuda_smoke_spec.spl
- test/05_perf/graphics_2d/metal_readback_proof_spec.spl
- test/05_perf/graphics_2d/metal_smoke_spec.spl
- test/05_perf/graphics_2d/no_duplication_spec.spl
- test/05_perf/graphics_2d/optimization_plugin_spec.spl
- test/05_perf/graphics_2d/shared_helpers_spec.spl
- test/05_perf/graphics_2d/shared_multilingual_gpu_fonts_perf_spec.spl
- test/05_perf/graphics_2d/simple_2d_vector_fonts_perf_spec.spl
- test/05_perf/graphics_2d/vulkan_spirv_spec.spl
- test/05_perf/graphics_2d/webgpu_real_spec.spl
- test/05_perf/graphics_2d/wm_frame_pacing_spec.spl
- test/05_perf/graphics_2d/report_spec.spl
- test/02_integration/sffi/callback_roundtrip_spec.spl
- test/02_integration/sffi/direction_a_c_roundtrip_spec.spl
- test/02_integration/sffi/direction_a_cpp_roundtrip_spec.spl
- test/02_integration/sffi/direction_b_import_roundtrip_spec.spl
- test/02_integration/sffi/layout_verification_roundtrip_spec.spl
- test/02_integration/sffi/rsa_sha512_reference_import_spec.spl
- test/feature/ml/tensor_dimensions_spec.spl
- test/01_unit/lib/baremetal/allocator_freelist_split_and_underflow_spec.spl
- test/01_unit/lib/baremetal/riscv/sbi_ipi_spec.spl
- test/01_unit/lib/baremetal/riscv/dtb_cpu_walker_spec.spl
- test/01_unit/lib/baremetal/allocator_block_header_spec.spl
- test/01_unit/lib/baremetal/allocator_real_memory_spec.spl
- test/01_unit/lib/blink/html_tree_builder_spec.spl
- test/01_unit/lib/blink/dom_node_spec.spl
- test/01_unit/lib/blink/hit_test_spec.spl
- test/01_unit/lib/blink/document_spec.spl
- test/01_unit/lib/blink/form_paint_spec.spl
- test/01_unit/lib/blink/css_tokenizer_spec.spl
- test/01_unit/lib/blink/render_lane_pipeline_spec.spl
- test/01_unit/lib/blink/paint_tree_walker_spec.spl
- test/01_unit/lib/blink/url/url_parser_spec.spl
- test/01_unit/lib/blink/css_inline_style_spec.spl
- test/01_unit/lib/blink/block_flow_spec.spl
- test/01_unit/lib/blink/inline_text_floats_spec.spl
- test/01_unit/lib/blink/style_cascade_spec.spl
- test/01_unit/lib/blink/paint_artifact_spec.spl
- test/01_unit/lib/blink/block_flow_floats_spec.spl
- test/01_unit/lib/blink/inline_flow_spec.spl
- test/01_unit/lib/blink/html_tokenizer_entities_spec.spl
- test/01_unit/lib/blink/paint_controller_spec.spl
- test/01_unit/lib/blink/scroll_manager_spec.spl
- test/01_unit/lib/blink/html_tokenizer_tree_builder_pipeline_spec.spl
- test/01_unit/lib/blink/computed_style_spec.spl
- test/01_unit/lib/blink/navigation_controller_spec.spl
- test/01_unit/lib/blink/style/user_agent_stylesheet_spec.spl
- test/01_unit/lib/blink/inline_text_spec.spl
- test/01_unit/lib/blink/image_paint_spec.spl
- test/01_unit/lib/blink/input_event_spec.spl
- test/01_unit/lib/blink/style_shorthand_spec.spl
- test/01_unit/lib/blink/flex_spec.spl
- test/01_unit/lib/blink/css_selector_spec.spl
- test/01_unit/lib/blink/paint/text_paint_spec.spl
- test/01_unit/lib/blink/values_length_spec.spl
- test/01_unit/lib/blink/style_at_rules_spec.spl
- test/01_unit/compiler/blocks/block_definition_three_level_spec.spl
- test/01_unit/compiler/blocks/block_outline_info_spec.spl
- test/01_unit/compiler/blocks/block_skip_policy_spec.spl
- test/01_unit/compiler/blocks/builder_api_spec.spl
- test/01_unit/compiler/blocks/easy_api_spec.spl
- test/01_unit/compiler/blocks/pre_lex_info_spec.spl
- test/01_unit/compiler/blocks/pre_lex_per_dsl_spec.spl
- test/01_unit/compiler/blocks/testing_spec.spl
- test/01_unit/compiler/blocks/unified_registry_bootstrap_source_spec.spl
- test/01_unit/compiler/blocks/utils_spec.spl
- test/01_unit/compiler/blocks/builder_api_basic_spec.spl
- test/01_unit/compiler/blocks/builder_default_parser_spec.spl
- test/01_unit/compiler/blocks/easy_api_basic_spec.spl
- test/01_unit/compiler/blocks/testing_framework_spec.spl
- test/01_unit/compiler/blocks/utils_basic_spec.spl
- test/03_system/game3d/rollball_production_spec.spl
- test/02_integration/debug/hardware/hardware_check_spec.spl
- test/02_integration/debug/hardware/stm32h7_openocd_spec.spl
- test/02_integration/debug/hardware/stm32h7_stlink_spec.spl
- test/02_integration/debug/hardware/stm32wb_openocd_spec.spl
- test/02_integration/debug/hardware/stm32wb_stlink_spec.spl
- test/02_integration/debug/hardware/t32_gdb_bridge_spec.spl
- test/02_integration/debug/hardware/t32_native_spec.spl
- test/02_integration/debug/hardware/t32_semihost_hello_spec.spl
- test/feature/mode_filter/all_modes_spec.spl
- test/feature/mode_filter/interpreter_only_spec.spl
- test/feature/mode_filter/native_only_spec.spl
- test/feature/mode_filter/skip_native_spec.spl
- test/01_unit/compiler/bootstrap/ast_native_arena_spec.spl
- test/01_unit/compiler/bootstrap/backend_helpers_shared_binding_contract_spec.spl
- test/01_unit/compiler/bootstrap/class_member_parser_parity_spec.spl
- test/01_unit/compiler/bootstrap/driver_phase_entry_shared_binding_contract_spec.spl
- test/01_unit/compiler/bootstrap/driver_symlink_source_dedup_spec.spl
- test/01_unit/compiler/bootstrap/entry_closure_bucket_count_contract_spec.spl
- test/01_unit/compiler/bootstrap/entry_closure_module_map_update_spec.spl
- test/01_unit/compiler/bootstrap/flattened_linker_symbol_types_contract_spec.spl
- test/01_unit/compiler/bootstrap/hir_expression_shared_binding_contract_spec.spl
- test/01_unit/compiler/bootstrap/hir_import_resolution_shared_binding_contract_spec.spl
- test/01_unit/compiler/bootstrap/hir_module_lowering_shared_binding_contract_spec.spl
- test/01_unit/compiler/bootstrap/hir_statement_shared_binding_contract_spec.spl
- test/01_unit/compiler/bootstrap/hir_symbol_alias_owner_collision_spec.spl
- test/01_unit/compiler/bootstrap/hir_symbol_table_shared_binding_contract_spec.spl
- test/01_unit/compiler/bootstrap/interpreter_function_lookup_shared_binding_contract_spec.spl
- test/01_unit/compiler/bootstrap/labeled_tuple_return_parser_spec.spl
- test/01_unit/compiler/bootstrap/llvm_aggregate_shared_binding_contract_spec.spl
- test/01_unit/compiler/bootstrap/loader_metadata_helpers_contract_spec.spl
- test/01_unit/compiler/bootstrap/mir_call_destination_shared_binding_contract_spec.spl
- test/01_unit/compiler/bootstrap/mir_expr_dispatch_shared_binding_contract_spec.spl
- test/01_unit/compiler/bootstrap/mir_module_lowering_shared_binding_contract_spec.spl
- test/01_unit/compiler/bootstrap/mir_switch_calls_shared_binding_contract_spec.spl
- test/01_unit/compiler/bootstrap/module_surface_canonical_once_spec.spl
- test/01_unit/compiler/bootstrap/module_surface_impl_retention_spec.spl
- test/01_unit/compiler/bootstrap/native_entry_closure_mode_contract_spec.spl
- test/01_unit/compiler/bootstrap/parser_multiline_shape_parity_spec.spl
- test/01_unit/compiler/bootstrap/parser_self_parse_spec.spl
- test/01_unit/compiler/bootstrap/stage2_source_shape_regression_spec.spl
- test/01_unit/compiler/bootstrap/stage4_manual_stage3_admission_contract_spec.spl
- test/01_unit/compiler/bootstrap/stage4_smoke_gate_spec.spl
- test/01_unit/compiler/bootstrap/trait_default_shared_binding_contract_spec.spl
- test/01_unit/compiler/bootstrap/type_multiline_signature_parser_spec.spl
- test/01_unit/compiler/bootstrap/u64_fnv_literal_stage4_spec.spl
- test/01_unit/compiler/bootstrap/vhdl_call_definition_shared_binding_contract_spec.spl
- test/01_unit/compiler/bootstrap/entry_closure_physical_source_dedup_spec.spl
- test/01_unit/compiler/cache/action_key_spec.spl
- test/01_unit/compiler/cache/cache_types_spec.spl
- test/01_unit/compiler/cache/cache_validator_smf_header_spec.spl
- test/01_unit/compiler/cache/cache_validator_spec.spl
- test/01_unit/compiler/cache/cas_store_spec.spl
- test/01_unit/compiler/cache/compile_options_hash_spec.spl
- test/01_unit/compiler/cache/file_stamp_spec.spl
- test/01_unit/compiler/cache/lazy_section_spec.spl
- test/01_unit/compiler/cache/shb_mtime_spec.spl
- test/01_unit/compiler/cache/smf_deps_validation_spec.spl
- test/01_unit/compiler/cache/dirty_closure_spec.spl
- test/01_unit/compiler/cache/interface_digest_spec.spl
- test/01_unit/compiler/cache/target_graph_spec.spl
- test/02_integration/ui/draw_ir_v2_v3_pixel_parity_spec.spl
- test/02_integration/ui/event_backend_matrix_spec.spl
- test/02_integration/ui/global_menubar_spec.spl
- test/02_integration/ui/unified_packed_scene_nesting_spec.spl
- test/02_integration/ui/widget_interact_model_spec.spl
- test/01_unit/compiler/common/attributes_spec.spl
- test/01_unit/compiler/common/config_spec.spl
- test/01_unit/compiler/common/di_spec.spl
- test/01_unit/compiler/common/driver_manifest_attr_spec.spl
- test/01_unit/compiler/common/effects_spec.spl
- test/01_unit/compiler/common/error_types_spec.spl
- test/01_unit/compiler/common/gc_config_spec.spl
- test/01_unit/compiler/common/task_policy_attr_spec.spl
- test/01_unit/compiler/common/export_attr_spec.spl
- test/feature/plugin/custom_block_plugin_spec.spl
- test/feature/plugin/plugin_startup_block_spec.spl
- test/feature/plugin/runtime_api_plugin_spec.spl
- test/feature/plugin/sugar_plugin_spec.spl
- test/03_system/helpers/text_helpers_p1_spec.spl
- test/01_unit/compiler/extern/rt_file_read_bytes_single_extern_signature_spec.spl
- test/01_unit/lib/text/text_index_slice_spec.spl
- test/01_unit/lib/text/text_length_spec.spl
- test/01_unit/lib/text/text_search_spec.spl
- test/01_unit/lib/text/utf8_validation_spec.spl
- test/01_unit/compiler/di/di_config_spec.spl
- test/01_unit/compiler/di/di_lock_phases_spec.spl
- test/01_unit/compiler/di/di_lock_spec.spl
- test/01_unit/compiler/di/di_proxy_spec.spl
- test/01_unit/compiler/di/di_runtime_slots_spec.spl
- test/01_unit/compiler/di/di_runtime_spec.spl
- test/01_unit/compiler/di/di_validation_spec.spl
- test/01_unit/compiler/di/export_as_spec.spl
- test/01_unit/compiler/di/extensions_phases_spec.spl
- test/01_unit/compiler/di/extensions_spec.spl
- test/01_unit/compiler/diagnostics/span_merge_spec.spl
- test/01_unit/compiler/diagnostic_formatter_contract_spec.spl
- test/01_unit/compiler/dict_array_membership_tagged_key_spec.spl
- test/01_unit/compiler/dict_bracket_vs_set_spec.spl
- test/01_unit/compiler/dict_class_field_contains_key_after_insert_spec.spl
- test/01_unit/compiler/dict_get_miss_returns_nil_spec.spl
- test/01_unit/lib/driver/fat32_file_io_spec.spl
- test/01_unit/lib/driver/registry_integration_test.spl
- test/01_unit/lib/driver/fat32_driver_adapter_test.spl
- test/01_unit/lib/driver/driver_manifest_test.spl
- test/01_unit/lib/driver/null_block_driver_test.spl
- test/01_unit/lib/ecs/ecs_spec.spl
- test/01_unit/lib/ffi/ffi_wrappers_spec.spl
- test/01_unit/lib/ffi/ffi_basics_spec.spl
- test/01_unit/lib/ffi/dynamic_versioned_spec.spl
- test/01_unit/lib/ffi/ffi_signature_spec.spl
- test/01_unit/lib/extended/execution_task_unit_spec.spl
- test/01_unit/lib/extended/execution_thread_integration_spec.spl
- test/01_unit/lib/extended/hooks_before_integration_spec.spl
- test/01_unit/lib/extended/memory_arena_unit_spec.spl
- test/01_unit/lib/extended/collections_graph_unit_spec.spl
- test/01_unit/lib/extended/torch_loss_unit_spec.spl
- test/01_unit/lib/extended/execution_context_integration_spec.spl
- test/01_unit/lib/extended/cuda_stream_unit_spec.spl
- test/01_unit/lib/extended/collections_heap_unit_spec.spl
- test/01_unit/lib/extended/hooks_after_unit_spec.spl
- test/01_unit/lib/extended/collections_tree_unit_spec.spl
- test/01_unit/lib/extended/memory_gc_integration_spec.spl
- test/01_unit/lib/extended/hooks_around_unit_spec.spl
- test/01_unit/lib/extended/memory_alloc_unit_spec.spl
- test/01_unit/lib/extended/pure_function_unit_spec.spl
- test/01_unit/lib/extended/qemu_system_integration_spec.spl
- test/01_unit/lib/extended/pure_function_integration_spec.spl
- test/01_unit/lib/extended/collections_heap_integration_spec.spl
- test/01_unit/lib/extended/qemu_device_unit_spec.spl
- test/01_unit/lib/extended/cuda_memory_integration_spec.spl
- test/01_unit/lib/extended/hooks_around_integration_spec.spl
- test/01_unit/lib/extended/hooks_after_integration_spec.spl
- test/01_unit/lib/extended/gpu_buffer_unit_spec.spl
- test/01_unit/lib/extended/execution_task_integration_spec.spl
- test/01_unit/lib/extended/hooks_error_integration_spec.spl
- test/01_unit/lib/extended/cuda_device_unit_spec.spl
- test/01_unit/lib/extended/cuda_stream_integration_spec.spl
- test/01_unit/lib/extended/pure_persistent_unit_spec.spl
- test/01_unit/lib/extended/pure_immutable_integration_spec.spl
- test/01_unit/lib/extended/collections_trie_integration_spec.spl
- test/01_unit/lib/extended/torch_tensor_unit_spec.spl
- test/01_unit/lib/extended/gpu_compute_unit_spec.spl
- test/01_unit/lib/extended/cuda_kernel_integration_spec.spl
- test/01_unit/lib/extended/hooks_error_unit_spec.spl
- test/01_unit/lib/extended/execution_fiber_unit_spec.spl
- test/01_unit/lib/gc_async_immut/root_pmap_native_probe_spec.spl
- test/01_unit/lib/gc_async_immut/facade_resolution_spec.spl
- test/01_unit/lib/gc_async_immut/persistent_vec_native_spec.spl
- test/01_unit/lib/gc_async_immut/vector_push_empty_native_probe_spec.spl
- test/01_unit/lib/gc_async_immut/versioned_native_probe_spec.spl
- test/01_unit/lib/gc_async_immut/native_combinators_spec.spl
- test/01_unit/lib/gc_async_immut/set_facade_native_spec.spl
- test/01_unit/lib/gc_async_immut/vector_empty_native_probe_spec.spl
- test/01_unit/lib/gc_async_immut/trie_root_facade_native_spec.spl
- test/01_unit/lib/gc_async_immut/map_facade_native_spec.spl
- test/01_unit/lib/gc_async_immut/atom_native_probe_spec.spl
- test/01_unit/lib/gc_async_immut/root_native_probe_spec.spl
- test/01_unit/lib/gc_async_immut/trie_facade_native_spec.spl
- test/01_unit/lib/gc_async_immut/persistent_collections_native_spec.spl
- test/01_unit/lib/gc_async_immut/root_version_native_probe_spec.spl
- test/01_unit/compiler/interpreter_extern/sdl3_registration_spec.spl
- test/01_unit/compiler/interpreter_extern/opengl_registration_spec.spl
- test/01_unit/compiler/interpreter_extern/file_char_device_registration_spec.spl
- test/01_unit/compiler/interpreter_extern/glfw_registration_spec.spl
- test/01_unit/compiler/interpreter_extern/oneapi_registration_spec.spl
- test/01_unit/compiler/interpreter_extern/capability_gap_spec.spl
- test/01_unit/compiler/interpreter_extern/audio_registration_spec.spl
- test/01_unit/compiler/interpreter_extern/fb_image_log_socket_registration_spec.spl
- test/01_unit/compiler/irdsl/parser_validator_spec.spl
- test/01_unit/lib/gc_sync_immut/facade_resolution_spec.spl
- test/01_unit/lib/gc_sync_immut/map_facade_native_spec.spl
- test/01_unit/lib/gc_sync_immut/native_combinators_spec.spl
- test/01_unit/lib/gc_sync_immut/persistent_collections_native_spec.spl
- test/01_unit/lib/gc_sync_immut/persistent_vec_native_spec.spl
- test/01_unit/lib/gc_sync_immut/set_facade_native_spec.spl
- test/01_unit/lib/gc_sync_immut/trie_facade_native_spec.spl
- test/01_unit/lib/gc_sync_immut/trie_root_facade_native_spec.spl
- test/02_integration/svmg/conformance/conformance_suite_spec.spl
- test/02_integration/core/common_compression_framework_facade_spec.spl
- test/02_integration/core/core_integration_10_spec.spl
- test/02_integration/core/core_integration_11_spec.spl
- test/02_integration/core/core_integration_12_spec.spl
- test/02_integration/core/core_integration_13_spec.spl
- test/02_integration/core/core_integration_14_spec.spl
- test/02_integration/core/core_integration_15_spec.spl
- test/02_integration/core/core_integration_16_spec.spl
- test/02_integration/core/core_integration_17_spec.spl
- test/02_integration/core/core_integration_18_spec.spl
- test/02_integration/core/core_integration_19_spec.spl
- test/02_integration/core/core_integration_1_spec.spl
- test/02_integration/core/core_integration_20_spec.spl
- test/02_integration/core/core_integration_21_spec.spl
- test/02_integration/core/core_integration_22_spec.spl
- test/02_integration/core/core_integration_23_spec.spl
- test/02_integration/core/core_integration_25_spec.spl
- test/02_integration/core/core_integration_26_spec.spl
- test/02_integration/core/core_integration_27_spec.spl
- test/02_integration/core/core_integration_28_spec.spl
- test/02_integration/core/core_integration_2_spec.spl
- test/02_integration/core/core_integration_30_spec.spl
- test/02_integration/core/core_integration_31_spec.spl
- test/02_integration/core/core_integration_32_spec.spl
- test/02_integration/core/core_integration_33_spec.spl
- test/02_integration/core/core_integration_34_spec.spl
- test/02_integration/core/core_integration_35_spec.spl
- test/02_integration/core/core_integration_39_spec.spl
- test/02_integration/core/core_integration_3_spec.spl
- test/02_integration/core/core_integration_42_spec.spl
- test/02_integration/core/core_integration_46_spec.spl
- test/02_integration/core/core_integration_48_spec.spl
- test/02_integration/core/core_integration_49_spec.spl
- test/02_integration/core/core_integration_50_spec.spl
- test/02_integration/core/core_integration_8_spec.spl
- test/01_unit/compiler/lint/bare_primitive_internal_spec.spl
- test/01_unit/compiler/lint/collection_array_rebuild_spec.spl
- test/01_unit/compiler/lint/collection_easy_fix_spec.spl
- test/01_unit/compiler/lint/collection_index_mutation_spec.spl
- test/01_unit/compiler/lint/const_ref_default_spec.spl
- test/01_unit/compiler/lint/critical_file_guard_spec.spl
- test/01_unit/compiler/lint/feature_tracking_done_gate_spec.spl
- test/01_unit/compiler/lint/lint_profile_spec.spl
- test/01_unit/compiler/lint/llvm_backend_type_safety_spec.spl
- test/01_unit/compiler/lint/mcp_perf_lint_spec.spl
- test/01_unit/compiler/lint/module_init_literal_spec.spl
- test/01_unit/compiler/lint/option_me_call_spec.spl
- test/01_unit/compiler/lint/parse001_spec_files_spec.spl
- test/01_unit/compiler/lint/primitive_types_parity_spec.spl
- test/01_unit/compiler/lint/public_doc_spec.spl
- test/01_unit/compiler/lint/raw_rt_access_spec.spl
- test/01_unit/compiler/lint/required_comment_cli_spec.spl
- test/01_unit/compiler/lint/riscv_rtl_debuggability_spec.spl
- test/01_unit/compiler/lint/script_language_spec.spl
- test/01_unit/compiler/lint/semantic_api_checker_spec.spl
- test/01_unit/compiler/lint/stub_impl_spec.spl
- test/01_unit/compiler/lint/test_lint_fn_spec.spl
- test/01_unit/compiler/lint/unwrapped_foreign_resource_spec.spl
- test/01_unit/compiler/lint/use_resolution_w0407_severity_spec.spl
- test/01_unit/compiler/lint/wide_public_spec.spl
- test/01_unit/compiler/lint/star_export_lint_spec.spl
- test/02_integration/infra/counterpart/foundation_redteam_spec.spl
- test/02_integration/infra/counterpart/worker_isolation_spec.spl
- test/01_unit/lib/gui/browser_window_spec.spl
- test/01_unit/lib/gui/menu_spec.spl
- test/01_unit/lib/gui/pure_core_spec.spl
- test/01_unit/lib/gui/pure_gui_release_lane_spec.spl
- test/01_unit/lib/gui/pure_smf_dynlib_perf_spec.spl
- test/01_unit/compiler/macros/template_kind_can_follow_spec.spl
- test/01_unit/compiler/macros/macro_integration_spec.spl
- test/01_unit/compiler/macros/macro_check_spec.spl
- test/02_integration/spec/coverage_spec.spl
- test/02_integration/spec/formatter_spec.spl
- test/02_integration/spec/mock_policy_execution_spec.spl
- test/02_integration/spec/runner_spec.spl
- test/01_unit/lib/host_io/fileio_async_spec.spl
- test/01_unit/lib/host_io/net_async_spec.spl
- test/01_unit/lib/host_io/stdio_async_spec.spl
- test/01_unit/lib/hardware/fpga_k26/k26_axi_hp_bridge_spec.spl
- test/01_unit/lib/hardware/fpga_k26/k26_kv260_rv64_spec.spl
- test/01_unit/lib/hardware/fpga_k26/k26_soc_top_vexriscv_spec.spl
- test/01_unit/lib/hardware/fpga_k26/k26_wb_axi_hp_bridge_spec.spl
- test/01_unit/lib/hardware/fpga_linux/fpga_synthesis_rv64_spec.spl
- test/01_unit/lib/hardware/fpga_linux/product_bus_adapter_spec.spl
- test/01_unit/lib/hardware/fpga_linux/rv64_product_soc_top_spec.spl
- test/01_unit/lib/hardware/fpga_linux/soc_vhdl_gen_rv64_spec.spl
- test/01_unit/lib/hardware/fpga_linux/synthesis_wrapper_vexriscv_spec.spl
- test/01_unit/lib/hardware/link_mux/jtag_debug_scenario_spec.spl
- test/01_unit/lib/hardware/link_mux/jtag_units_spec.spl
- test/01_unit/lib/hardware/opensource_rtl/vexriscv_smp/vexriscv_smp_import_spec.spl
- test/01_unit/lib/hardware/riscv_common/riscv_compressed_mission_critical_spec.spl
- test/01_unit/lib/hardware/riscv_common/riscv_compressed_zca_seed_spec.spl
- test/01_unit/lib/hardware/riscv_common/riscv_scalar_isa_database_spec.spl
- test/01_unit/lib/hardware/riscv_product_ports_source_spec.spl
- test/01_unit/lib/hardware/rv64gc_rtl/core64_integration_spec.spl
- test/01_unit/lib/hardware/rv64gc_rtl/core_protected_cycle_spec.spl
- test/01_unit/lib/hardware/rv64gc_rtl/imac_synth_source_closure_spec.spl
- test/01_unit/lib/hardware/rv64gc_rtl/register_banks_spec.spl
- test/01_unit/lib/hardware/soc_rtl/eth_fcs_spec.spl
- test/01_unit/lib/hardware/soc_rtl/soc_dtb_asset_spec.spl
- test/01_unit/lib/hardware/soc_rtl/soc_top_64_protected_spec.spl
- test/01_unit/lib/hardware/soc_rtl/soc_top_64_spec.spl
- test/01_unit/lib/hardware/soc_rtl/soc_top_rv32_protected_spec.spl
- test/01_unit/lib/hardware/vhdl_gen/exec_core_gen_spec.spl
- test/01_unit/lib/hardware/vhdl_gen/rv32_trap_completeness_spec.spl
- test/02_integration/lib/std/improvements/stdlib_improvements_spec.spl
- test/02_integration/lib/std/diagram/diagram_integration_spec.spl
- test/02_integration/lib/std/ml/simple_math_integration_spec.spl
- test/02_integration/lib/std/failsafe/crash_prevention_spec.spl
- test/02_integration/lib/std/doctest/discovery_spec.spl
- test/02_integration/lib/std/screenshot/screenshot_ffi_spec.spl
- test/02_integration/lib/persistence_intensive_spec.spl
- test/02_integration/lib/database_query_spec.spl
- test/02_integration/lib/thread_pool_async_spec.spl
- test/02_integration/lib/database_e2e_spec.spl
- test/02_integration/lib/stdlib_intensive_spec.spl
- test/02_integration/lib/failsafe_integration_spec.spl
- test/02_integration/lib/query_intensive_spec.spl
- test/02_integration/lib/protocol_intensive_spec.spl
- test/02_integration/lib/database_atomic_spec.spl
- test/02_integration/lib/game_net/udp_transport_spec.spl
- test/02_integration/lib/simd_stdlib_spec.spl
- test/02_integration/lib/gpu/gpu_kernel_emission_spec.spl
- test/02_integration/lib/gpu/gpu_scheduler_diag_spec.spl
- test/02_integration/lib/gpu/gpu_offload_payload_gating_spec.spl
- test/02_integration/lib/gpu/cpu_sw_primitive_readback_spec.spl
- test/01_unit/lib/http/ws/ws_writer_opcode_emission_spec.spl
- test/01_unit/lib/http/ws/ws_frame_round_trip_spec.spl
- test/01_unit/lib/http/ws/ws_negative_offset_guard_spec.spl
- test/01_unit/lib/http/ws/ws_opcode_dispatch_spec.spl
- test/01_unit/lib/http/multipart_header_separator_spec.spl
- test/01_unit/lib/http/request_empty_guard_spec.spl
- test/01_unit/lib/http/response_plain_text_helper_dedup_spec.spl
- test/01_unit/lib/http/response_empty_guard_spec.spl
- test/01_unit/lib/http/h2/h2_preface_probe_spec.spl
- test/01_unit/lib/http/h2/h2_frame_round_trip_spec.spl
- test/01_unit/lib/http/h2/h2_server_text_to_u8_spec.spl
- test/01_unit/lib/http/h2/h2_negative_offset_guard_spec.spl
- test/01_unit/lib/http/h2/hpack_round_trip_spec.spl
- test/01_unit/lib/http/h3/h3_negative_offset_guard_spec.spl
- test/01_unit/lib/http/h3/h3_frame_round_trip_spec.spl
- test/01_unit/lib/http/chunked_size_overflow_sync_spec.spl
- test/01_unit/compiler/mir_opt/auto_vectorize_spec.spl
- test/01_unit/compiler/mir_opt/bounds_check_elim_spec.spl
- test/01_unit/compiler/mir_opt/cipher/cipher_intrinsics_spec.spl
- test/01_unit/compiler/mir_opt/cipher/cipher_parity_spec.spl
- test/01_unit/compiler/mir_opt/cipher/cipher_rewrite_integration_spec.spl
- test/01_unit/compiler/mir_opt/cipher/opt_remark_spec.spl
- test/01_unit/compiler/mir_opt/cipher/pattern_dispatch_spec.spl
- test/01_unit/compiler/mir_opt/cipher/pattern_engine_spec.spl
- test/01_unit/compiler/mir_opt/cipher/target_opt_context_spec.spl
- test/01_unit/compiler/mir_opt/clib_parity_hotspot_spec.spl
- test/01_unit/compiler/mir_opt/collection_opt_spec.spl
- test/01_unit/compiler/mir_opt/constant_folding_spec.spl
- test/01_unit/compiler/mir_opt/copy_propagation_spec.spl
- test/01_unit/compiler/mir_opt/dead_code_spec.spl
- test/01_unit/compiler/mir_opt/fs_optimization_spec.spl
- test/01_unit/compiler/mir_opt/general_patterns_backend_recommendation_spec.spl
- test/01_unit/compiler/mir_opt/loop_invariant_motion_spec.spl
- test/01_unit/compiler/mir_opt/optimization_pipeline_aggregate_transport_source_spec.spl
- test/01_unit/compiler/mir_opt/optimizer_manifest_backend_policy_spec.spl
- test/01_unit/compiler/mir_opt/pass_descriptor_spec.spl
- test/01_unit/compiler/mir_opt/predicate_promote_spec.spl
- test/01_unit/compiler/mir_opt/runtime_array_assignment_ssa_spec.spl
- test/01_unit/compiler/mir_opt/storage_layout_access_advisory_spec.spl
- test/01_unit/compiler/mir_opt/storage_simd_admission_spec.spl
- test/01_unit/compiler/mir_opt/storage_simd_codegen_spec.spl
- test/01_unit/compiler/mir_opt/storage_simd_schedule_spec.spl
- test/01_unit/compiler/mir_opt/strength_reduction_spec.spl
- test/01_unit/compiler/mir_opt/typed_storage_view_producer_spec.spl
- test/01_unit/compiler/mir_opt/var_reassign_analysis_spec.spl
- test/01_unit/compiler/module_resolver/allowed_families_spec.spl
- test/01_unit/compiler/module_resolver/type_domain_resolver_spec.spl
- test/01_unit/compiler/module_resolver/numbered_dir_spec.spl
- test/01_unit/compiler/module_resolver/tier_ambiguity_warning_spec.spl
- test/01_unit/compiler/module_resolver/var_resolution_spec.spl
- test/01_unit/compiler/mono/monomorphize/deferred_deserialize_byte_text_spec.spl
- test/01_unit/compiler/mono/generic_template_spec.spl
- test/01_unit/compiler/mono/mold_pure_spec.spl
- test/01_unit/compiler/mono/mono_cache_efficiency_spec.spl
- test/01_unit/compiler/mono/monomorphization_native_build_regression_spec.spl
- test/01_unit/compiler/mono/monomorphize_spec.spl
- test/01_unit/compiler/mono/note_sdn_bdd_spec.spl
- test/01_unit/compiler/mono/note_sdn_spec.spl
- test/01_unit/compiler/mono/monomorphize_integration_spec.spl
- test/01_unit/lib/i18n/resource_bundle_spec.spl
- test/01_unit/compiler/native/arm_neon_spec.spl
- test/01_unit/compiler/native/asm_match_spec.spl
- test/01_unit/compiler/native/auto_vectorize_spec.spl
- test/01_unit/compiler/native/baremetal_syntax_spec.spl
- test/01_unit/compiler/native/bitfield_codegen_spec.spl
- test/01_unit/compiler/native/build_native_min_spec.spl
- test/01_unit/compiler/native/callconv_bridge_spec.spl
- test/01_unit/compiler/native/cli_interpreter_path_spec.spl
- test/01_unit/compiler/native/dict_get_struct_value_spec.spl
- test/01_unit/compiler/native/inline_asm_constraints_spec.spl
- test/01_unit/compiler/native/inline_asm_core_parser_spec.spl
- test/01_unit/compiler/native/inline_asm_matrix_spec.spl
- test/01_unit/compiler/native/inline_asm_spec.spl
- test/01_unit/compiler/native/native_compile_spec.spl
- test/01_unit/compiler/native/simd_capabilities_spec.spl
- test/01_unit/compiler/native/simd_check_spec.spl
- test/01_unit/compiler/native/x86_64_simd_spec.spl
- test/01_unit/compiler/native/x86_simd_register_contract_spec.spl
- test/01_unit/lib/immut/persistent_trie_spec.spl
- test/01_unit/lib/immut/atom_spec.spl
- test/01_unit/lib/immut/persistent_builder_spec.spl
- test/01_unit/lib/immut/persistent_map_spec.spl
- test/01_unit/lib/immut/ref_spec.spl
- test/01_unit/lib/immut/actor_snapshot_spec.spl
- test/01_unit/lib/immut/persistent_list_spec.spl
- test/01_unit/lib/immut/persistent_vec_spec.spl
- test/01_unit/lib/immut/versioned_snapshot_spec.spl
- test/01_unit/lib/immut/persistent_set_spec.spl
- test/01_unit/lib/immut/persistent_sorted_map_spec.spl
- test/01_unit/lib/immut/integration_spec.spl
- test/01_unit/lib/immut/combinators_spec.spl
- test/01_unit/lib/immut/debug_map_spec.spl
- test/01_unit/compiler/regression/entry_closure_defect_semantics_spec.spl
- test/01_unit/compiler/regression/short_circuit_semantics_spec.spl
- test/01_unit/compiler/regression/struct_init_omitted_field_nil_fill_spec.spl
- test/01_unit/compiler/regression/try_operator_preservation_spec.spl
- test/01_unit/lib/jit/jit_types_spec.spl
- test/01_unit/lib/jit/jit_unified_runner_spec.spl
- test/01_unit/compiler/resource/resource_borrow_pinning_spec.spl
- test/01_unit/compiler/resource/resource_decl_spec.spl
- test/01_unit/compiler/resource/resource_drop_exactly_once_spec.spl
- test/01_unit/compiler/resource/resource_family_inference_spec.spl
- test/01_unit/compiler/resource/resource_hir_metadata_spec.spl
- test/01_unit/compiler/resource/resource_interp_drop_spec.spl
- test/01_unit/compiler/resource/resource_mir_drop_spec.spl
- test/01_unit/compiler/resource/resource_ownership_sigil_spec.spl
- test/01_unit/compiler/resource/resource_sffi_pilot_spec.spl
- test/01_unit/compiler/resource/resource_shared_mut_method_spec.spl
- test/01_unit/compiler/resource/resource_use_after_move_spec.spl
- test/01_unit/compiler/resource/resource_with_scoped_mir_drop_spec.spl
- test/01_unit/compiler/resource/resource_with_scoped_spec.spl
- test/01_unit/compiler/resource/resource_wrapper_gen_spec.spl
- test/01_unit/compiler/semantic/self_field_method_resolution_spec.spl
- test/01_unit/compiler/semantic/typed_empty_array_constructor_general_spec.spl
- test/01_unit/compiler/semantic/typed_empty_array_constructor_spec.spl
- test/01_unit/lib/js/js_native_confinement_spec.spl
- test/01_unit/lib/js/json_unicode_escape_spec.spl
- test/01_unit/lib/js/typeof_builtin_introspection_spec.spl
- test/01_unit/lib/nogc_async_mut_noalloc/async/poll_spec.spl
- test/01_unit/lib/nogc_async_mut_noalloc/async/response_time_report_spec.spl
- test/01_unit/lib/nogc_async_mut_noalloc/async/scheduler_ravenscar_spec.spl
- test/01_unit/lib/nogc_async_mut_noalloc/async/scheduler_spec.spl
- test/01_unit/lib/nogc_async_mut_noalloc/async/timing_model_spec.spl
- test/01_unit/lib/nogc_async_mut_noalloc/async/wcet_adapter_spec.spl
- test/01_unit/lib/nogc_async_mut_noalloc/collections/fixed_array_spec.spl
- test/01_unit/lib/nogc_async_mut_noalloc/collections/fixed_array_stack_backing_storage_regression_spec.spl
- test/01_unit/lib/nogc_async_mut_noalloc/collections/fixed_map_backing_storage_regression_spec.spl
- test/01_unit/lib/nogc_async_mut_noalloc/collections/fixed_map_spec.spl
- test/01_unit/lib/nogc_async_mut_noalloc/collections/fixed_set_spec.spl
- test/01_unit/lib/nogc_async_mut_noalloc/collections/fixed_stack_spec.spl
- test/01_unit/lib/nogc_async_mut_noalloc/collections/linked_list_backing_storage_regression_spec.spl
- test/01_unit/lib/nogc_async_mut_noalloc/collections/linked_list_spec.spl
- test/01_unit/lib/nogc_async_mut_noalloc/collections/ring_buffer_spec.spl
- test/01_unit/lib/nogc_async_mut_noalloc/execution/semihost_capture_sleep_ms_spec.spl
- test/01_unit/lib/nogc_async_mut_noalloc/memory/refc_binary_spec.spl
- test/01_unit/lib/nogc_async_mut_noalloc/path/baremetal_path_spec.spl
- test/01_unit/lib/nogc_async_mut_noalloc/qemu_spec.spl
- test/01_unit/lib/nogc_async_mut_noalloc/tls/tls_smoke_spec.spl
- test/01_unit/compiler/type_infer/type_infer_correctness_spec.spl
- test/01_unit/compiler/hir/host_gpu_lane_hir_lowering_spec.spl
- failed
- test/01_unit/compiler/hir/alias_static_call_resolution_spec.spl
- test/01_unit/compiler/hir/tuple_match_enum_subpattern_spec.spl
- passed
- test/01_unit/compiler/hir/nil_dict_receiver_phantom_option_spec.spl
- test/01_unit/compiler/hir/method_self_context_save_restore_spec.spl
- test/01_unit/compiler/hir/hir_lazy_import_registration_flag_regression_spec.spl
- test/01_unit/compiler/hir/enum_payload_range_or_frontend_exec_spec.spl
- test/01_unit/compiler/hir/module_surface_spec.spl
- test/01_unit/compiler/hir/hir_async_spec.spl
- test/01_unit/compiler/hir/hir_glob_reachable_miss_memo_spec.spl
- test/01_unit/compiler/hir/stage4_hir_value_name_dispatch_spec.spl
- test/01_unit/compiler/hir/legacy_builtin_alias_source_spec.spl
- test/01_unit/compiler/hir/resolve_import_module_value_spec.spl
- test/01_unit/compiler/hir/imported_composite_field_package_sibling_spec.spl
- test/01_unit/compiler/hir/vulkan_gpu_attr_hir_spec.spl
- test/01_unit/compiler/hir/exhaustiveness/critical_wildcard_coverage_spec.spl
- test/01_unit/compiler/hir/imported_tuple_signature_dependency_spec.spl
- test/01_unit/compiler/hir/hir_forward_lowering_spec.spl
- test/01_unit/compiler/hir/package_export_route_shapes_spec.spl
- test/01_unit/compiler/hir/bootstrap_hir_store_spec.spl
- test/01_unit/compiler/hir/symbol_display_name_spec.spl
- test/01_unit/compiler/hir/hir_lowering_begin_module_spec.spl
- test/01_unit/compiler/hir/qualified_import_call_spec.spl
- test/01_unit/compiler/hir/payload_binding_contest_names_agree_source_spec.spl
- test/01_unit/compiler/hir/hir_module_spec.spl
- test/01_unit/compiler/hir/hir_async_errors_spec.spl
- test/01_unit/compiler/hir/unannotated_module_const_type_spec.spl
- test/01_unit/compiler/hir/symbol_table_module_reset_spec.spl
- test/01_unit/compiler/hir/hir_module_callable_index_spec.spl
- test/01_unit/compiler/hir/hir_eval_spec.spl
- test/01_unit/compiler/hir/field_index_erased_receiver_spec.spl
- test/01_unit/compiler/hir/me_field_resolution_spec.spl
- test/01_unit/compiler/hir/hir_lower_spec.spl
- test/01_unit/compiler/hir/hir_codec_roundtrip_spec.spl
- test/01_unit/compiler/hir/self_context_pair_consistency_spec.spl
- test/01_unit/compiler/hir/hir_forward_decl_spec.spl
- test/01_unit/compiler/hir/seed_parity_scalar_type_names_spec.spl
- test/01_unit/compiler/hir/tuple_match_enum_subpattern_spec.spl
- test/01_unit/compiler/hir/nil_dict_receiver_phantom_option_spec.spl
- test/01_unit/compiler/hir/method_self_context_save_restore_spec.spl
- test/01_unit/compiler/hir/hir_lazy_import_registration_flag_regression_spec.spl
- test/01_unit/compiler/hir/enum_payload_range_or_frontend_exec_spec.spl
- test/01_unit/compiler/hir/module_surface_spec.spl
- test/01_unit/compiler/hir/hir_async_spec.spl
- test/01_unit/compiler/hir/hir_glob_reachable_miss_memo_spec.spl
- test/01_unit/compiler/hir/stage4_hir_value_name_dispatch_spec.spl
- test/01_unit/compiler/hir/legacy_builtin_alias_source_spec.spl
- test/01_unit/compiler/hir/resolve_import_module_value_spec.spl
- test/01_unit/compiler/hir/vulkan_gpu_attr_hir_spec.spl
- test/01_unit/compiler/hir/exhaustiveness/critical_wildcard_coverage_spec.spl
- test/01_unit/compiler/hir/imported_tuple_signature_dependency_spec.spl
- test/01_unit/compiler/hir/bootstrap_hir_store_spec.spl
- test/01_unit/compiler/hir/symbol_display_name_spec.spl
- test/01_unit/compiler/hir/hir_lowering_begin_module_spec.spl
- test/01_unit/compiler/hir/payload_binding_contest_names_agree_source_spec.spl
- test/01_unit/compiler/hir/hir_module_spec.spl
- test/01_unit/compiler/hir/hir_async_errors_spec.spl
- test/01_unit/compiler/hir/unannotated_module_const_type_spec.spl
- test/01_unit/compiler/hir/hir_module_callable_index_spec.spl
- test/01_unit/compiler/hir/hir_eval_spec.spl
- test/01_unit/compiler/hir/field_index_erased_receiver_spec.spl
- test/01_unit/compiler/hir/me_field_resolution_spec.spl
- test/01_unit/compiler/hir/hir_lower_spec.spl
- test/01_unit/compiler/hir/hir_codec_roundtrip_spec.spl
- test/01_unit/compiler/hir/self_context_pair_consistency_spec.spl
- test/01_unit/compiler/hir/seed_parity_scalar_type_names_spec.spl
- test/01_unit/compiler/hir/hir_verification_contract_preservation_spec.spl
- test/01_unit/compiler/hir/rv32_decode_helper_hir_lowering_spec.spl
- test/01_unit/compiler/hir/hir_import_registration_per_symbol_cost_spec.spl
- test/01_unit/compiler/hir/hir_symbol_table_all_functions_spec.spl
- test/01_unit/compiler/hir/imported_surface_callable_projection_spec.spl
- test/01_unit/compiler/hir/generic_impl_head_params_gate_spec.spl
- test/01_unit/compiler/hir/implicit_self_field_hir_probe_spec.spl
- test/01_unit/compiler/hir/hir_types_spec.spl
- test/01_unit/compiler/hir/enum_attributes_spec.spl
- test/01_unit/compiler/hir/enum_lowering_end_to_end_spec.spl
- test/01_unit/compiler/hir/module_surface_glob_export_origin_spec.spl
- test/01_unit/compiler/hir/float_primitive_cast_spec.spl

---

| Run ID | Status | Tests | Passed | Failed | Timed Out |
|--------|--------|-------|--------|--------|-----------|
| run_1787461121811624 | completed | 111 | 337 | 122 | 0 |
| run_1787460169307476 | completed | 1 | 1 | 0 | 0 |
| run_1787459801057382 | completed | 1 | 1 | 0 | 0 |
| run_1787044991418969 | crashed | 0 | 0 | 0 | 0 |
| run_1787044352338672 | crashed | 0 | 0 | 0 | 0 |
| run_1786952237405436 | crashed | 0 | 0 | 0 | 0 |
| run_1786952013677874 | crashed | 0 | 0 | 0 | 0 |
| run_1786948610656126 | crashed | 0 | 0 | 0 | 0 |
| run_1786947929319349 | crashed | 0 | 0 | 0 | 0 |
| run_1786947779912230 | crashed | 0 | 0 | 0 | 0 |

### 🔴 iffs identical V4 buffers as exact

| Test | Status | Runs | Mean (ms) | p50 (ms) |
|------|--------|------|-----------|----------|
| test/01_unit/compiler/async/async_desugar_integration_spec.spl | passed | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/compiler/async/async_frame_analysis_spec.spl | failed | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/compiler/async/async_integration_spec.spl | failed | 3 | 2563.246153846154 | 668.0 |
| test/01_unit/compiler/async/async_mir_interpreter_spec.spl | failed | 3 | 2818.396551724138 | 545.0 |
| test/01_unit/compiler/async/async_mir_spec.spl | failed | 2 | 1687.26 | 623.0 |
| test/01_unit/compiler/async/async_pipeline_spec.spl | passed | 2 | 1936.2727272727273 | 578.5 |
| test/01_unit/compiler/async/async_reservation_analysis_spec.spl | passed | 2 | 2293.048780487805 | 605.0 |
| test/01_unit/compiler/async/async_spawn_analysis_spec.spl | passed | 2 | 2733.9756097560976 | 566.0 |
| test/01_unit/compiler/async/async_state_machine_spec.spl | failed | 2 | 5776.694444444444 | 551.0 |
| test/01_unit/compiler/async/poll_generator_spec.spl | failed | 2 | 1679.9705882352941 | 524.0 |
| test/01_unit/compiler/async/state_enum_spec.spl | failed | 2 | 1098.3636363636363 | 591.0 |
| test/01_unit/compiler/async/suspension_analysis_spec.spl | failed | 2 | 1933.878787878788 | 673.0 |
| test/02_integration/net/http_content_encoding_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/compiler/verify/baremetal_noalloc_constraints_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/compiler/verification/cache_correctness_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/compiler/verification/deterministic_emission_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/compiler/verification/lean_basic_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/01_unit/compiler/verification/lean_block_integration_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/01_unit/compiler/verification/lean_codegen_spec.spl | unknown | 2 | 1687.26 | 623.0 |
| test/01_unit/compiler/verification/lean_workflow_spec.spl | unknown | 2 | 1936.2727272727273 | 578.5 |
| test/01_unit/compiler/verification/memory_capabilities_spec.spl | unknown | 2 | 2293.048780487805 | 605.0 |
| test/01_unit/compiler/verification/naming_spec.spl | unknown | 2 | 2733.9756097560976 | 566.0 |
| test/01_unit/compiler/verification/proof_reference_spec.spl | unknown | 2 | 5776.694444444444 | 551.0 |
| test/01_unit/compiler/verification/regeneration_spec.spl | unknown | 2 | 1679.9705882352941 | 524.0 |
| test/01_unit/compiler/verification/report_rendering_spec.spl | unknown | 2 | 1098.3636363636363 | 591.0 |
| test/01_unit/compiler/verification/tool_checker_spec.spl | unknown | 2 | 1933.878787878788 | 673.0 |
| test/01_unit/compiler/verification/toolchain_detection_spec.spl | passed | 2 | 1758.225806451613 | 480.0 |
| test/01_unit/compiler/verification/unified_attrs_spec.spl | failed | 2 | 611.6071428571429 | 503.5 |
| test/01_unit/compiler/verification/unsupported_construct_spec.spl | passed | 2 | 661.0384615384615 | 632.0 |
| test/01_unit/compiler/verification/verification_diagnostics_spec.spl | passed | 3 | 1255.375 | 508.0 |
| test/01_unit/compiler/assurance/assurance_schemas_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/compiler/assurance/dynamic_composition_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/compiler/assurance/flight_rules_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/01_unit/compiler/assurance/formal_delivery_gates_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/01_unit/compiler/assurance/formal_interfaces_spec.spl | unknown | 2 | 1687.26 | 623.0 |
| test/01_unit/compiler/assurance/formal_receipt_spec.spl | unknown | 2 | 1936.2727272727273 | 578.5 |
| test/01_unit/compiler/assurance/formal_status_spec.spl | unknown | 2 | 2293.048780487805 | 605.0 |
| test/01_unit/compiler/assurance/nat_normalizer_receipt_spec.spl | unknown | 2 | 2733.9756097560976 | 566.0 |
| test/01_unit/compiler/assurance/policy_five_site_convergence_spec.spl | unknown | 2 | 5776.694444444444 | 551.0 |
| test/01_unit/compiler/assurance/policy_graph_contamination_probe_spec.spl | unknown | 2 | 1679.9705882352941 | 524.0 |
| test/01_unit/compiler/assurance/proof_dag_spec.spl | unknown | 2 | 1098.3636363636363 | 591.0 |
| test/01_unit/compiler/assurance/sha512_integrity_receipt_spec.spl | unknown | 2 | 1933.878787878788 | 673.0 |
| test/01_unit/compiler/assurance/verified_release_gate_spec.spl | unknown | 2 | 1758.225806451613 | 480.0 |
| test/01_unit/compiler/mdsoc/aop_proceed_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/compiler/mdsoc/config_multi_dim_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/compiler/mdsoc/config_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/01_unit/compiler/mdsoc/construct_checker_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/01_unit/compiler/mdsoc/construct_types_spec.spl | unknown | 2 | 1687.26 | 623.0 |
| test/01_unit/compiler/mdsoc/cross_query_spec.spl | unknown | 2 | 1936.2727272727273 | 578.5 |
| test/01_unit/compiler/mdsoc/doc_validation_spec.spl | unknown | 2 | 2293.048780487805 | 605.0 |
| test/01_unit/compiler/mdsoc/feature_ports_spec.spl | unknown | 2 | 2733.9756097560976 | 566.0 |
| test/01_unit/compiler/mdsoc/layer_checker_spec.spl | unknown | 2 | 5776.694444444444 | 551.0 |
| test/01_unit/compiler/mdsoc/layer_ci_spec.spl | unknown | 2 | 1679.9705882352941 | 524.0 |
| test/01_unit/compiler/mdsoc/layer_enforcement_spec.spl | unknown | 2 | 1098.3636363636363 | 591.0 |
| test/01_unit/compiler/mdsoc/pipeline_integration_spec.spl | unknown | 2 | 1933.878787878788 | 673.0 |
| test/01_unit/compiler/mdsoc/transform_adapters_spec.spl | unknown | 2 | 1758.225806451613 | 480.0 |
| test/01_unit/compiler/mdsoc/types_spec.spl | unknown | 2 | 611.6071428571429 | 503.5 |
| test/01_unit/compiler/mdsoc/vc_import_spec.spl | unknown | 2 | 661.0384615384615 | 632.0 |
| test/01_unit/compiler/mdsoc/vc_static_spec.spl | unknown | 3 | 1255.375 | 508.0 |
| test/01_unit/compiler/mdsoc/weaving_support_spec.spl | passed | 2 | 806.95 | 686.5 |
| test/02_integration/doctest/discovery_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/07_security/csprng_salt_iv_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/compiler/visibility_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/compiler/60.mir_opt/general_patterns_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/compiler/60.mir_opt/hwir_opt_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/compiler/60.mir_opt/optimizer_manifest_backend_budget_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/01_unit/compiler/60.mir_opt/pass_descriptor_budget_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/01_unit/compiler/vhdl/hardware_spawn_lower_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/compiler/vhdl/vhdl_subprogram_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/compiler/vhdl/vhdl_testbench_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/01_unit/compiler/vhdl_riscv_gap_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/01_unit/compiler/vhdl_subprogram_spec.spl | unknown | 2 | 1687.26 | 623.0 |
| test/01_unit/compiler/vhdl_testbench_spec.spl | unknown | 2 | 1936.2727272727273 | 578.5 |
| test/01_unit/app/audit/audit_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/app/arch_check_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/02_integration/rust/meta/comment_only_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/app/auto_coverage_10_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/app/auto_coverage_1_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/app/auto_coverage_11_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/app/auto_coverage_12_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/01_unit/app/build/build_targets_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/app/build/feature_flags_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/app/build/repo_hygiene_gate_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/01_unit/app/build/change_classifier_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/01_unit/app/build/action_identity_spec.spl | unknown | 2 | 1687.26 | 623.0 |
| test/01_unit/app/build/opt_remarks_spec.spl | unknown | 2 | 1936.2727272727273 | 578.5 |
| test/01_unit/app/build/artifact_receipt_spec.spl | unknown | 2 | 2293.048780487805 | 605.0 |
| test/01_unit/app/build/bootstrap_policy_spec.spl | unknown | 2 | 2733.9756097560976 | 566.0 |
| test/01_unit/app/build/build_explain_spec.spl | unknown | 2 | 5776.694444444444 | 551.0 |
| test/01_unit/app/build_coverage_spec.spl | unknown | 2 | 1679.9705882352941 | 524.0 |
| test/03_system/coverage/coverage_check_api_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/03_system/coverage/coverage_core_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/03_system/coverage/coverage_doc_stats_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/03_system/coverage/coverage_runtime_ffi_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/03_system/coverage/coverage_test_runner_spec.spl | unknown | 2 | 1687.26 | 623.0 |
| test/01_unit/compiler/borrow/borrow_check_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/compiler/borrow/iso_move_assign_field_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/compiler/borrow/iso_move_pipeline_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/01_unit/compiler/borrow/iso_move_return_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/01_unit/compiler/borrow/iso_move_sites_spec.spl | unknown | 2 | 1687.26 | 623.0 |
| test/01_unit/compiler/borrow/iso_parse_pipeline_spec.spl | unknown | 2 | 1936.2727272727273 | 578.5 |
| test/01_unit/compiler/borrow/iso_use_after_move_e2e_spec.spl | unknown | 2 | 2293.048780487805 | 605.0 |
| test/01_unit/compiler/borrow/lifetime_spec.spl | unknown | 2 | 2733.9756097560976 | 566.0 |
| test/02_integration/watcher/watcher_backend_validation_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/02_integration/watcher/watcher_shb_integration_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/02_integration/watcher/watcher_smf_integration_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/01_unit/app/auto_coverage_5_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/02_integration/io/native_ops_dir_create_all_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/02_integration/io/native_ops_dir_create_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/02_integration/io/native_ops_dir_recursive_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/02_integration/io/native_ops_file_copy_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/02_integration/io/native_ops_file_read_write_spec.spl | unknown | 2 | 1687.26 | 623.0 |
| test/02_integration/io/native_ops_file_size_spec.spl | unknown | 2 | 1936.2727272727273 | 578.5 |
| test/feature/lib/gc_parity/gc_module_loader_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/feature/lib/gc_parity/nogc_sync_mut_contract_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/feature/lib/gc_parity/otp_behaviours_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/feature/lib/mcp/bootstrap_e2e_test.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/feature/lib/mcp/bootstrap_functions_test.spl | unknown | 2 | 1687.26 | 623.0 |
| test/feature/lib/mcp/bootstrap_import_test.spl | unknown | 2 | 1936.2727272727273 | 578.5 |
| test/feature/lib/mcp/bootstrap_protocol_test.spl | unknown | 2 | 2293.048780487805 | 605.0 |
| test/feature/lib/mcp/core_spec.spl | unknown | 2 | 2733.9756097560976 | 566.0 |
| test/feature/lib/mcp/handler_function_test.spl | unknown | 2 | 5776.694444444444 | 551.0 |
| test/feature/lib/mcp/handler_import_test.spl | unknown | 2 | 1679.9705882352941 | 524.0 |
| test/feature/lib/mcp/handler_registry_spec.spl | unknown | 2 | 1098.3636363636363 | 591.0 |
| test/feature/lib/mcp/helpers_spec.spl | unknown | 2 | 1933.878787878788 | 673.0 |
| test/feature/lib/mcp/integration_spec.spl | unknown | 2 | 1758.225806451613 | 480.0 |
| test/feature/lib/mcp/lazy_loading_v2_test.spl | unknown | 2 | 611.6071428571429 | 503.5 |
| test/feature/lib/mcp/schema_simple_test.spl | unknown | 2 | 661.0384615384615 | 632.0 |
| test/feature/lib/mcp/schema_spec.spl | unknown | 3 | 1255.375 | 508.0 |
| test/feature/lib/mcp/simple_import_test.spl | unknown | 2 | 806.95 | 686.5 |
| test/feature/lib/std/compiler/lexer_ffi_test.spl | failed | 2 | 1158.642857142857 | 483.0 |
| test/feature/lib/std/helpers_example_spec.spl | passed | 2 | 1686.4615384615386 | 466.0 |
| test/feature/lib/import_debug_spec.spl | passed | 3 | 682.0769230769231 | 663.0 |
| test/feature/lib/minimal_spec.spl | failed | 3 | 2055.923076923077 | 792.0 |
| test/05_perf/graphics_2d/backend_preference_startup_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/05_perf/graphics_2d/backend_probe_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/05_perf/graphics_2d/c_vs_simple_2d_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/05_perf/graphics_2d/cpu_simd_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/05_perf/graphics_2d/cuda_smoke_spec.spl | unknown | 2 | 1687.26 | 623.0 |
| test/05_perf/graphics_2d/metal_readback_proof_spec.spl | unknown | 2 | 1936.2727272727273 | 578.5 |
| test/05_perf/graphics_2d/metal_smoke_spec.spl | unknown | 2 | 2293.048780487805 | 605.0 |
| test/05_perf/graphics_2d/no_duplication_spec.spl | unknown | 2 | 2733.9756097560976 | 566.0 |
| test/05_perf/graphics_2d/optimization_plugin_spec.spl | unknown | 2 | 5776.694444444444 | 551.0 |
| test/05_perf/graphics_2d/shared_helpers_spec.spl | unknown | 2 | 1679.9705882352941 | 524.0 |
| test/05_perf/graphics_2d/shared_multilingual_gpu_fonts_perf_spec.spl | unknown | 2 | 1098.3636363636363 | 591.0 |
| test/05_perf/graphics_2d/simple_2d_vector_fonts_perf_spec.spl | unknown | 2 | 1933.878787878788 | 673.0 |
| test/05_perf/graphics_2d/vulkan_spirv_spec.spl | unknown | 2 | 1758.225806451613 | 480.0 |
| test/05_perf/graphics_2d/webgpu_real_spec.spl | unknown | 2 | 611.6071428571429 | 503.5 |
| test/05_perf/graphics_2d/wm_frame_pacing_spec.spl | unknown | 2 | 661.0384615384615 | 632.0 |
| test/05_perf/graphics_2d/report_spec.spl | unknown | 3 | 1255.375 | 508.0 |
| test/02_integration/sffi/callback_roundtrip_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/02_integration/sffi/direction_a_c_roundtrip_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/02_integration/sffi/direction_a_cpp_roundtrip_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/02_integration/sffi/direction_b_import_roundtrip_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/02_integration/sffi/layout_verification_roundtrip_spec.spl | unknown | 2 | 1687.26 | 623.0 |
| test/02_integration/sffi/rsa_sha512_reference_import_spec.spl | unknown | 2 | 1936.2727272727273 | 578.5 |
| test/feature/ml/tensor_dimensions_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/lib/baremetal/allocator_freelist_split_and_underflow_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/lib/baremetal/riscv/sbi_ipi_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/lib/baremetal/riscv/dtb_cpu_walker_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/01_unit/lib/baremetal/allocator_block_header_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/01_unit/lib/baremetal/allocator_real_memory_spec.spl | unknown | 2 | 1687.26 | 623.0 |
| test/01_unit/lib/blink/html_tree_builder_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/lib/blink/dom_node_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/lib/blink/hit_test_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/01_unit/lib/blink/document_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/01_unit/lib/blink/form_paint_spec.spl | unknown | 2 | 1687.26 | 623.0 |
| test/01_unit/lib/blink/css_tokenizer_spec.spl | unknown | 2 | 1936.2727272727273 | 578.5 |
| test/01_unit/lib/blink/render_lane_pipeline_spec.spl | unknown | 2 | 2293.048780487805 | 605.0 |
| test/01_unit/lib/blink/paint_tree_walker_spec.spl | unknown | 2 | 2733.9756097560976 | 566.0 |
| test/01_unit/lib/blink/url/url_parser_spec.spl | unknown | 2 | 5776.694444444444 | 551.0 |
| test/01_unit/lib/blink/css_inline_style_spec.spl | unknown | 2 | 1679.9705882352941 | 524.0 |
| test/01_unit/lib/blink/block_flow_spec.spl | unknown | 2 | 1098.3636363636363 | 591.0 |
| test/01_unit/lib/blink/inline_text_floats_spec.spl | unknown | 2 | 1933.878787878788 | 673.0 |
| test/01_unit/lib/blink/style_cascade_spec.spl | unknown | 2 | 1758.225806451613 | 480.0 |
| test/01_unit/lib/blink/paint_artifact_spec.spl | unknown | 2 | 611.6071428571429 | 503.5 |
| test/01_unit/lib/blink/block_flow_floats_spec.spl | unknown | 2 | 661.0384615384615 | 632.0 |
| test/01_unit/lib/blink/inline_flow_spec.spl | unknown | 3 | 1255.375 | 508.0 |
| test/01_unit/lib/blink/navigation_fetch_spec.spl | unknown | 2 | 806.95 | 686.5 |
| test/01_unit/lib/blink/html_tokenizer_entities_spec.spl | unknown | 2 | 1158.642857142857 | 483.0 |
| test/01_unit/lib/blink/paint_controller_spec.spl | unknown | 2 | 1686.4615384615386 | 466.0 |
| test/01_unit/lib/blink/scroll_manager_spec.spl | unknown | 3 | 682.0769230769231 | 663.0 |
| test/01_unit/lib/blink/html_tokenizer_tree_builder_pipeline_spec.spl | unknown | 3 | 2055.923076923077 | 792.0 |
| test/01_unit/lib/blink/css_parser_spec.spl | passed | 2 | 585.75 | 594.0 |
| test/01_unit/lib/blink/computed_style_spec.spl | passed | 2 | 1168.375 | 591.5 |
| test/01_unit/lib/blink/navigation_controller_spec.spl | passed | 2 | 3543.285714285714 | 713.0 |
| test/01_unit/lib/blink/style/user_agent_stylesheet_spec.spl | failed | 2 | 1645.5714285714287 | 809.0 |
| test/01_unit/lib/blink/inline_text_spec.spl | failed | 2 | 1030.5714285714287 | 583.0 |
| test/01_unit/lib/blink/image_paint_spec.spl | passed | 2 | 1145.0 | 594.0 |
| test/01_unit/lib/blink/input_event_spec.spl | passed | 2 | 4028.285714285714 | 505.0 |
| test/01_unit/lib/blink/style_shorthand_spec.spl | failed | 2 | 20489.5 | 551.0 |
| test/01_unit/lib/blink/render_lane_pixels_spec.spl | passed | 2 | 885.2 | 616.0 |
| test/01_unit/lib/blink/html_tokenizer_spec.spl | failed | 2 | 676.0 | 622.0 |
| test/01_unit/lib/blink/paint_chunk_spec.spl | failed | 2 | 519.8 | 540.0 |
| test/01_unit/lib/blink/flex_spec.spl | passed | 2 | 3088.4 | 827.0 |
| test/01_unit/lib/blink/css_selector_spec.spl | failed | 2 | 1033.2 | 628.0 |
| test/01_unit/lib/blink/paint/invalidation_spec.spl | failed | 2 | 746.5 | 627.0 |
| test/01_unit/lib/blink/paint/style_paint_spec.spl | passed | 2 | 737.25 | 753.5 |
| test/01_unit/lib/blink/paint/text_paint_spec.spl | passed | 2 | 1296.0 | 645.5 |
| test/01_unit/lib/blink/paint/effects_spec.spl | passed | 2 | 708.25 | 673.0 |
| test/01_unit/lib/blink/paint/border_paint_spec.spl | failed | 2 | 768.0 | 768.0 |
| test/01_unit/lib/blink/paint/effect_paint_spec.spl | passed | 2 | 673.0 | 625.0 |
| test/01_unit/lib/blink/values_length_spec.spl | failed | 2 | 740.25 | 610.0 |
| test/01_unit/lib/blink/table_flow_spec.spl | passed | 2 | 816.5 | 838.0 |
| test/01_unit/lib/blink/style_at_rules_spec.spl | failed | 2 | 2468.0 | 783.0 |
| test/01_unit/compiler/blocks/block_definition_three_level_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/compiler/blocks/block_outline_info_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/compiler/blocks/block_skip_policy_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/01_unit/compiler/blocks/builder_api_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/01_unit/compiler/blocks/easy_api_spec.spl | unknown | 2 | 1687.26 | 623.0 |
| test/01_unit/compiler/blocks/pre_lex_info_spec.spl | unknown | 2 | 1936.2727272727273 | 578.5 |
| test/01_unit/compiler/blocks/pre_lex_per_dsl_spec.spl | unknown | 2 | 2293.048780487805 | 605.0 |
| test/01_unit/compiler/blocks/testing_spec.spl | unknown | 2 | 2733.9756097560976 | 566.0 |
| test/01_unit/compiler/blocks/unified_registry_bootstrap_source_spec.spl | unknown | 2 | 5776.694444444444 | 551.0 |
| test/01_unit/compiler/blocks/utils_spec.spl | unknown | 2 | 1679.9705882352941 | 524.0 |
| test/01_unit/compiler/blocks/builder_api_basic_spec.spl | unknown | 2 | 1098.3636363636363 | 591.0 |
| test/01_unit/compiler/blocks/builder_default_parser_spec.spl | unknown | 2 | 1933.878787878788 | 673.0 |
| test/01_unit/compiler/blocks/easy_api_basic_spec.spl | unknown | 2 | 1758.225806451613 | 480.0 |
| test/01_unit/compiler/blocks/testing_framework_spec.spl | unknown | 2 | 611.6071428571429 | 503.5 |
| test/01_unit/compiler/blocks/utils_basic_spec.spl | unknown | 2 | 661.0384615384615 | 632.0 |
| test/03_system/game3d/rollball_production_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/02_integration/debug/hardware/hardware_check_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/02_integration/debug/hardware/stm32h7_openocd_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/02_integration/debug/hardware/stm32h7_stlink_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/02_integration/debug/hardware/stm32wb_openocd_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/02_integration/debug/hardware/stm32wb_stlink_spec.spl | unknown | 2 | 1687.26 | 623.0 |
| test/02_integration/debug/hardware/t32_gdb_bridge_spec.spl | unknown | 2 | 1936.2727272727273 | 578.5 |
| test/02_integration/debug/hardware/t32_native_spec.spl | unknown | 2 | 2293.048780487805 | 605.0 |
| test/02_integration/debug/hardware/t32_semihost_hello_spec.spl | unknown | 2 | 2733.9756097560976 | 566.0 |
| test/feature/mode_filter/all_modes_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/feature/mode_filter/interpreter_only_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/feature/mode_filter/native_only_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/feature/mode_filter/skip_native_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/01_unit/compiler/bootstrap/ast_native_arena_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/compiler/bootstrap/backend_helpers_shared_binding_contract_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/compiler/bootstrap/class_member_parser_parity_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/01_unit/compiler/bootstrap/driver_phase_entry_shared_binding_contract_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/01_unit/compiler/bootstrap/driver_symlink_source_dedup_spec.spl | unknown | 2 | 1687.26 | 623.0 |
| test/01_unit/compiler/bootstrap/entry_closure_bucket_count_contract_spec.spl | unknown | 2 | 1936.2727272727273 | 578.5 |
| test/01_unit/compiler/bootstrap/entry_closure_module_map_update_spec.spl | unknown | 2 | 2293.048780487805 | 605.0 |
| test/01_unit/compiler/bootstrap/flattened_linker_symbol_types_contract_spec.spl | unknown | 2 | 2733.9756097560976 | 566.0 |
| test/01_unit/compiler/bootstrap/hir_expression_shared_binding_contract_spec.spl | unknown | 2 | 5776.694444444444 | 551.0 |
| test/01_unit/compiler/bootstrap/hir_import_resolution_shared_binding_contract_spec.spl | unknown | 2 | 1679.9705882352941 | 524.0 |
| test/01_unit/compiler/bootstrap/hir_module_lowering_shared_binding_contract_spec.spl | unknown | 2 | 1098.3636363636363 | 591.0 |
| test/01_unit/compiler/bootstrap/hir_statement_shared_binding_contract_spec.spl | unknown | 2 | 1933.878787878788 | 673.0 |
| test/01_unit/compiler/bootstrap/hir_symbol_alias_owner_collision_spec.spl | unknown | 2 | 1758.225806451613 | 480.0 |
| test/01_unit/compiler/bootstrap/hir_symbol_table_shared_binding_contract_spec.spl | unknown | 2 | 611.6071428571429 | 503.5 |
| test/01_unit/compiler/bootstrap/interpreter_function_lookup_shared_binding_contract_spec.spl | unknown | 2 | 661.0384615384615 | 632.0 |
| test/01_unit/compiler/bootstrap/labeled_tuple_return_parser_spec.spl | unknown | 3 | 1255.375 | 508.0 |
| test/01_unit/compiler/bootstrap/lint_short_grammar_helper_import_contract_spec.spl | unknown | 2 | 806.95 | 686.5 |
| test/01_unit/compiler/bootstrap/llvm_aggregate_shared_binding_contract_spec.spl | unknown | 2 | 1158.642857142857 | 483.0 |
| test/01_unit/compiler/bootstrap/loader_metadata_helpers_contract_spec.spl | unknown | 2 | 1686.4615384615386 | 466.0 |
| test/01_unit/compiler/bootstrap/mir_call_destination_shared_binding_contract_spec.spl | unknown | 3 | 682.0769230769231 | 663.0 |
| test/01_unit/compiler/bootstrap/mir_expr_dispatch_shared_binding_contract_spec.spl | unknown | 3 | 2055.923076923077 | 792.0 |
| test/01_unit/compiler/bootstrap/mir_method_calls_shared_binding_contract_spec.spl | unknown | 2 | 585.75 | 594.0 |
| test/01_unit/compiler/bootstrap/mir_module_lowering_shared_binding_contract_spec.spl | unknown | 2 | 1168.375 | 591.5 |
| test/01_unit/compiler/bootstrap/mir_switch_calls_shared_binding_contract_spec.spl | unknown | 2 | 3543.285714285714 | 713.0 |
| test/01_unit/compiler/bootstrap/module_surface_canonical_once_spec.spl | unknown | 2 | 1645.5714285714287 | 809.0 |
| test/01_unit/compiler/bootstrap/module_surface_impl_retention_spec.spl | unknown | 2 | 1030.5714285714287 | 583.0 |
| test/01_unit/compiler/bootstrap/native_entry_closure_mode_contract_spec.spl | unknown | 2 | 1145.0 | 594.0 |
| test/01_unit/compiler/bootstrap/parser_multiline_shape_parity_spec.spl | unknown | 2 | 4028.285714285714 | 505.0 |
| test/01_unit/compiler/bootstrap/parser_self_parse_spec.spl | unknown | 2 | 20489.5 | 551.0 |
| test/01_unit/compiler/bootstrap/seed_jit_temp_project_hint_source_spec.spl | unknown | 2 | 885.2 | 616.0 |
| test/01_unit/compiler/bootstrap/specialized_template_context_contract_spec.spl | unknown | 2 | 676.0 | 622.0 |
| test/01_unit/compiler/bootstrap/stage2_bare_variant_owner_spec.spl | unknown | 2 | 519.8 | 540.0 |
| test/01_unit/compiler/bootstrap/stage2_source_shape_regression_spec.spl | unknown | 2 | 3088.4 | 827.0 |
| test/01_unit/compiler/bootstrap/stage4_manual_stage3_admission_contract_spec.spl | unknown | 2 | 1033.2 | 628.0 |
| test/01_unit/compiler/bootstrap/stage4_multiline_call_paren_spec.spl | unknown | 2 | 746.5 | 627.0 |
| test/01_unit/compiler/bootstrap/stage4_post_x86_platform_matrix_spec.spl | unknown | 2 | 737.25 | 753.5 |
| test/01_unit/compiler/bootstrap/stage4_smoke_gate_spec.spl | unknown | 2 | 1296.0 | 645.5 |
| test/01_unit/compiler/bootstrap/stage4_streaming_surfaces_contract_spec.spl | unknown | 2 | 708.25 | 673.0 |
| test/01_unit/compiler/bootstrap/stage4_unlimited_streaming_ownership_spec.spl | unknown | 2 | 768.0 | 768.0 |
| test/01_unit/compiler/bootstrap/tier_resolution_order_source_spec.spl | unknown | 2 | 673.0 | 625.0 |
| test/01_unit/compiler/bootstrap/trait_default_shared_binding_contract_spec.spl | unknown | 2 | 740.25 | 610.0 |
| test/01_unit/compiler/bootstrap/transient_parse_array_scope_spec.spl | unknown | 2 | 816.5 | 838.0 |
| test/01_unit/compiler/bootstrap/type_multiline_signature_parser_spec.spl | unknown | 2 | 2468.0 | 783.0 |
| test/01_unit/compiler/bootstrap/u64_fnv_literal_stage4_spec.spl | passed | 2 | 679.3333333333334 | 457.0 |
| test/01_unit/compiler/bootstrap/vhdl_artifact_source_shared_binding_contract_spec.spl | passed | 2 | 548.0 | 535.0 |
| test/01_unit/compiler/bootstrap/vhdl_call_definition_shared_binding_contract_spec.spl | passed | 2 | 737.3333333333334 | 658.0 |
| test/01_unit/compiler/bootstrap/vhdl_design_catalog_shared_binding_contract_spec.spl | passed | 2 | 512.0 | 548.0 |
| test/01_unit/compiler/bootstrap/vhdl_entity_shared_binding_contract_spec.spl | failed | 2 | 555.3333333333334 | 624.0 |
| test/01_unit/compiler/bootstrap/check_entry_target_routing_contract_spec.spl | passed | 2 | 525.6666666666666 | 524.0 |
| test/01_unit/compiler/bootstrap/entry_closure_physical_source_dedup_spec.spl | failed | 2 | 15202.333333333334 | 1012.0 |
| test/01_unit/compiler/cache/action_key_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/compiler/cache/cache_types_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/compiler/cache/cache_validator_smf_header_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/01_unit/compiler/cache/cache_validator_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/01_unit/compiler/cache/cas_store_spec.spl | unknown | 2 | 1687.26 | 623.0 |
| test/01_unit/compiler/cache/compile_options_hash_spec.spl | unknown | 2 | 1936.2727272727273 | 578.5 |
| test/01_unit/compiler/cache/file_stamp_spec.spl | unknown | 2 | 2293.048780487805 | 605.0 |
| test/01_unit/compiler/cache/lazy_section_spec.spl | unknown | 2 | 2733.9756097560976 | 566.0 |
| test/01_unit/compiler/cache/shb_mtime_spec.spl | unknown | 2 | 5776.694444444444 | 551.0 |
| test/01_unit/compiler/cache/smf_deps_validation_spec.spl | unknown | 2 | 1679.9705882352941 | 524.0 |
| test/01_unit/compiler/cache/dirty_closure_spec.spl | unknown | 2 | 1098.3636363636363 | 591.0 |
| test/01_unit/compiler/cache/interface_digest_spec.spl | unknown | 2 | 1933.878787878788 | 673.0 |
| test/01_unit/compiler/cache/target_graph_spec.spl | unknown | 2 | 1758.225806451613 | 480.0 |
| test/02_integration/ui/draw_ir_v2_v3_pixel_parity_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/02_integration/ui/event_backend_matrix_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/02_integration/ui/global_menubar_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/02_integration/ui/unified_packed_scene_nesting_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/02_integration/ui/widget_interact_model_spec.spl | unknown | 2 | 1687.26 | 623.0 |
| test/01_unit/compiler/common/attributes_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/compiler/common/config_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/compiler/common/di_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/01_unit/compiler/common/driver_manifest_attr_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/01_unit/compiler/common/effects_spec.spl | unknown | 2 | 1687.26 | 623.0 |
| test/01_unit/compiler/common/error_types_spec.spl | unknown | 2 | 1936.2727272727273 | 578.5 |
| test/01_unit/compiler/common/gc_config_spec.spl | unknown | 2 | 2293.048780487805 | 605.0 |
| test/01_unit/compiler/common/task_policy_attr_spec.spl | unknown | 2 | 2733.9756097560976 | 566.0 |
| test/01_unit/compiler/common/export_attr_spec.spl | unknown | 2 | 5776.694444444444 | 551.0 |
| test/feature/plugin/custom_block_plugin_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/feature/plugin/plugin_startup_block_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/feature/plugin/runtime_api_plugin_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/feature/plugin/sugar_plugin_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/03_system/helpers/text_helpers_p1_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/compiler/extern/rt_file_read_bytes_single_extern_signature_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/lib/text/text_index_slice_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/lib/text/text_length_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/lib/text/text_search_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/01_unit/lib/text/utf8_validation_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/01_unit/compiler/di/di_config_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/compiler/di/di_lock_phases_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/compiler/di/di_lock_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/01_unit/compiler/di/di_proxy_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/01_unit/compiler/di/di_runtime_slots_spec.spl | unknown | 2 | 1687.26 | 623.0 |
| test/01_unit/compiler/di/di_runtime_spec.spl | unknown | 2 | 1936.2727272727273 | 578.5 |
| test/01_unit/compiler/di/di_validation_spec.spl | unknown | 2 | 2293.048780487805 | 605.0 |
| test/01_unit/compiler/di/export_as_spec.spl | unknown | 2 | 2733.9756097560976 | 566.0 |
| test/01_unit/compiler/di/extensions_phases_spec.spl | unknown | 2 | 5776.694444444444 | 551.0 |
| test/01_unit/compiler/di/extensions_spec.spl | unknown | 2 | 1679.9705882352941 | 524.0 |
| test/01_unit/compiler/diagnostics/span_merge_spec.spl | unknown | 2 | 1098.3636363636363 | 591.0 |
| test/01_unit/compiler/diagnostic_formatter_contract_spec.spl | unknown | 2 | 1933.878787878788 | 673.0 |
| test/01_unit/compiler/dict_array_membership_tagged_key_spec.spl | unknown | 2 | 1758.225806451613 | 480.0 |
| test/01_unit/compiler/dict_bracket_vs_set_spec.spl | unknown | 2 | 611.6071428571429 | 503.5 |
| test/01_unit/compiler/dict_class_field_contains_key_after_insert_spec.spl | unknown | 2 | 661.0384615384615 | 632.0 |
| test/01_unit/compiler/dict_get_miss_returns_nil_spec.spl | unknown | 3 | 1255.375 | 508.0 |
| test/01_unit/compiler/diagnostic_predicate_empty_state_spec.spl | unknown | 2 | 806.95 | 686.5 |
| test/01_unit/lib/driver/fat32_file_io_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/lib/driver/registry_integration_test.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/lib/driver/fat32_driver_adapter_test.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/01_unit/lib/driver/driver_manifest_test.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/01_unit/lib/driver/null_block_driver_test.spl | unknown | 2 | 1687.26 | 623.0 |
| test/01_unit/lib/ecs/ecs_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/lib/ffi/ffi_wrappers_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/lib/ffi/ffi_basics_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/lib/ffi/dynamic_versioned_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/01_unit/lib/ffi/ffi_signature_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/01_unit/lib/extended/execution_task_unit_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/lib/extended/execution_thread_integration_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/lib/extended/hooks_before_integration_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/01_unit/lib/extended/memory_arena_unit_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/01_unit/lib/extended/collections_graph_unit_spec.spl | unknown | 2 | 1687.26 | 623.0 |
| test/01_unit/lib/extended/torch_loss_unit_spec.spl | unknown | 2 | 1936.2727272727273 | 578.5 |
| test/01_unit/lib/extended/execution_context_integration_spec.spl | unknown | 2 | 2293.048780487805 | 605.0 |
| test/01_unit/lib/extended/cuda_stream_unit_spec.spl | unknown | 2 | 2733.9756097560976 | 566.0 |
| test/01_unit/lib/extended/collections_heap_unit_spec.spl | unknown | 2 | 5776.694444444444 | 551.0 |
| test/01_unit/lib/extended/hooks_after_unit_spec.spl | unknown | 2 | 1679.9705882352941 | 524.0 |
| test/01_unit/lib/extended/collections_tree_unit_spec.spl | unknown | 2 | 1098.3636363636363 | 591.0 |
| test/01_unit/lib/extended/memory_gc_integration_spec.spl | unknown | 2 | 1933.878787878788 | 673.0 |
| test/01_unit/lib/extended/hooks_around_unit_spec.spl | unknown | 2 | 1758.225806451613 | 480.0 |
| test/01_unit/lib/extended/memory_alloc_unit_spec.spl | unknown | 2 | 611.6071428571429 | 503.5 |
| test/01_unit/lib/extended/pure_function_unit_spec.spl | unknown | 2 | 661.0384615384615 | 632.0 |
| test/01_unit/lib/extended/qemu_system_integration_spec.spl | unknown | 3 | 1255.375 | 508.0 |
| test/01_unit/lib/extended/gpu_buffer_integration_spec.spl | unknown | 2 | 806.95 | 686.5 |
| test/01_unit/lib/extended/pure_function_integration_spec.spl | unknown | 2 | 1158.642857142857 | 483.0 |
| test/01_unit/lib/extended/collections_heap_integration_spec.spl | unknown | 2 | 1686.4615384615386 | 466.0 |
| test/01_unit/lib/extended/qemu_device_unit_spec.spl | unknown | 3 | 682.0769230769231 | 663.0 |
| test/01_unit/lib/extended/cuda_memory_integration_spec.spl | unknown | 3 | 2055.923076923077 | 792.0 |
| test/01_unit/lib/extended/collections_tree_integration_spec.spl | unknown | 2 | 585.75 | 594.0 |
| test/01_unit/lib/extended/hooks_around_integration_spec.spl | unknown | 2 | 1168.375 | 591.5 |
| test/01_unit/lib/extended/hooks_after_integration_spec.spl | unknown | 2 | 3543.285714285714 | 713.0 |
| test/01_unit/lib/extended/gpu_buffer_unit_spec.spl | unknown | 2 | 1645.5714285714287 | 809.0 |
| test/01_unit/lib/extended/execution_task_integration_spec.spl | unknown | 2 | 1030.5714285714287 | 583.0 |
| test/01_unit/lib/extended/hooks_error_integration_spec.spl | unknown | 2 | 1145.0 | 594.0 |
| test/01_unit/lib/extended/cuda_device_unit_spec.spl | unknown | 2 | 4028.285714285714 | 505.0 |
| test/01_unit/lib/extended/cuda_stream_integration_spec.spl | unknown | 2 | 20489.5 | 551.0 |
| test/01_unit/lib/extended/qemu_system_unit_spec.spl | unknown | 2 | 885.2 | 616.0 |
| test/01_unit/lib/extended/hooks_before_unit_spec.spl | unknown | 2 | 676.0 | 622.0 |
| test/01_unit/lib/extended/memory_pool_integration_spec.spl | unknown | 2 | 519.8 | 540.0 |
| test/01_unit/lib/extended/pure_persistent_unit_spec.spl | unknown | 2 | 3088.4 | 827.0 |
| test/01_unit/lib/extended/pure_immutable_integration_spec.spl | unknown | 2 | 1033.2 | 628.0 |
| test/01_unit/lib/extended/execution_fiber_integration_spec.spl | unknown | 2 | 746.5 | 627.0 |
| test/01_unit/lib/extended/torch_tensor_integration_spec.spl | unknown | 2 | 737.25 | 753.5 |
| test/01_unit/lib/extended/collections_trie_integration_spec.spl | unknown | 2 | 1296.0 | 645.5 |
| test/01_unit/lib/extended/pure_immutable_unit_spec.spl | unknown | 2 | 708.25 | 673.0 |
| test/01_unit/lib/extended/collections_trie_unit_spec.spl | unknown | 2 | 768.0 | 768.0 |
| test/01_unit/lib/extended/torch_data_integration_spec.spl | unknown | 2 | 673.0 | 625.0 |
| test/01_unit/lib/extended/torch_tensor_unit_spec.spl | unknown | 2 | 740.25 | 610.0 |
| test/01_unit/lib/extended/gpu_compute_integration_spec.spl | unknown | 2 | 816.5 | 838.0 |
| test/01_unit/lib/extended/gpu_compute_unit_spec.spl | unknown | 2 | 2468.0 | 783.0 |
| test/01_unit/lib/extended/cuda_kernel_integration_spec.spl | unknown | 2 | 679.3333333333334 | 457.0 |
| test/01_unit/lib/extended/torch_optim_unit_spec.spl | unknown | 2 | 548.0 | 535.0 |
| test/01_unit/lib/extended/hooks_error_unit_spec.spl | unknown | 2 | 737.3333333333334 | 658.0 |
| test/01_unit/lib/extended/cuda_device_integration_spec.spl | unknown | 2 | 512.0 | 548.0 |
| test/01_unit/lib/extended/gpu_shader_integration_spec.spl | unknown | 2 | 555.3333333333334 | 624.0 |
| test/01_unit/lib/extended/execution_thread_unit_spec.spl | unknown | 2 | 525.6666666666666 | 524.0 |
| test/01_unit/lib/extended/execution_fiber_unit_spec.spl | unknown | 2 | 15202.333333333334 | 1012.0 |
| test/01_unit/lib/extended/memory_pool_unit_spec.spl | failed | 2 | 572.5 | 572.5 |
| test/01_unit/lib/extended/execution_context_unit_spec.spl | passed | 2 | 433.0 | 433.0 |
| test/01_unit/lib/extended/qemu_user_integration_spec.spl | failed | 2 | 993.0 | 993.0 |
| test/01_unit/lib/extended/cuda_kernel_unit_spec.spl | passed | 2 | 418.0 | 418.0 |
| test/01_unit/lib/extended/gpu_pipeline_integration_spec.spl | failed | 2 | 364.0 | 364.0 |
| test/01_unit/lib/extended/collections_graph_integration_spec.spl | passed | 2 | 441.0 | 441.0 |
| test/01_unit/lib/extended/torch_nn_integration_spec.spl | passed | 2 | 420.0 | 420.0 |
| test/01_unit/lib/extended/gpu_pipeline_unit_spec.spl | failed | 2 | 436.0 | 436.0 |
| test/01_unit/lib/extended/torch_nn_unit_spec.spl | passed | 2 | 440.0 | 440.0 |
| test/01_unit/lib/extended/memory_arena_integration_spec.spl | failed | 2 | 435.0 | 435.0 |
| test/01_unit/lib/extended/torch_data_unit_spec.spl | passed | 2 | 446.0 | 446.0 |
| test/01_unit/lib/extended/qemu_user_unit_spec.spl | failed | 2 | 361.0 | 361.0 |
| test/01_unit/lib/extended/pure_persistent_integration_spec.spl | passed | 2 | 366.0 | 366.0 |
| test/01_unit/lib/extended/torch_optim_integration_spec.spl | passed | 2 | 447.0 | 447.0 |
| test/01_unit/lib/extended/cuda_event_integration_spec.spl | passed | 2 | 609.0 | 609.0 |
| test/01_unit/lib/extended/qemu_device_integration_spec.spl | failed | 2 | 2754.0 | 2754.0 |
| test/01_unit/lib/extended/gpu_shader_unit_spec.spl | passed | 2 | 932.0 | 932.0 |
| test/01_unit/lib/extended/torch_loss_integration_spec.spl | passed | 2 | 637.0 | 637.0 |
| test/01_unit/lib/extended/cuda_event_unit_spec.spl | failed | 2 | 593.0 | 593.0 |
| test/01_unit/lib/extended/memory_gc_unit_spec.spl | passed | 2 | 868.0 | 868.0 |
| test/01_unit/lib/extended/memory_alloc_integration_spec.spl | passed | 2 | 713.0 | 713.0 |
| test/01_unit/lib/extended/gpu_render_unit_spec.spl | passed | 2 | 399.0 | 399.0 |
| test/01_unit/lib/extended/cuda_memory_unit_spec.spl | passed | 2 | 717.0 | 717.0 |
| test/01_unit/lib/extended/gpu_render_integration_spec.spl | failed | 2 | 601.0 | 601.0 |
| test/01_unit/lib/gc_async_immut/root_pmap_native_probe_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/lib/gc_async_immut/facade_resolution_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/lib/gc_async_immut/persistent_vec_native_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/01_unit/lib/gc_async_immut/vector_push_empty_native_probe_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/01_unit/lib/gc_async_immut/versioned_native_probe_spec.spl | unknown | 2 | 1687.26 | 623.0 |
| test/01_unit/lib/gc_async_immut/native_combinators_spec.spl | unknown | 2 | 1936.2727272727273 | 578.5 |
| test/01_unit/lib/gc_async_immut/set_facade_native_spec.spl | unknown | 2 | 2293.048780487805 | 605.0 |
| test/01_unit/lib/gc_async_immut/vector_empty_native_probe_spec.spl | unknown | 2 | 2733.9756097560976 | 566.0 |
| test/01_unit/lib/gc_async_immut/trie_root_facade_native_spec.spl | unknown | 2 | 5776.694444444444 | 551.0 |
| test/01_unit/lib/gc_async_immut/map_facade_native_spec.spl | unknown | 2 | 1679.9705882352941 | 524.0 |
| test/01_unit/lib/gc_async_immut/atom_native_probe_spec.spl | unknown | 2 | 1098.3636363636363 | 591.0 |
| test/01_unit/lib/gc_async_immut/root_native_probe_spec.spl | unknown | 2 | 1933.878787878788 | 673.0 |
| test/01_unit/lib/gc_async_immut/trie_facade_native_spec.spl | unknown | 2 | 1758.225806451613 | 480.0 |
| test/01_unit/lib/gc_async_immut/persistent_collections_native_spec.spl | unknown | 2 | 611.6071428571429 | 503.5 |
| test/01_unit/lib/gc_async_immut/root_version_native_probe_spec.spl | unknown | 2 | 661.0384615384615 | 632.0 |
| test/01_unit/compiler/interpreter_extern/sdl3_registration_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/compiler/interpreter_extern/opengl_registration_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/compiler/interpreter_extern/file_char_device_registration_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/01_unit/compiler/interpreter_extern/glfw_registration_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/01_unit/compiler/interpreter_extern/oneapi_registration_spec.spl | unknown | 2 | 1687.26 | 623.0 |
| test/01_unit/compiler/interpreter_extern/capability_gap_spec.spl | unknown | 2 | 1936.2727272727273 | 578.5 |
| test/01_unit/compiler/interpreter_extern/audio_registration_spec.spl | unknown | 2 | 2293.048780487805 | 605.0 |
| test/01_unit/compiler/interpreter_extern/fb_image_log_socket_registration_spec.spl | unknown | 2 | 2733.9756097560976 | 566.0 |
| test/01_unit/compiler/irdsl/parser_validator_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/lib/gc_sync_immut/facade_resolution_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/lib/gc_sync_immut/map_facade_native_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/lib/gc_sync_immut/native_combinators_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/01_unit/lib/gc_sync_immut/persistent_collections_native_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/01_unit/lib/gc_sync_immut/persistent_vec_native_spec.spl | unknown | 2 | 1687.26 | 623.0 |
| test/01_unit/lib/gc_sync_immut/set_facade_native_spec.spl | unknown | 2 | 1936.2727272727273 | 578.5 |
| test/01_unit/lib/gc_sync_immut/trie_facade_native_spec.spl | unknown | 2 | 2293.048780487805 | 605.0 |
| test/01_unit/lib/gc_sync_immut/trie_root_facade_native_spec.spl | unknown | 2 | 2733.9756097560976 | 566.0 |
| test/02_integration/svmg/conformance/conformance_suite_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/02_integration/core/common_compression_framework_facade_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/02_integration/core/core_integration_10_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/02_integration/core/core_integration_11_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/02_integration/core/core_integration_12_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/02_integration/core/core_integration_13_spec.spl | unknown | 2 | 1687.26 | 623.0 |
| test/02_integration/core/core_integration_14_spec.spl | unknown | 2 | 1936.2727272727273 | 578.5 |
| test/02_integration/core/core_integration_15_spec.spl | unknown | 2 | 2293.048780487805 | 605.0 |
| test/02_integration/core/core_integration_16_spec.spl | unknown | 2 | 2733.9756097560976 | 566.0 |
| test/02_integration/core/core_integration_17_spec.spl | unknown | 2 | 5776.694444444444 | 551.0 |
| test/02_integration/core/core_integration_18_spec.spl | unknown | 2 | 1679.9705882352941 | 524.0 |
| test/02_integration/core/core_integration_19_spec.spl | unknown | 2 | 1098.3636363636363 | 591.0 |
| test/02_integration/core/core_integration_1_spec.spl | unknown | 2 | 1933.878787878788 | 673.0 |
| test/02_integration/core/core_integration_20_spec.spl | unknown | 2 | 1758.225806451613 | 480.0 |
| test/02_integration/core/core_integration_21_spec.spl | unknown | 2 | 611.6071428571429 | 503.5 |
| test/02_integration/core/core_integration_22_spec.spl | unknown | 2 | 661.0384615384615 | 632.0 |
| test/02_integration/core/core_integration_23_spec.spl | unknown | 3 | 1255.375 | 508.0 |
| test/02_integration/core/core_integration_24_spec.spl | unknown | 2 | 806.95 | 686.5 |
| test/02_integration/core/core_integration_25_spec.spl | unknown | 2 | 1158.642857142857 | 483.0 |
| test/02_integration/core/core_integration_26_spec.spl | unknown | 2 | 1686.4615384615386 | 466.0 |
| test/02_integration/core/core_integration_27_spec.spl | unknown | 3 | 682.0769230769231 | 663.0 |
| test/02_integration/core/core_integration_28_spec.spl | unknown | 3 | 2055.923076923077 | 792.0 |
| test/02_integration/core/core_integration_29_spec.spl | unknown | 2 | 585.75 | 594.0 |
| test/02_integration/core/core_integration_2_spec.spl | unknown | 2 | 1168.375 | 591.5 |
| test/02_integration/core/core_integration_30_spec.spl | unknown | 2 | 3543.285714285714 | 713.0 |
| test/02_integration/core/core_integration_31_spec.spl | unknown | 2 | 1645.5714285714287 | 809.0 |
| test/02_integration/core/core_integration_32_spec.spl | unknown | 2 | 1030.5714285714287 | 583.0 |
| test/02_integration/core/core_integration_33_spec.spl | unknown | 2 | 1145.0 | 594.0 |
| test/02_integration/core/core_integration_34_spec.spl | unknown | 2 | 4028.285714285714 | 505.0 |
| test/02_integration/core/core_integration_35_spec.spl | unknown | 2 | 20489.5 | 551.0 |
| test/02_integration/core/core_integration_36_spec.spl | unknown | 2 | 885.2 | 616.0 |
| test/02_integration/core/core_integration_37_spec.spl | unknown | 2 | 676.0 | 622.0 |
| test/02_integration/core/core_integration_38_spec.spl | unknown | 2 | 519.8 | 540.0 |
| test/02_integration/core/core_integration_39_spec.spl | unknown | 2 | 3088.4 | 827.0 |
| test/02_integration/core/core_integration_3_spec.spl | unknown | 2 | 1033.2 | 628.0 |
| test/02_integration/core/core_integration_40_spec.spl | unknown | 2 | 746.5 | 627.0 |
| test/02_integration/core/core_integration_41_spec.spl | unknown | 2 | 737.25 | 753.5 |
| test/02_integration/core/core_integration_42_spec.spl | unknown | 2 | 1296.0 | 645.5 |
| test/02_integration/core/core_integration_43_spec.spl | unknown | 2 | 708.25 | 673.0 |
| test/02_integration/core/core_integration_44_spec.spl | unknown | 2 | 768.0 | 768.0 |
| test/02_integration/core/core_integration_45_spec.spl | unknown | 2 | 673.0 | 625.0 |
| test/02_integration/core/core_integration_46_spec.spl | unknown | 2 | 740.25 | 610.0 |
| test/02_integration/core/core_integration_47_spec.spl | unknown | 2 | 816.5 | 838.0 |
| test/02_integration/core/core_integration_48_spec.spl | unknown | 2 | 2468.0 | 783.0 |
| test/02_integration/core/core_integration_49_spec.spl | unknown | 2 | 679.3333333333334 | 457.0 |
| test/02_integration/core/core_integration_4_spec.spl | unknown | 2 | 548.0 | 535.0 |
| test/02_integration/core/core_integration_50_spec.spl | unknown | 2 | 737.3333333333334 | 658.0 |
| test/02_integration/core/core_integration_5_spec.spl | unknown | 2 | 512.0 | 548.0 |
| test/02_integration/core/core_integration_6_spec.spl | unknown | 2 | 555.3333333333334 | 624.0 |
| test/02_integration/core/core_integration_7_spec.spl | unknown | 2 | 525.6666666666666 | 524.0 |
| test/02_integration/core/core_integration_8_spec.spl | unknown | 2 | 15202.333333333334 | 1012.0 |
| test/02_integration/core/core_integration_9_spec.spl | unknown | 2 | 572.5 | 572.5 |
| test/01_unit/compiler/lint/bare_primitive_internal_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/compiler/lint/collection_array_rebuild_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/compiler/lint/collection_easy_fix_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/01_unit/compiler/lint/collection_index_mutation_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/01_unit/compiler/lint/const_ref_default_spec.spl | unknown | 2 | 1687.26 | 623.0 |
| test/01_unit/compiler/lint/critical_file_guard_spec.spl | unknown | 2 | 1936.2727272727273 | 578.5 |
| test/01_unit/compiler/lint/feature_tracking_done_gate_spec.spl | unknown | 2 | 2293.048780487805 | 605.0 |
| test/01_unit/compiler/lint/lint_profile_spec.spl | unknown | 2 | 2733.9756097560976 | 566.0 |
| test/01_unit/compiler/lint/llvm_backend_type_safety_spec.spl | unknown | 2 | 5776.694444444444 | 551.0 |
| test/01_unit/compiler/lint/mcp_perf_lint_spec.spl | unknown | 2 | 1679.9705882352941 | 524.0 |
| test/01_unit/compiler/lint/module_init_literal_spec.spl | unknown | 2 | 1098.3636363636363 | 591.0 |
| test/01_unit/compiler/lint/option_me_call_spec.spl | unknown | 2 | 1933.878787878788 | 673.0 |
| test/01_unit/compiler/lint/parse001_spec_files_spec.spl | unknown | 2 | 1758.225806451613 | 480.0 |
| test/01_unit/compiler/lint/primitive_types_parity_spec.spl | unknown | 2 | 611.6071428571429 | 503.5 |
| test/01_unit/compiler/lint/public_doc_spec.spl | unknown | 2 | 661.0384615384615 | 632.0 |
| test/01_unit/compiler/lint/raw_rt_access_spec.spl | unknown | 3 | 1255.375 | 508.0 |
| test/01_unit/compiler/lint/remote_exec_lint_spec.spl | unknown | 2 | 806.95 | 686.5 |
| test/01_unit/compiler/lint/required_comment_cli_spec.spl | unknown | 2 | 1158.642857142857 | 483.0 |
| test/01_unit/compiler/lint/riscv_rtl_debuggability_spec.spl | unknown | 2 | 1686.4615384615386 | 466.0 |
| test/01_unit/compiler/lint/script_language_spec.spl | unknown | 3 | 682.0769230769231 | 663.0 |
| test/01_unit/compiler/lint/semantic_api_checker_spec.spl | unknown | 3 | 2055.923076923077 | 792.0 |
| test/01_unit/compiler/lint/simd_opportunity_lint_spec.spl | unknown | 2 | 585.75 | 594.0 |
| test/01_unit/compiler/lint/stub_impl_spec.spl | unknown | 2 | 1168.375 | 591.5 |
| test/01_unit/compiler/lint/test_lint_fn_spec.spl | unknown | 2 | 3543.285714285714 | 713.0 |
| test/01_unit/compiler/lint/unwrapped_foreign_resource_spec.spl | unknown | 2 | 1645.5714285714287 | 809.0 |
| test/01_unit/compiler/lint/use_resolution_w0407_severity_spec.spl | unknown | 2 | 1030.5714285714287 | 583.0 |
| test/01_unit/compiler/lint/wide_public_spec.spl | unknown | 2 | 1145.0 | 594.0 |
| test/01_unit/compiler/lint/star_export_lint_spec.spl | unknown | 2 | 4028.285714285714 | 505.0 |
| test/02_integration/infra/counterpart/foundation_redteam_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/02_integration/infra/counterpart/worker_isolation_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/lib/gui/browser_window_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/lib/gui/menu_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/lib/gui/pure_core_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/01_unit/lib/gui/pure_gui_release_lane_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/01_unit/lib/gui/pure_smf_dynlib_perf_spec.spl | unknown | 2 | 1687.26 | 623.0 |
| test/01_unit/compiler/macros/template_kind_can_follow_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/compiler/macros/macro_integration_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/compiler/macros/macro_check_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/02_integration/spec/coverage_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/02_integration/spec/formatter_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/02_integration/spec/mock_policy_execution_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/02_integration/spec/runner_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/01_unit/lib/host_io/fileio_async_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/lib/host_io/net_async_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/lib/host_io/stdio_async_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/01_unit/lib/hardware/fpga_k26/k26_axi_hp_bridge_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/lib/hardware/fpga_k26/k26_kv260_rv64_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/lib/hardware/fpga_k26/k26_soc_top_vexriscv_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/01_unit/lib/hardware/fpga_k26/k26_wb_axi_hp_bridge_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/01_unit/lib/hardware/fpga_linux/fpga_synthesis_rv64_spec.spl | unknown | 2 | 1687.26 | 623.0 |
| test/01_unit/lib/hardware/fpga_linux/product_bus_adapter_spec.spl | unknown | 2 | 1936.2727272727273 | 578.5 |
| test/01_unit/lib/hardware/fpga_linux/rv64_product_soc_top_spec.spl | unknown | 2 | 2293.048780487805 | 605.0 |
| test/01_unit/lib/hardware/fpga_linux/soc_vhdl_gen_rv64_spec.spl | unknown | 2 | 2733.9756097560976 | 566.0 |
| test/01_unit/lib/hardware/fpga_linux/synthesis_wrapper_vexriscv_spec.spl | unknown | 2 | 5776.694444444444 | 551.0 |
| test/01_unit/lib/hardware/link_mux/jtag_debug_scenario_spec.spl | unknown | 2 | 1679.9705882352941 | 524.0 |
| test/01_unit/lib/hardware/link_mux/jtag_units_spec.spl | unknown | 2 | 1098.3636363636363 | 591.0 |
| test/01_unit/lib/hardware/opensource_rtl/vexriscv_smp/vexriscv_smp_import_spec.spl | unknown | 2 | 1933.878787878788 | 673.0 |
| test/01_unit/lib/hardware/riscv_common/riscv_compressed_mission_critical_spec.spl | unknown | 2 | 1758.225806451613 | 480.0 |
| test/01_unit/lib/hardware/riscv_common/riscv_compressed_zca_seed_spec.spl | unknown | 2 | 611.6071428571429 | 503.5 |
| test/01_unit/lib/hardware/riscv_common/riscv_scalar_isa_database_spec.spl | unknown | 2 | 661.0384615384615 | 632.0 |
| test/01_unit/lib/hardware/riscv_product_ports_source_spec.spl | unknown | 3 | 1255.375 | 508.0 |
| test/01_unit/lib/hardware/rv64gc_rtl/core64_imac_protected_spec.spl | unknown | 2 | 806.95 | 686.5 |
| test/01_unit/lib/hardware/rv64gc_rtl/core64_integration_spec.spl | unknown | 2 | 1158.642857142857 | 483.0 |
| test/01_unit/lib/hardware/rv64gc_rtl/core_protected_cycle_spec.spl | unknown | 2 | 1686.4615384615386 | 466.0 |
| test/01_unit/lib/hardware/rv64gc_rtl/imac_synth_source_closure_spec.spl | unknown | 3 | 682.0769230769231 | 663.0 |
| test/01_unit/lib/hardware/rv64gc_rtl/register_banks_spec.spl | unknown | 3 | 2055.923076923077 | 792.0 |
| test/01_unit/lib/hardware/rv64gc_rtl/rv64_imac_misa_spec.spl | unknown | 2 | 585.75 | 594.0 |
| test/01_unit/lib/hardware/soc_rtl/eth_fcs_spec.spl | unknown | 2 | 1168.375 | 591.5 |
| test/01_unit/lib/hardware/soc_rtl/soc_dtb_asset_spec.spl | unknown | 2 | 3543.285714285714 | 713.0 |
| test/01_unit/lib/hardware/soc_rtl/soc_top_64_protected_spec.spl | unknown | 2 | 1645.5714285714287 | 809.0 |
| test/01_unit/lib/hardware/soc_rtl/soc_top_64_spec.spl | unknown | 2 | 1030.5714285714287 | 583.0 |
| test/01_unit/lib/hardware/soc_rtl/soc_top_rv32_protected_spec.spl | unknown | 2 | 1145.0 | 594.0 |
| test/01_unit/lib/hardware/vhdl_gen/exec_core_gen_spec.spl | unknown | 2 | 4028.285714285714 | 505.0 |
| test/01_unit/lib/hardware/vhdl_gen/rv32_trap_completeness_spec.spl | unknown | 2 | 20489.5 | 551.0 |
| test/02_integration/lib/std/improvements/stdlib_improvements_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/02_integration/lib/std/diagram/diagram_integration_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/02_integration/lib/std/ml/simple_math_integration_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/02_integration/lib/std/failsafe/crash_prevention_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/02_integration/lib/std/doctest/discovery_spec.spl | unknown | 2 | 1687.26 | 623.0 |
| test/02_integration/lib/std/screenshot/screenshot_ffi_spec.spl | unknown | 2 | 1936.2727272727273 | 578.5 |
| test/02_integration/lib/persistence_intensive_spec.spl | unknown | 2 | 2293.048780487805 | 605.0 |
| test/02_integration/lib/database_query_spec.spl | unknown | 2 | 2733.9756097560976 | 566.0 |
| test/02_integration/lib/thread_pool_async_spec.spl | unknown | 2 | 5776.694444444444 | 551.0 |
| test/02_integration/lib/database_e2e_spec.spl | unknown | 2 | 1679.9705882352941 | 524.0 |
| test/02_integration/lib/stdlib_intensive_spec.spl | unknown | 2 | 1098.3636363636363 | 591.0 |
| test/02_integration/lib/failsafe_integration_spec.spl | unknown | 2 | 1933.878787878788 | 673.0 |
| test/02_integration/lib/query_intensive_spec.spl | unknown | 2 | 1758.225806451613 | 480.0 |
| test/02_integration/lib/protocol_intensive_spec.spl | unknown | 2 | 611.6071428571429 | 503.5 |
| test/02_integration/lib/database_atomic_spec.spl | unknown | 2 | 661.0384615384615 | 632.0 |
| test/02_integration/lib/game_net/udp_transport_spec.spl | unknown | 3 | 1255.375 | 508.0 |
| test/02_integration/lib/database_core_spec.spl | unknown | 2 | 806.95 | 686.5 |
| test/02_integration/lib/simd_stdlib_spec.spl | unknown | 2 | 1158.642857142857 | 483.0 |
| test/02_integration/lib/gpu/gpu_kernel_emission_spec.spl | unknown | 2 | 1686.4615384615386 | 466.0 |
| test/02_integration/lib/gpu/gpu_scheduler_diag_spec.spl | unknown | 3 | 682.0769230769231 | 663.0 |
| test/02_integration/lib/gpu/gpu_offload_payload_gating_spec.spl | unknown | 3 | 2055.923076923077 | 792.0 |
| test/02_integration/lib/gpu/host_gpu_queue_roundtrip_spec.spl | unknown | 2 | 585.75 | 594.0 |
| test/02_integration/lib/gpu/cpu_sw_primitive_readback_spec.spl | unknown | 2 | 1168.375 | 591.5 |
| test/01_unit/lib/http/ws/ws_writer_opcode_emission_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/lib/http/ws/ws_frame_round_trip_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/lib/http/ws/ws_negative_offset_guard_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/01_unit/lib/http/ws/ws_opcode_dispatch_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/01_unit/lib/http/multipart_header_separator_spec.spl | unknown | 2 | 1687.26 | 623.0 |
| test/01_unit/lib/http/request_empty_guard_spec.spl | unknown | 2 | 1936.2727272727273 | 578.5 |
| test/01_unit/lib/http/response_plain_text_helper_dedup_spec.spl | unknown | 2 | 2293.048780487805 | 605.0 |
| test/01_unit/lib/http/response_empty_guard_spec.spl | unknown | 2 | 2733.9756097560976 | 566.0 |
| test/01_unit/lib/http/h2/h2_preface_probe_spec.spl | unknown | 2 | 5776.694444444444 | 551.0 |
| test/01_unit/lib/http/h2/h2_frame_round_trip_spec.spl | unknown | 2 | 1679.9705882352941 | 524.0 |
| test/01_unit/lib/http/h2/h2_server_text_to_u8_spec.spl | unknown | 2 | 1098.3636363636363 | 591.0 |
| test/01_unit/lib/http/h2/h2_negative_offset_guard_spec.spl | unknown | 2 | 1933.878787878788 | 673.0 |
| test/01_unit/lib/http/h2/hpack_round_trip_spec.spl | unknown | 2 | 1758.225806451613 | 480.0 |
| test/01_unit/lib/http/h3/h3_negative_offset_guard_spec.spl | unknown | 2 | 611.6071428571429 | 503.5 |
| test/01_unit/lib/http/h3/h3_frame_round_trip_spec.spl | unknown | 2 | 661.0384615384615 | 632.0 |
| test/01_unit/lib/http/chunked_size_overflow_sync_spec.spl | unknown | 3 | 1255.375 | 508.0 |
| test/01_unit/compiler/mir_opt/auto_vectorize_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/compiler/mir_opt/bounds_check_elim_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/compiler/mir_opt/cipher/cipher_intrinsics_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/01_unit/compiler/mir_opt/cipher/cipher_parity_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/01_unit/compiler/mir_opt/cipher/cipher_rewrite_integration_spec.spl | unknown | 2 | 1687.26 | 623.0 |
| test/01_unit/compiler/mir_opt/cipher/opt_remark_spec.spl | unknown | 2 | 1936.2727272727273 | 578.5 |
| test/01_unit/compiler/mir_opt/cipher/pattern_dispatch_spec.spl | unknown | 2 | 2293.048780487805 | 605.0 |
| test/01_unit/compiler/mir_opt/cipher/pattern_engine_spec.spl | unknown | 2 | 2733.9756097560976 | 566.0 |
| test/01_unit/compiler/mir_opt/cipher/target_opt_context_spec.spl | unknown | 2 | 5776.694444444444 | 551.0 |
| test/01_unit/compiler/mir_opt/clib_parity_hotspot_spec.spl | unknown | 2 | 1679.9705882352941 | 524.0 |
| test/01_unit/compiler/mir_opt/collection_opt_spec.spl | unknown | 2 | 1098.3636363636363 | 591.0 |
| test/01_unit/compiler/mir_opt/constant_folding_spec.spl | unknown | 2 | 1933.878787878788 | 673.0 |
| test/01_unit/compiler/mir_opt/copy_propagation_spec.spl | unknown | 2 | 1758.225806451613 | 480.0 |
| test/01_unit/compiler/mir_opt/dead_code_spec.spl | unknown | 2 | 611.6071428571429 | 503.5 |
| test/01_unit/compiler/mir_opt/fs_optimization_spec.spl | unknown | 2 | 661.0384615384615 | 632.0 |
| test/01_unit/compiler/mir_opt/general_patterns_backend_recommendation_spec.spl | unknown | 3 | 1255.375 | 508.0 |
| test/01_unit/compiler/mir_opt/inlining_spec.spl | unknown | 2 | 806.95 | 686.5 |
| test/01_unit/compiler/mir_opt/loop_invariant_motion_spec.spl | unknown | 2 | 1158.642857142857 | 483.0 |
| test/01_unit/compiler/mir_opt/optimization_pipeline_aggregate_transport_source_spec.spl | unknown | 2 | 1686.4615384615386 | 466.0 |
| test/01_unit/compiler/mir_opt/optimizer_manifest_backend_policy_spec.spl | unknown | 3 | 682.0769230769231 | 663.0 |
| test/01_unit/compiler/mir_opt/pass_descriptor_spec.spl | unknown | 3 | 2055.923076923077 | 792.0 |
| test/01_unit/compiler/mir_opt/pattern_rule_spec.spl | unknown | 2 | 585.75 | 594.0 |
| test/01_unit/compiler/mir_opt/predicate_promote_spec.spl | unknown | 2 | 1168.375 | 591.5 |
| test/01_unit/compiler/mir_opt/runtime_array_assignment_ssa_spec.spl | unknown | 2 | 3543.285714285714 | 713.0 |
| test/01_unit/compiler/mir_opt/storage_layout_access_advisory_spec.spl | unknown | 2 | 1645.5714285714287 | 809.0 |
| test/01_unit/compiler/mir_opt/storage_simd_admission_spec.spl | unknown | 2 | 1030.5714285714287 | 583.0 |
| test/01_unit/compiler/mir_opt/storage_simd_codegen_spec.spl | unknown | 2 | 1145.0 | 594.0 |
| test/01_unit/compiler/mir_opt/storage_simd_schedule_spec.spl | unknown | 2 | 4028.285714285714 | 505.0 |
| test/01_unit/compiler/mir_opt/strength_reduction_spec.spl | unknown | 2 | 20489.5 | 551.0 |
| test/01_unit/compiler/mir_opt/target_family_package_surface_spec.spl | unknown | 2 | 885.2 | 616.0 |
| test/01_unit/compiler/mir_opt/typed_byte_canon_spec.spl | unknown | 2 | 676.0 | 622.0 |
| test/01_unit/compiler/mir_opt/typed_storage_view_declaration_spec.spl | unknown | 2 | 519.8 | 540.0 |
| test/01_unit/compiler/mir_opt/typed_storage_view_producer_spec.spl | unknown | 2 | 3088.4 | 827.0 |
| test/01_unit/compiler/mir_opt/var_reassign_analysis_spec.spl | unknown | 2 | 1033.2 | 628.0 |
| test/01_unit/compiler/module_resolver/allowed_families_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/compiler/module_resolver/type_domain_resolver_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/compiler/module_resolver/numbered_dir_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/01_unit/compiler/module_resolver/tier_ambiguity_warning_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/01_unit/compiler/module_resolver/var_resolution_spec.spl | unknown | 2 | 1687.26 | 623.0 |
| test/01_unit/compiler/mono/monomorphize/deferred_deserialize_byte_text_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/compiler/mono/generic_template_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/compiler/mono/mold_pure_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/01_unit/compiler/mono/mono_cache_efficiency_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/01_unit/compiler/mono/monomorphization_native_build_regression_spec.spl | unknown | 2 | 1687.26 | 623.0 |
| test/01_unit/compiler/mono/monomorphize_spec.spl | unknown | 2 | 1936.2727272727273 | 578.5 |
| test/01_unit/compiler/mono/note_sdn_bdd_spec.spl | unknown | 2 | 2293.048780487805 | 605.0 |
| test/01_unit/compiler/mono/note_sdn_spec.spl | unknown | 2 | 2733.9756097560976 | 566.0 |
| test/01_unit/compiler/mono/monomorphize_integration_spec.spl | unknown | 2 | 5776.694444444444 | 551.0 |
| test/01_unit/lib/i18n/resource_bundle_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/compiler/native/arm_neon_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/compiler/native/asm_match_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/compiler/native/auto_vectorize_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/01_unit/compiler/native/baremetal_syntax_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/01_unit/compiler/native/bitfield_codegen_spec.spl | unknown | 2 | 1687.26 | 623.0 |
| test/01_unit/compiler/native/build_native_min_spec.spl | unknown | 2 | 1936.2727272727273 | 578.5 |
| test/01_unit/compiler/native/callconv_bridge_spec.spl | unknown | 2 | 2293.048780487805 | 605.0 |
| test/01_unit/compiler/native/cli_interpreter_path_spec.spl | unknown | 2 | 2733.9756097560976 | 566.0 |
| test/01_unit/compiler/native/dict_get_struct_value_spec.spl | unknown | 2 | 5776.694444444444 | 551.0 |
| test/01_unit/compiler/native/inline_asm_constraints_spec.spl | unknown | 2 | 1679.9705882352941 | 524.0 |
| test/01_unit/compiler/native/inline_asm_core_parser_spec.spl | unknown | 2 | 1098.3636363636363 | 591.0 |
| test/01_unit/compiler/native/inline_asm_matrix_spec.spl | unknown | 2 | 1933.878787878788 | 673.0 |
| test/01_unit/compiler/native/inline_asm_spec.spl | unknown | 2 | 1758.225806451613 | 480.0 |
| test/01_unit/compiler/native/native_compile_spec.spl | unknown | 2 | 611.6071428571429 | 503.5 |
| test/01_unit/compiler/native/simd_capabilities_spec.spl | unknown | 2 | 661.0384615384615 | 632.0 |
| test/01_unit/compiler/native/simd_check_spec.spl | unknown | 3 | 1255.375 | 508.0 |
| test/01_unit/compiler/native/struct_dict_field_map_copy_spec.spl | unknown | 2 | 806.95 | 686.5 |
| test/01_unit/compiler/native/x86_64_simd_spec.spl | unknown | 2 | 1158.642857142857 | 483.0 |
| test/01_unit/compiler/native/x86_simd_register_contract_spec.spl | unknown | 2 | 1686.4615384615386 | 466.0 |
| test/01_unit/lib/immut/persistent_trie_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/lib/immut/atom_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/lib/immut/persistent_builder_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/01_unit/lib/immut/persistent_map_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/01_unit/lib/immut/ref_spec.spl | unknown | 2 | 1687.26 | 623.0 |
| test/01_unit/lib/immut/actor_snapshot_spec.spl | unknown | 2 | 1936.2727272727273 | 578.5 |
| test/01_unit/lib/immut/persistent_list_spec.spl | unknown | 2 | 2293.048780487805 | 605.0 |
| test/01_unit/lib/immut/persistent_vec_spec.spl | unknown | 2 | 2733.9756097560976 | 566.0 |
| test/01_unit/lib/immut/versioned_snapshot_spec.spl | unknown | 2 | 5776.694444444444 | 551.0 |
| test/01_unit/lib/immut/persistent_set_spec.spl | unknown | 2 | 1679.9705882352941 | 524.0 |
| test/01_unit/lib/immut/persistent_sorted_map_spec.spl | unknown | 2 | 1098.3636363636363 | 591.0 |
| test/01_unit/lib/immut/integration_spec.spl | unknown | 2 | 1933.878787878788 | 673.0 |
| test/01_unit/lib/immut/combinators_spec.spl | unknown | 2 | 1758.225806451613 | 480.0 |
| test/01_unit/lib/immut/debug_map_spec.spl | unknown | 2 | 611.6071428571429 | 503.5 |
| test/01_unit/compiler/regression/entry_closure_defect_semantics_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/compiler/regression/short_circuit_semantics_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/compiler/regression/struct_init_omitted_field_nil_fill_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/01_unit/compiler/regression/try_operator_preservation_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/01_unit/lib/jit/jit_types_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/lib/jit/jit_unified_runner_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/compiler/resource/resource_borrow_pinning_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/compiler/resource/resource_decl_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/compiler/resource/resource_drop_exactly_once_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/01_unit/compiler/resource/resource_family_inference_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/01_unit/compiler/resource/resource_hir_metadata_spec.spl | unknown | 2 | 1687.26 | 623.0 |
| test/01_unit/compiler/resource/resource_interp_drop_spec.spl | unknown | 2 | 1936.2727272727273 | 578.5 |
| test/01_unit/compiler/resource/resource_mir_drop_spec.spl | unknown | 2 | 2293.048780487805 | 605.0 |
| test/01_unit/compiler/resource/resource_ownership_sigil_spec.spl | unknown | 2 | 2733.9756097560976 | 566.0 |
| test/01_unit/compiler/resource/resource_sffi_pilot_spec.spl | unknown | 2 | 5776.694444444444 | 551.0 |
| test/01_unit/compiler/resource/resource_shared_mut_method_spec.spl | unknown | 2 | 1679.9705882352941 | 524.0 |
| test/01_unit/compiler/resource/resource_use_after_move_spec.spl | unknown | 2 | 1098.3636363636363 | 591.0 |
| test/01_unit/compiler/resource/resource_with_scoped_mir_drop_spec.spl | unknown | 2 | 1933.878787878788 | 673.0 |
| test/01_unit/compiler/resource/resource_with_scoped_spec.spl | unknown | 2 | 1758.225806451613 | 480.0 |
| test/01_unit/compiler/resource/resource_wrapper_gen_spec.spl | unknown | 2 | 611.6071428571429 | 503.5 |
| test/01_unit/compiler/semantic/self_field_method_resolution_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/compiler/semantic/typed_empty_array_constructor_general_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/compiler/semantic/typed_empty_array_constructor_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/01_unit/lib/js/js_native_confinement_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/lib/js/json_unicode_escape_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/lib/js/typeof_builtin_introspection_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/01_unit/lib/nogc_async_mut_noalloc/async/poll_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/lib/nogc_async_mut_noalloc/async/response_time_report_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/lib/nogc_async_mut_noalloc/async/scheduler_ravenscar_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/01_unit/lib/nogc_async_mut_noalloc/async/scheduler_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/01_unit/lib/nogc_async_mut_noalloc/async/timing_model_spec.spl | unknown | 2 | 1687.26 | 623.0 |
| test/01_unit/lib/nogc_async_mut_noalloc/async/wcet_adapter_spec.spl | unknown | 2 | 1936.2727272727273 | 578.5 |
| test/01_unit/lib/nogc_async_mut_noalloc/collections/fixed_array_spec.spl | unknown | 2 | 2293.048780487805 | 605.0 |
| test/01_unit/lib/nogc_async_mut_noalloc/collections/fixed_array_stack_backing_storage_regression_spec.spl | unknown | 2 | 2733.9756097560976 | 566.0 |
| test/01_unit/lib/nogc_async_mut_noalloc/collections/fixed_map_backing_storage_regression_spec.spl | unknown | 2 | 5776.694444444444 | 551.0 |
| test/01_unit/lib/nogc_async_mut_noalloc/collections/fixed_map_spec.spl | unknown | 2 | 1679.9705882352941 | 524.0 |
| test/01_unit/lib/nogc_async_mut_noalloc/collections/fixed_set_spec.spl | unknown | 2 | 1098.3636363636363 | 591.0 |
| test/01_unit/lib/nogc_async_mut_noalloc/collections/fixed_stack_spec.spl | unknown | 2 | 1933.878787878788 | 673.0 |
| test/01_unit/lib/nogc_async_mut_noalloc/collections/linked_list_backing_storage_regression_spec.spl | unknown | 2 | 1758.225806451613 | 480.0 |
| test/01_unit/lib/nogc_async_mut_noalloc/collections/linked_list_spec.spl | unknown | 2 | 611.6071428571429 | 503.5 |
| test/01_unit/lib/nogc_async_mut_noalloc/collections/ring_buffer_spec.spl | unknown | 2 | 661.0384615384615 | 632.0 |
| test/01_unit/lib/nogc_async_mut_noalloc/execution/semihost_capture_sleep_ms_spec.spl | unknown | 3 | 1255.375 | 508.0 |
| test/01_unit/lib/nogc_async_mut_noalloc/execution/watchdog_manager_spec.spl | unknown | 2 | 806.95 | 686.5 |
| test/01_unit/lib/nogc_async_mut_noalloc/memory/refc_binary_spec.spl | unknown | 2 | 1158.642857142857 | 483.0 |
| test/01_unit/lib/nogc_async_mut_noalloc/path/baremetal_path_spec.spl | unknown | 2 | 1686.4615384615386 | 466.0 |
| test/01_unit/lib/nogc_async_mut_noalloc/qemu_spec.spl | unknown | 3 | 682.0769230769231 | 663.0 |
| test/01_unit/lib/nogc_async_mut_noalloc/tls/tls_smoke_spec.spl | unknown | 3 | 2055.923076923077 | 792.0 |
| test/01_unit/compiler/type_infer/type_infer_correctness_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/compiler/hir/host_gpu_lane_hir_lowering_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| failed | unknown | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/compiler/hir/alias_static_call_resolution_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/01_unit/compiler/hir/tuple_match_enum_subpattern_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| passed | unknown | 2 | 1687.26 | 623.0 |
| test/01_unit/compiler/hir/nil_dict_receiver_phantom_option_spec.spl | unknown | 2 | 1936.2727272727273 | 578.5 |
| test/01_unit/compiler/hir/method_self_context_save_restore_spec.spl | unknown | 2 | 2293.048780487805 | 605.0 |
| test/01_unit/compiler/hir/hir_lazy_import_registration_flag_regression_spec.spl | unknown | 2 | 2733.9756097560976 | 566.0 |
| test/01_unit/compiler/hir/enum_payload_range_or_frontend_exec_spec.spl | unknown | 2 | 5776.694444444444 | 551.0 |
| test/01_unit/compiler/hir/module_surface_spec.spl | unknown | 2 | 1679.9705882352941 | 524.0 |
| test/01_unit/compiler/hir/hir_async_spec.spl | unknown | 2 | 1098.3636363636363 | 591.0 |
| test/01_unit/compiler/hir/hir_glob_reachable_miss_memo_spec.spl | unknown | 2 | 1933.878787878788 | 673.0 |
| test/01_unit/compiler/hir/stage4_hir_value_name_dispatch_spec.spl | unknown | 2 | 1758.225806451613 | 480.0 |
| test/01_unit/compiler/hir/legacy_builtin_alias_source_spec.spl | unknown | 2 | 611.6071428571429 | 503.5 |
| test/01_unit/compiler/hir/resolve_import_module_value_spec.spl | unknown | 2 | 661.0384615384615 | 632.0 |
| test/01_unit/compiler/hir/imported_composite_field_package_sibling_spec.spl | unknown | 3 | 1255.375 | 508.0 |
| test/01_unit/compiler/hir/vulkan_gpu_attr_hir_spec.spl | unknown | 2 | 806.95 | 686.5 |
| test/01_unit/compiler/hir/exhaustiveness/critical_wildcard_coverage_spec.spl | unknown | 2 | 1158.642857142857 | 483.0 |
| test/01_unit/compiler/hir/imported_tuple_signature_dependency_spec.spl | unknown | 2 | 1686.4615384615386 | 466.0 |
| test/01_unit/compiler/hir/hir_forward_lowering_spec.spl | unknown | 3 | 682.0769230769231 | 663.0 |
| test/01_unit/compiler/hir/package_export_route_shapes_spec.spl | unknown | 3 | 2055.923076923077 | 792.0 |
| test/01_unit/compiler/hir/bootstrap_hir_store_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/compiler/hir/symbol_display_name_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/compiler/hir/hir_lowering_begin_module_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/01_unit/compiler/hir/qualified_import_call_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/01_unit/compiler/hir/payload_binding_contest_names_agree_source_spec.spl | unknown | 2 | 1687.26 | 623.0 |
| test/01_unit/compiler/hir/hir_module_spec.spl | unknown | 2 | 1936.2727272727273 | 578.5 |
| test/01_unit/compiler/hir/hir_async_errors_spec.spl | unknown | 2 | 2293.048780487805 | 605.0 |
| test/01_unit/compiler/hir/unannotated_module_const_type_spec.spl | unknown | 2 | 2733.9756097560976 | 566.0 |
| test/01_unit/compiler/hir/symbol_table_module_reset_spec.spl | unknown | 2 | 5776.694444444444 | 551.0 |
| test/01_unit/compiler/hir/hir_module_callable_index_spec.spl | unknown | 2 | 1679.9705882352941 | 524.0 |
| test/01_unit/compiler/hir/hir_eval_spec.spl | unknown | 2 | 1098.3636363636363 | 591.0 |
| test/01_unit/compiler/hir/field_index_erased_receiver_spec.spl | unknown | 2 | 1933.878787878788 | 673.0 |
| test/01_unit/compiler/hir/me_field_resolution_spec.spl | unknown | 2 | 1758.225806451613 | 480.0 |
| test/01_unit/compiler/hir/hir_lower_spec.spl | unknown | 2 | 611.6071428571429 | 503.5 |
| test/01_unit/compiler/hir/hir_codec_roundtrip_spec.spl | unknown | 2 | 661.0384615384615 | 632.0 |
| test/01_unit/compiler/hir/self_context_pair_consistency_spec.spl | unknown | 3 | 1255.375 | 508.0 |
| test/01_unit/compiler/hir/hir_forward_decl_spec.spl | unknown | 2 | 806.95 | 686.5 |
| test/01_unit/compiler/hir/seed_parity_scalar_type_names_spec.spl | unknown | 2 | 1158.642857142857 | 483.0 |
| test/01_unit/compiler/hir/tuple_match_enum_subpattern_spec.spl | unknown | 5 | 5168.011111111111 | 770.5 |
| test/01_unit/compiler/hir/nil_dict_receiver_phantom_option_spec.spl | unknown | 2 | 2443.283582089552 | 650.0 |
| test/01_unit/compiler/hir/method_self_context_save_restore_spec.spl | unknown | 3 | 2563.246153846154 | 668.0 |
| test/01_unit/compiler/hir/hir_lazy_import_registration_flag_regression_spec.spl | unknown | 3 | 2818.396551724138 | 545.0 |
| test/01_unit/compiler/hir/enum_payload_range_or_frontend_exec_spec.spl | unknown | 2 | 1687.26 | 623.0 |
| test/01_unit/compiler/hir/module_surface_spec.spl | unknown | 2 | 1936.2727272727273 | 578.5 |
| test/01_unit/compiler/hir/hir_async_spec.spl | unknown | 2 | 2293.048780487805 | 605.0 |
| test/01_unit/compiler/hir/hir_glob_reachable_miss_memo_spec.spl | unknown | 2 | 2733.9756097560976 | 566.0 |
| test/01_unit/compiler/hir/stage4_hir_value_name_dispatch_spec.spl | unknown | 2 | 5776.694444444444 | 551.0 |
| test/01_unit/compiler/hir/legacy_builtin_alias_source_spec.spl | unknown | 2 | 1679.9705882352941 | 524.0 |
| test/01_unit/compiler/hir/resolve_import_module_value_spec.spl | unknown | 2 | 1098.3636363636363 | 591.0 |
| test/01_unit/compiler/hir/vulkan_gpu_attr_hir_spec.spl | unknown | 2 | 1933.878787878788 | 673.0 |
| test/01_unit/compiler/hir/exhaustiveness/critical_wildcard_coverage_spec.spl | unknown | 2 | 1758.225806451613 | 480.0 |
| test/01_unit/compiler/hir/imported_tuple_signature_dependency_spec.spl | unknown | 2 | 611.6071428571429 | 503.5 |
| test/01_unit/compiler/hir/bootstrap_hir_store_spec.spl | unknown | 2 | 661.0384615384615 | 632.0 |
| test/01_unit/compiler/hir/symbol_display_name_spec.spl | unknown | 3 | 1255.375 | 508.0 |
| test/01_unit/compiler/hir/hir_lowering_begin_module_spec.spl | unknown | 2 | 806.95 | 686.5 |
| test/01_unit/compiler/hir/payload_binding_contest_names_agree_source_spec.spl | unknown | 2 | 1158.642857142857 | 483.0 |
| test/01_unit/compiler/hir/hir_module_spec.spl | unknown | 2 | 1686.4615384615386 | 466.0 |
| test/01_unit/compiler/hir/hir_async_errors_spec.spl | unknown | 3 | 682.0769230769231 | 663.0 |
| test/01_unit/compiler/hir/unannotated_module_const_type_spec.spl | unknown | 3 | 2055.923076923077 | 792.0 |
| test/01_unit/compiler/hir/symbol_table_module_reset_spec.spl | unknown | 2 | 585.75 | 594.0 |
| test/01_unit/compiler/hir/hir_module_callable_index_spec.spl | unknown | 2 | 1168.375 | 591.5 |
| test/01_unit/compiler/hir/hir_eval_spec.spl | unknown | 2 | 3543.285714285714 | 713.0 |
| test/01_unit/compiler/hir/field_index_erased_receiver_spec.spl | unknown | 2 | 1645.5714285714287 | 809.0 |
| test/01_unit/compiler/hir/me_field_resolution_spec.spl | unknown | 2 | 1030.5714285714287 | 583.0 |
| test/01_unit/compiler/hir/hir_lower_spec.spl | unknown | 2 | 1145.0 | 594.0 |
| test/01_unit/compiler/hir/hir_codec_roundtrip_spec.spl | unknown | 2 | 4028.285714285714 | 505.0 |
| test/01_unit/compiler/hir/self_context_pair_consistency_spec.spl | unknown | 2 | 20489.5 | 551.0 |
| test/01_unit/compiler/hir/hir_forward_decl_spec.spl | unknown | 2 | 885.2 | 616.0 |
| test/01_unit/compiler/hir/seed_parity_scalar_type_names_spec.spl | unknown | 2 | 676.0 | 622.0 |
| test/01_unit/compiler/hir/module_surface_index_allocation_guard_spec.spl | unknown | 2 | 519.8 | 540.0 |
| test/01_unit/compiler/hir/hir_verification_contract_preservation_spec.spl | unknown | 2 | 3088.4 | 827.0 |
| test/01_unit/compiler/hir/rv32_decode_helper_hir_lowering_spec.spl | unknown | 2 | 1033.2 | 628.0 |
| test/01_unit/compiler/hir/bootstrap_expr_args_source_spec.spl | unknown | 2 | 746.5 | 627.0 |
| test/01_unit/compiler/hir/qualified_type_lookup_scaling_spec.spl | unknown | 2 | 737.25 | 753.5 |
| test/01_unit/compiler/hir/hir_import_registration_per_symbol_cost_spec.spl | unknown | 2 | 1296.0 | 645.5 |
| test/01_unit/compiler/hir/hir_symbol_table_all_functions_spec.spl | unknown | 2 | 708.25 | 673.0 |
| test/01_unit/compiler/hir/impl_self_symbol_id_scope_spec.spl | unknown | 2 | 768.0 | 768.0 |
| test/01_unit/compiler/hir/symbol_table_scope_bracket_read_class_spec.spl | unknown | 2 | 673.0 | 625.0 |
| test/01_unit/compiler/hir/imported_surface_callable_projection_spec.spl | unknown | 2 | 740.25 | 610.0 |
| test/01_unit/compiler/hir/generic_impl_head_params_gate_spec.spl | unknown | 2 | 816.5 | 838.0 |
| test/01_unit/compiler/hir/implicit_self_field_hir_probe_spec.spl | unknown | 2 | 2468.0 | 783.0 |
| test/01_unit/compiler/hir/hir_types_spec.spl | unknown | 2 | 679.3333333333334 | 457.0 |
| test/01_unit/compiler/hir/enum_attributes_spec.spl | unknown | 2 | 548.0 | 535.0 |
| test/01_unit/compiler/hir/enum_lowering_end_to_end_spec.spl | unknown | 2 | 737.3333333333334 | 658.0 |
| test/01_unit/compiler/hir/hir_new_spec.spl | unknown | 2 | 512.0 | 548.0 |
| test/01_unit/compiler/hir/if_val_expression_binding_spec.spl | unknown | 2 | 555.3333333333334 | 624.0 |
| test/01_unit/compiler/hir/module_surface_projected_type_shape_spec.spl | unknown | 2 | 525.6666666666666 | 524.0 |
| test/01_unit/compiler/hir/module_surface_glob_export_origin_spec.spl | unknown | 2 | 15202.333333333334 | 1012.0 |
| test/01_unit/compiler/hir/float_primitive_cast_spec.spl | unknown | 2 | 572.5 | 572.5 |
| test/01_unit/compiler/hir/standalone_lowering_real_compiler_files_spec.spl | unknown | 2 | 433.0 | 433.0 |
| test/01_unit/compiler/hir/module_namespace_retained_surface_spec.spl | unknown | 2 | 993.0 | 993.0 |
| test/01_unit/compiler/hir/hir_function_span_populate_spec.spl | unknown | 2 | 418.0 | 418.0 |
| test/01_unit/compiler/hir/bootstrap_block_value_has_source_spec.spl | unknown | 2 | 364.0 | 364.0 |
| test/01_unit/compiler/hir/parser_contract_type_owner_spec.spl | unknown | 2 | 441.0 | 441.0 |
| test/01_unit/compiler/hir/hir_import_registration_cost_spec.spl | unknown | 2 | 420.0 | 420.0 |
| test/01_unit/compiler/hir/fixed_width_array_type_spec.spl | unknown | 2 | 436.0 | 436.0 |
| test/01_unit/compiler/hir/statement_payload_types_source_spec.spl | unknown | 2 | 440.0 | 440.0 |
| test/01_unit/compiler/hir/enum_shortname_collision_two_owners_spec.spl | unknown | 2 | 435.0 | 435.0 |
| test/01_unit/compiler/hir/symbol_table_cross_file_impl_spec.spl | unknown | 2 | 446.0 | 446.0 |
| test/01_unit/compiler/hir/symbol_table_dict_get_source_spec.spl | unknown | 2 | 361.0 | 361.0 |
| test/01_unit/compiler/hir/enum_payload_nested_range_or_lowering_spec.spl | unknown | 2 | 366.0 | 366.0 |
| test/01_unit/compiler/hir/hir_inference_type_to_text_array_spec.spl | unknown | 2 | 447.0 | 447.0 |
| test/01_unit/compiler/hir/symbol_table_lookup_scope_guard_spec.spl | unknown | 2 | 609.0 | 609.0 |
| test/01_unit/compiler/hir/class_method_bodies_reachable_spec.spl | unknown | 2 | 2754.0 | 2754.0 |
| test/01_unit/compiler/hir/module_surface_owner_index_spec.spl | unknown | 2 | 932.0 | 932.0 |
| test/01_unit/compiler/hir/hir_stage4_field_inference_spec.spl | unknown | 2 | 637.0 | 637.0 |
| test/01_unit/compiler/hir/hir_block_tail_invariants_source_spec.spl | unknown | 2 | 593.0 | 593.0 |
| test/01_unit/compiler/hir/untyped_param_declared_callable_type_spec.spl | unknown | 2 | 868.0 | 868.0 |
| test/01_unit/compiler/hir/symbol_table_qualified_indexes_spec.spl | unknown | 2 | 713.0 | 713.0 |
| test/01_unit/compiler/hir/enum_payload_origin_plain_use_spec.spl | unknown | 2 | 399.0 | 399.0 |
| test/01_unit/compiler/hir/untyped_return_nil_safe_spec.spl | unknown | 2 | 717.0 | 717.0 |
| test/01_unit/compiler/hir/match_arm_underscore_subpattern_spec.spl | unknown | 2 | 601.0 | 601.0 |
| test/01_unit/compiler/hir/domain_block_hir_lowering_spec.spl | passed | 1 | 0.0 | 0.0 |
| test/01_unit/compiler/hir/tuple_destructure_mutability_source_spec.spl | passed | 1 | 0.0 | 0.0 |
| test/01_unit/compiler/hir/imported_callable_materialization_cardinality_spec.spl | failed | 1 | 0.0 | 0.0 |
| test/01_unit/compiler/hir/seed_parity_container_and_self_types_spec.spl | failed | 1 | 0.0 | 0.0 |
| test/01_unit/compiler/hir/void_return_type_spec.spl | passed | 1 | 0.0 | 0.0 |
| test/01_unit/compiler/hir/untyped_return_value_shapes_spec.spl | passed | 1 | 0.0 | 0.0 |
| test/01_unit/compiler/hir/module_surface_index_alignment_spec.spl | passed | 1 | 0.0 | 0.0 |
| test/01_unit/compiler/hir/resolve_import_symbols_spec.spl | failed | 1 | 0.0 | 0.0 |
| test/01_unit/compiler/hir/impl_lowering_self_symbol_id_spec.spl | failed | 1 | 0.0 | 0.0 |
| test/01_unit/compiler/hir/eprint_builtin_native_path_spec.spl | passed | 1 | 0.0 | 0.0 |
| test/01_unit/compiler/hir/hir_bootstrap_source_regression_spec.spl | failed | 1 | 0.0 | 0.0 |
| test/01_unit/compiler/hir/hir_types_equal_int_width_spec.spl | passed | 1 | 0.0 | 0.0 |
| test/01_unit/compiler/hir/symbol_table_id_zero_spec.spl | passed | 1 | 0.0 | 0.0 |
| test/01_unit/compiler/hir/tuple_match_enum_subpattern_runtime_spec.spl | passed | 1 | 0.0 | 0.0 |
| test/01_unit/compiler/hir/hir_item_nested_value_ownership_spec.spl | passed | 1 | 0.0 | 0.0 |
| test/01_unit/compiler/hir/hir_type_structural_equality_spec.spl | passed | 1 | 0.0 | 0.0 |
| test/01_unit/compiler/hir/hir_lowering_items_surface_completeness_spec.spl | passed | 1 | 0.0 | 0.0 |
| test/01_unit/compiler/hir/hir_codec_writer_chunked_cost_spec.spl | passed | 1 | 0.0 | 0.0 |
| test/01_unit/compiler/hir/module_lowering_dict_keys_source_spec.spl | failed | 1 | 0.0 | 0.0 |
| test/01_unit/compiler/hir/generic_template_marking_spec.spl | passed | 1 | 0.0 | 0.0 |
| test/01_unit/compiler/hir/same_named_package_facade_reexport_spec.spl | failed | 1 | 0.0 | 0.0 |
| test/01_unit/compiler/hir/hir_stmt_dispatch_source_spec.spl | failed | 1 | 0.0 | 0.0 |
| test/01_unit/compiler/hir/llvm_backend_compile_module_typed_return_spec.spl | passed | 1 | 0.0 | 0.0 |
| test/01_unit/compiler/hir/field_index_guess_class_spec.spl | failed | 1 | 0.0 | 0.0 |
| test/01_unit/compiler/hir/symbol_table_all_functions_spec.spl | passed | 1 | 0.0 | 0.0 |
| test/01_unit/compiler/hir/hir_async_integration_spec.spl | passed | 1 | 0.0 | 0.0 |
| test/01_unit/compiler/hir/reexport_physical_cache_spec.spl | failed | 1 | 0.0 | 0.0 |
| test/01_unit/compiler/hir/hir_lowering_spec.spl | passed | 1 | 0.0 | 0.0 |
| test/01_unit/compiler/hir/hir_package_dependency_scan_memo_spec.spl | passed | 1 | 0.0 | 0.0 |
| test/01_unit/compiler/hir/module_filename_populated_spec.spl | passed | 1 | 0.0 | 0.0 |
| test/01_unit/compiler/hir/pattern_condition_mutability_source_spec.spl | passed | 1 | 0.0 | 0.0 |

**Error:**
```
Test 'iffs identical V4 buffers as exact' failed
Location: /home/ormastes/dev/pub/simple/test/sys/wm_compare/v1_v4_parity_spec.spl
```

| Test | p50 (ms) | Mean (ms) | Runs |
|------|----------|-----------|------|
| test/01_unit/compiler/bootstrap/entry_closure_physical_source_dedup_spec.spl | 1012.0 | 15202.333333333334 | 2 |
| test/01_unit/lib/extended/execution_fiber_unit_spec.spl | 1012.0 | 15202.333333333334 | 2 |
| test/01_unit/lib/extended/qemu_device_integration_spec.spl | 2754.0 | 2754.0 | 2 |
| test/02_integration/core/core_integration_8_spec.spl | 1012.0 | 15202.333333333334 | 2 |
| test/01_unit/compiler/hir/module_surface_glob_export_origin_spec.spl | 1012.0 | 15202.333333333334 | 2 |
| test/01_unit/compiler/hir/class_method_bodies_reachable_spec.spl | 2754.0 | 2754.0 | 2 |

## Failed Tests

- test/01_unit/compiler/async/async_frame_analysis_spec.spl
- test/01_unit/compiler/async/async_integration_spec.spl
- test/01_unit/compiler/async/async_mir_interpreter_spec.spl
- test/01_unit/compiler/async/async_mir_spec.spl
- test/01_unit/compiler/async/async_state_machine_spec.spl
- test/01_unit/compiler/async/poll_generator_spec.spl
- test/01_unit/compiler/async/state_enum_spec.spl
- test/01_unit/compiler/async/suspension_analysis_spec.spl
- test/01_unit/compiler/verification/unified_attrs_spec.spl
- test/feature/lib/std/compiler/lexer_ffi_test.spl
- test/feature/lib/minimal_spec.spl
- test/01_unit/lib/blink/style/user_agent_stylesheet_spec.spl
- test/01_unit/lib/blink/inline_text_spec.spl
- test/01_unit/lib/blink/style_shorthand_spec.spl
- test/01_unit/lib/blink/html_tokenizer_spec.spl
- test/01_unit/lib/blink/paint_chunk_spec.spl
- test/01_unit/lib/blink/css_selector_spec.spl
- test/01_unit/lib/blink/paint/invalidation_spec.spl
- test/01_unit/lib/blink/paint/border_paint_spec.spl
- test/01_unit/lib/blink/values_length_spec.spl
- test/01_unit/lib/blink/style_at_rules_spec.spl
- test/01_unit/compiler/bootstrap/vhdl_entity_shared_binding_contract_spec.spl
- test/01_unit/compiler/bootstrap/entry_closure_physical_source_dedup_spec.spl
- test/01_unit/lib/extended/memory_pool_unit_spec.spl
- test/01_unit/lib/extended/qemu_user_integration_spec.spl
- test/01_unit/lib/extended/gpu_pipeline_integration_spec.spl
- test/01_unit/lib/extended/gpu_pipeline_unit_spec.spl
- test/01_unit/lib/extended/memory_arena_integration_spec.spl
- test/01_unit/lib/extended/qemu_user_unit_spec.spl
- test/01_unit/lib/extended/qemu_device_integration_spec.spl
- test/01_unit/lib/extended/cuda_event_unit_spec.spl
- test/01_unit/lib/extended/gpu_render_integration_spec.spl
- test/01_unit/compiler/hir/imported_callable_materialization_cardinality_spec.spl
- test/01_unit/compiler/hir/seed_parity_container_and_self_types_spec.spl
- test/01_unit/compiler/hir/resolve_import_symbols_spec.spl
- test/01_unit/compiler/hir/impl_lowering_self_symbol_id_spec.spl
- test/01_unit/compiler/hir/hir_bootstrap_source_regression_spec.spl
- test/01_unit/compiler/hir/module_lowering_dict_keys_source_spec.spl
- test/01_unit/compiler/hir/same_named_package_facade_reexport_spec.spl
- test/01_unit/compiler/hir/hir_stmt_dispatch_source_spec.spl
- test/01_unit/compiler/hir/field_index_guess_class_spec.spl
- test/01_unit/compiler/hir/reexport_physical_cache_spec.spl
