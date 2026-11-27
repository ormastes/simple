# Unwired `*_test.shs` census (2026-11-26)

Base: origin/release/1.0.0. Vendor paths excluded.

## Method
A test is WIRED when a file other than itself (and not under `doc/` or `*.md`)
references its path/basename and that file is a `.github/workflows/*`,
`config/check/must_check_gates.sdn`, a `*.shs` script, or a `*_spec.spl`.
Baseline/opt-out lists (`guard_wiring_optout.txt`, `*_baseline.txt`), `.c` files
and build logs do not count. `bin/simple test` does not discover `*_test.shs`
(no `.shs` suffix in the test_runner discovery) and no glob-based runner exists.

## Census (633 files)
| class | count | meaning |
|---|---|---|
| wired | 116 | referenced by a workflow, gate manifest, script or spec |
| unwired total | 517 | nothing runs them |
| (a) dead target, delete | 0 | no unwired test has all its script targets missing, see below |
| (b) live, candidate to wire | 288 | no env-heavy keywords; NOT yet run green |
| (c) needs special env | 229 | mention qemu/clang/cargo/bin/simple/docker/ssh/freebsd/riscv/llvm/native-build/etc. |

(a) detail: two tests have only-missing targets,
`test/01_unit/compiler/interp/interpreter_load_facade_contract_test.shs` and
`test/01_unit/scripts/compiler_interpreter_loader_layering_mutation_test.shs`.
They are the pending contract of a module that never landed
(`doc/08_tracking/bug/interpreter_load_facade_module_never_landed_2026-10-30.md`),
so they are kept, not deleted.

## Why (b) is not wired yet
Wiring without a green run would turn a required gate red. A sample run on
Windows git-bash of 5 unwired scripts gave rc 1, 124 (timeout), 1, 2, 124, with
a sparse checkout missing `src/`, so it is not conclusive. Plan: run the (b) list
on a Linux host with a full checkout, wire the passing ones into ONE existing
manifest (`config/check/must_check_gates.sdn`, advisory tier), and file bugs for
failures. Batches of at most 60 files per PR.

## (b) candidates
- examples/10_tooling/trace32_tools/relay_power/relay_power_cycle_test.shs
- scripts/check/bootstrap_compiler_headroom_boundary_test.shs
- test/00_unit/scripts/devhub_windows_launch_modes_test.shs
- test/00_unit/scripts/hir_worker_diagnostics_workaround_test.shs
- test/00_unit/scripts/kernel_plugin_phase8_source_contract_test.shs
- test/00_unit/scripts/stage4_runtime_abi_provenance_wiring_mutation_test.shs
- test/01_unit/app/arch_check_fast_help_contract_test.shs
- test/01_unit/app/compiler_entrypoint/demand_entry_path_contract_test.shs
- test/01_unit/app/stdio_runtime_owner_contract_test.shs
- test/01_unit/compiler/action_graph/artifact_service_bridge_ownership_contract_test.shs
- test/01_unit/compiler/action_graph/demand_compile_integration_contract_test.shs
- test/01_unit/compiler/action_graph/package_archive_admission_import_contract_test.shs
- test/01_unit/compiler/backend/backend_plugin_failure_diagnostics_source_contract_test.shs
- test/01_unit/compiler/backend/io_mmap_text_abi_runtime_link_contract_test.shs
- test/01_unit/compiler/backend_plugin/backend_plugin_v1_abi_contract_test.shs
- test/01_unit/compiler/backend_plugin/backend_plugin_v1_native_bridge_test.shs
- test/01_unit/compiler/cache/package_index_driver_cutover_contract_test.shs
- test/01_unit/compiler/driver/backend_plugin_cli_propagation_contract_test.shs
- test/01_unit/compiler/driver/entry_closure_app_doc_source_contract_test.shs
- test/01_unit/compiler/driver/memory_snapshot_sink_contract_test.shs
- test/01_unit/compiler/hir/conditional_empty_symbol_keys_native_test.shs
- test/01_unit/compiler/interp/interpreter_load_facade_contract_test.shs
- test/01_unit/compiler/interpreter/interpreter_load_facade_contract_test.shs
- test/01_unit/compiler/lint/raw_if_chain_lint_walkers_source_test.shs
- test/01_unit/compiler/loader/interpreter_loader_production_entrypoint_contract_test.shs
- test/01_unit/compiler/mir/demand_mir_integration_contract_test.shs
- test/01_unit/compiler/plugin_arch/kernel_plugin_migration_evidence_matrix_test.shs
- test/01_unit/compiler/portable_numeric_path_contract_test.shs
- test/01_unit/compiler/stats_bug_schema_path_contract_test.shs
- test/01_unit/infrastructure/app_io_mod_source_run_path_contract_test.shs
- test/01_unit/lib/nogc_async_mut_noalloc/kernel_plugin/strict_noalloc_proof_contract_test.shs
- test/01_unit/os/kernel/arch/x86_64_enum_variant_result_contract_test.shs
- test/01_unit/os/kernel/arch/x86_64_exec_token_result_v2_test.shs
- test/01_unit/os/kernel/arch/x86_64_text_eq_any_contract_test.shs
- test/01_unit/os/kernel/arch/x86_64_typed_handoff_source_test.shs
- test/01_unit/os/kernel/boot/baremetal_rt_string_join_contract_test.shs
- test/01_unit/os/kernel/fs/fat32_mount_value_owner_contract_test.shs
- test/01_unit/os/services/vfs/arm64_fat_raw_capacity_contract_test.shs
- test/01_unit/os/smf/kernel_plugin/real_worker_native_test.shs
- test/01_unit/os/smf/kernel_plugin/shared_memory_native_test.shs
- test/01_unit/os/smf/kernel_plugin/signature_policy_native_test.shs
- test/01_unit/os/x86_64_fs_exec_exit_oracle_test.shs
- test/01_unit/perf/live_static_compare_contract_test.shs
- test/01_unit/runtime/run_allocation_observer_reset_count_link_test.shs
- test/01_unit/runtime/run_dir_sync_focus_test.shs
- test/01_unit/runtime/run_io_uring_queue_contract_test.shs
- test/01_unit/runtime/run_runtime_exception_frame_test.shs
- test/01_unit/runtime/run_transient_empty_scope_test.shs
- test/01_unit/runtime/run_x86_avx512_xstate_runtime_test.shs
- test/01_unit/runtime/runtime_memory_owner_composition_test.shs
- test/01_unit/runtime/simple_core_argv_owner_production_link_test.shs
- test/01_unit/runtime/value_format_string_runtime_test.shs
- test/01_unit/runtime/windows_core_c_mingw_source_contract_test.shs
- test/01_unit/scripts/admit_simpleos_arm64_server_compiler_contract_test.shs
- test/01_unit/scripts/aot_lane_fences_bootstrap_receipt_contract_test.shs
- test/01_unit/scripts/aspect_pack_cardinality_contract_test.shs
- test/01_unit/scripts/aspect_pack_file_size_facade_contract_test.shs
- test/01_unit/scripts/binary_size_go_parity_producer_test.shs
- test/01_unit/scripts/bootstrap_authority_target_revalidation_sequence_contract_test.shs
- test/01_unit/scripts/bootstrap_authority_target_toctou_contract_test.shs
- test/01_unit/scripts/bootstrap_cache_archive_directory_test.shs
- test/01_unit/scripts/bootstrap_cache_escaped_writer_test.shs
- test/01_unit/scripts/bootstrap_cache_policy_test.shs
- test/01_unit/scripts/bootstrap_cache_prune_attempts_test.shs
- test/01_unit/scripts/bootstrap_cache_refresh_path_test.shs
- test/01_unit/scripts/bootstrap_compile_context_authority_contract_test.shs
- test/01_unit/scripts/bootstrap_compiler_inventory_discovery_test.shs
- test/01_unit/scripts/bootstrap_compiler_unit_execution_count_test.shs
- test/01_unit/scripts/bootstrap_evidence_retention_contract_test.shs
- test/01_unit/scripts/bootstrap_fingerprint_diff_test.shs
- test/01_unit/scripts/bootstrap_fingerprint_tmp_contract_test.shs
- test/01_unit/scripts/bootstrap_frozen_plugin_scope_contract_test.shs
- test/01_unit/scripts/bootstrap_hosted_runtime_windows_find_authority_test.shs
- test/01_unit/scripts/bootstrap_jest_json_validator_test.shs
- test/01_unit/scripts/bootstrap_jobs_policy_test.shs
- test/01_unit/scripts/bootstrap_module_documentation_classification_test.shs
- test/01_unit/scripts/bootstrap_phase_status_classification_test.shs
- test/01_unit/scripts/bootstrap_phase1_current_authority_test.shs
- test/01_unit/scripts/bootstrap_phase1_tool_containment_test.shs
- test/01_unit/scripts/bootstrap_phase2_portable_loader_contract_test.shs
- test/01_unit/scripts/bootstrap_phase3_docs_inventory_test.shs
- test/01_unit/scripts/bootstrap_phase3_expanded_runner_test.shs
- test/01_unit/scripts/bootstrap_phase3_nested_inventory_test.shs
- test/01_unit/scripts/bootstrap_planner_admission_bound_contract_test.shs
- test/01_unit/scripts/bootstrap_portability_owner_contract_test.shs
- test/01_unit/scripts/bootstrap_release_cache_vector_test.shs
- test/01_unit/scripts/bootstrap_reviewed_reason_test.shs
- test/01_unit/scripts/bootstrap_sanity_session_scrub_test.shs
- test/01_unit/scripts/bootstrap_session_cmd_argv_windows_test.shs
- test/01_unit/scripts/bootstrap_session_contract_test.shs
- test/01_unit/scripts/bootstrap_session_guard_test.shs
- test/01_unit/scripts/bootstrap_session_transcript_test.shs
- test/01_unit/scripts/bootstrap_stage2_positional_stage3_route_contract_test.shs
- test/01_unit/scripts/bootstrap_stage2_rss_observation_budget_test.shs
- test/01_unit/scripts/bootstrap_stage2_sanity_output_preflight_contract_test.shs
- test/01_unit/scripts/bootstrap_stage2_struct_receiver_gate_test.shs
- test/01_unit/scripts/bootstrap_stage3_atomic_generation_publication_test.shs
- test/01_unit/scripts/bootstrap_stage3_current_acceptance_contract_test.shs
- test/01_unit/scripts/bootstrap_stage3_darwin_nested_watchdog_test.shs
- test/01_unit/scripts/bootstrap_stage3_descriptor_map_contract_test.shs
- test/01_unit/scripts/bootstrap_stage3_direct_parallel_policy_test.shs
- test/01_unit/scripts/bootstrap_stage3_directory_snapshot_streaming_test.shs
- test/01_unit/scripts/bootstrap_stage3_evidence_reuse_contract_test.shs
- test/01_unit/scripts/bootstrap_stage3_explicit_one_route_test.shs
- test/01_unit/scripts/bootstrap_stage3_fingerprint_details_verification_test.shs
- test/01_unit/scripts/bootstrap_stage3_frontend_cache_off_parity_contract_test.shs
- test/01_unit/scripts/bootstrap_stage3_full_src_snapshot_test.shs
- test/01_unit/scripts/bootstrap_stage3_helper_capsule_callers_test.shs
- test/01_unit/scripts/bootstrap_stage3_manifest_focused_route_contract_test.shs
- test/01_unit/scripts/bootstrap_stage3_mode1_admission_contract_test.shs
- test/01_unit/scripts/bootstrap_stage3_os_source_snapshot_test.shs
- test/01_unit/scripts/bootstrap_stage3_plugin_source_snapshot_test.shs
- test/01_unit/scripts/bootstrap_stage3_receipt_pure_parent_test.shs
- test/01_unit/scripts/bootstrap_stage3_resume_manifest_receiver_env_contract_test.shs
- test/01_unit/scripts/bootstrap_stage3_resume_output_path_test.shs
- test/01_unit/scripts/bootstrap_stage3_resume_snapshot_binding_contract_test.shs
- test/01_unit/scripts/bootstrap_stage3_resume_source_lineage_contract_test.shs
- test/01_unit/scripts/bootstrap_stage3_runtime_policy_source_snapshot_test.shs
- test/01_unit/scripts/bootstrap_stage3_snapshot_path_contract_test.shs
- test/01_unit/scripts/bootstrap_stage3_unicode_git_state_test.shs
- test/01_unit/scripts/bootstrap_stage3_unit_supervisor_test.shs
- test/01_unit/scripts/bootstrap_stage3_verification_receipt_parser_test.shs
- test/01_unit/scripts/bootstrap_stage3_windows_native_compatibility_test.shs
- test/01_unit/scripts/bootstrap_stage4_atomic_local_deploy_test.shs
- test/01_unit/scripts/bootstrap_stop_after_stage2_contract_test.shs
- test/01_unit/scripts/bootstrap_stop_after_stage3_contract_test.shs
- test/01_unit/scripts/bootstrap_strategy_fallback_contract_test.shs
- test/01_unit/scripts/bootstrap_transcript_failure_diagnostics_test.shs
- test/01_unit/scripts/bootstrap_whole_build_two_worker_floor_test.shs
- test/01_unit/scripts/bootstrap_windows_cl_mode_test.shs
- test/01_unit/scripts/bootstrap_windows_compatibility_junction_test.shs
- test/01_unit/scripts/bootstrap_windows_native_metadata_owner_test.shs
- test/01_unit/scripts/bootstrap_windows_output_root_preflight_test.shs
- test/01_unit/scripts/bootstrap_windows_startup_owner_test.shs
- test/01_unit/scripts/candidate_frontend_darwin_capture_test.shs
- test/01_unit/scripts/candidate_frontend_hash_portability_test.shs
- test/01_unit/scripts/caret_external_receipt_semantic_quarantine_test.shs
- test/01_unit/scripts/check/cert/freeze_tool_qual_default_path_contract_test.shs
- test/01_unit/scripts/check/cert/fuzz_diff_default_path_contract_test.shs
- test/01_unit/scripts/check/cert/soundness_diff_default_path_contract_test.shs
- test/01_unit/scripts/check/cert/stress_suite_default_path_contract_test.shs
- test/01_unit/scripts/check/cert/tool_qual_corpus_default_path_contract_test.shs
- test/01_unit/scripts/check/cert/tool_qual_meta_default_path_contract_test.shs
- test/01_unit/scripts/check_no_sabotage_residue_contract_test.shs
- test/01_unit/scripts/check_seed_builds_push_selftest_isolation_test.shs
- test/01_unit/scripts/checker_performance_harness_test.shs
- test/01_unit/scripts/cli_compileoptions_layer_boundary_test.shs
- test/01_unit/scripts/compiled_check_tree_test.shs
- test/01_unit/scripts/compiler_interpreter_loader_layering_mutation_test.shs
- test/01_unit/scripts/completeness_contract_lock_gate_test.shs
- test/01_unit/scripts/conflict_marker_guard_raw_diff_test.shs
- test/01_unit/scripts/core_c_capsule_failure_retention_test.shs
- test/01_unit/scripts/critical_release_seal_gate_test.shs
- test/01_unit/scripts/cross_language_execution_mode_receipt_contract_test.shs
- test/01_unit/scripts/db_perf_compare_admission_contract_test.shs
- test/01_unit/scripts/db_runtime_capsule_provenance_gate_test.shs
- test/01_unit/scripts/db_server_request_port_evidence_test.shs
- test/01_unit/scripts/demand_driven_smf_evidence_contract_test.shs
- test/01_unit/scripts/doc06_spec_layout_migration_test.shs
- test/01_unit/scripts/dynsmf_facet_ref_count_contract_test.shs
- test/01_unit/scripts/engine2d_rendering_probe_source_contract_test.shs
- test/01_unit/scripts/engine2d_rendering_raw_v1_writer_contract_test.shs
- test/01_unit/scripts/f64_call_abi_guard_contract_test.shs
- test/01_unit/scripts/gdb_inferior_strict_gate_test.shs
- test/01_unit/scripts/interpreter_startup_producer_test.shs
- test/01_unit/scripts/io_parity_mirror_contract_test.shs
- test/01_unit/scripts/kpf_cross_placement_semantic_mutation_test.shs
- test/01_unit/scripts/kpf_extended_enum_sealer_mutation_test.shs
- test/01_unit/scripts/linux_vulkan_renderdoc_reason_precedence_contract_test.shs
- test/01_unit/scripts/macos_m5_hermetic_snapshot_wrapper_test.shs
- test/01_unit/scripts/macos_process_live_native_test.shs
- test/01_unit/scripts/macos_process_observer_detail_test.shs
- test/01_unit/scripts/macos_process_observer_permission_test.shs
- test/01_unit/scripts/macos_process_observer_test.shs
- test/01_unit/scripts/macos_reverse_reference_m4_contract_test.shs
- test/01_unit/scripts/macos_stage3_authority_portability_contract_test.shs
- test/01_unit/scripts/materialize_symlinks_windows_posix_sh_guard_test.shs
- test/01_unit/scripts/mcdc_cross_engine_vectors_gate_test.shs
- test/01_unit/scripts/mci_v2_independent_review_contract_test.shs
- test/01_unit/scripts/mci_v2_lane_signer_contract_test.shs
- test/01_unit/scripts/mcp_startup_lib_obsolete_contract_test.shs
- test/01_unit/scripts/mir_enum_discriminant_owner_contract_test.shs
- test/01_unit/scripts/native_smoke_matrix_progress_contract_test.shs
- test/01_unit/scripts/no_refresh_file_lock_test.shs
- test/01_unit/scripts/orchestration_storage_roots_test.shs
- test/01_unit/scripts/pane_launcher_lifetime_test.shs
- test/01_unit/scripts/performance_receipt_fail_closed_test.shs
- test/01_unit/scripts/performance_target_identity_external_test.shs
- test/01_unit/scripts/performance_target_identity_test.shs
- test/01_unit/scripts/phase2_capsule_schema_layout_contract_test.shs
- test/01_unit/scripts/phase3_test_inventory_test.shs
- test/01_unit/scripts/portable_process_lock_macos_observer_test.shs
- test/01_unit/scripts/portable_process_lock_windows_birth_test.shs
- test/01_unit/scripts/portable_semantic_scope_authority_contract_test.shs
- test/01_unit/scripts/portable_session_exec_contract_test.shs
- test/01_unit/scripts/pr_approve_workflow_contract_test.shs
- test/01_unit/scripts/prepush_dispatcher_git_env_isolation_test.shs
- test/01_unit/scripts/preserve_phase_binary_keep_newest_test.shs
- test/01_unit/scripts/process_group_bounded_log_contract_test.shs
- test/01_unit/scripts/process_tree_rss_absolute_limit_test.shs
- test/01_unit/scripts/process_tree_rss_bounded_diagnostic_test.shs
- test/01_unit/scripts/process_tree_rss_cgroup_root_test.shs
- test/01_unit/scripts/process_tree_rss_controller_exit_test.shs
- test/01_unit/scripts/process_tree_rss_deadline_test.shs
- test/01_unit/scripts/process_tree_rss_diagnostics_test.shs
- test/01_unit/scripts/process_tree_rss_monitor_budget_test.shs
- test/01_unit/scripts/process_tree_rss_monitor_test.shs
- test/01_unit/scripts/process_tree_rss_observation_budget_test.shs
- test/01_unit/scripts/process_tree_rss_proc_stat_test.shs
- test/01_unit/scripts/process_tree_rss_watchdog_test.shs
- test/01_unit/scripts/process_tree_rss_windows_parent_guard_test.shs
- test/01_unit/scripts/product_frontend_worker_estimates_test.shs
- test/01_unit/scripts/publish_win_stage_rc_msvc_contract_test.shs
- test/01_unit/scripts/publish_win_stage_rc_tmp_cleanup_test.shs
- test/01_unit/scripts/required_gates_sparse_checkout_test.shs
- test/01_unit/scripts/rt_unsafe_priority_contract_test.shs
- test/01_unit/scripts/runtime_process_owned_linux_random_guard_test.shs
- test/01_unit/scripts/sanitizer_smoke_reporting_test.shs
- test/01_unit/scripts/scv_bootstrap_composition_scope_contract_test.shs
- test/01_unit/scripts/sffi_admission_acceptance_runner_test.shs
- test/01_unit/scripts/sffi_contract_inventory_columns_test.shs
- test/01_unit/scripts/sffi_evidence_admission_contract_test.shs
- test/01_unit/scripts/sffi_v2_authority_gate_test.shs
- test/01_unit/scripts/simple_runtime_provenance_selection_test.shs
- test/01_unit/scripts/simpleos_toolchain_desktop_boot_receipt_contract_test.shs
- test/01_unit/scripts/simpleos_workflow_bootstrap_memory_route_test.shs
- test/01_unit/scripts/stage2_parent_admission_test.shs
- test/01_unit/scripts/stage2_parent_receipt_producer_test.shs
- test/01_unit/scripts/storage_roots_darwin_case_marker_test.shs
- test/01_unit/scripts/test_daemon_environment_identity_wiring_test.shs
- test/01_unit/scripts/tool_storage_roots_mutation_test.shs
- test/01_unit/scripts/tree_size_guard_duplicate_entry_test.shs
- test/01_unit/scripts/unoq_qrb2210_cpu_server_live_runner_contract_test.shs
- test/01_unit/scripts/unoq_qrb2210_native_2d_live_runner_contract_test.shs
- test/01_unit/scripts/vulkan_2d_c_evidence_contract_test.shs
- test/01_unit/scripts/vulkan_2d_c_immutable_runs_contract_test.shs
- test/01_unit/scripts/web_server_request_port_evidence_test.shs
- test/01_unit/scripts/windows_checkout_placeholder_contract_test.shs
- test/01_unit/scripts/windows_msvc_cl_environment_test.shs
- test/01_unit/scripts/windows_spipe_pending_policy_test.shs
- test/01_unit/sdk/kernel_plugin/c_cpp_conformance_test.shs
- test/01_unit/tool/kernel_plugin_schema/c_abi_conformance_test.shs
- test/01_unit/tool/kernel_plugin_schema/generated_wit_fixture_test.shs
- test/01_unit/tools/mail_cli/account_secret_argv_release_test.shs
- test/02_integration/bootstrap_diagnostic_sweep_resume_test.shs
- test/02_integration/bootstrap_stage3_git_path_bytes_test.shs
- test/02_integration/bootstrap_stage3_git_state_paths_test.shs
- test/02_integration/bootstrap_stage3_git_state_test.shs
- test/02_integration/bootstrap_stage3_retry_preflight_order_test.shs
- test/02_integration/bootstrap_stage3_runtime_authority_root_test.shs
- test/02_integration/compiler/demand_dirty_mixed_scc_publication_contract_test.shs
- test/02_integration/compiler/raw_rt_lint_cli_fix_test.shs
- test/02_integration/runtime/run_process_stdout_lifecycle_native_test.shs
- test/02_integration/simple_release_wrapper_platform_probe_test.shs
- test/02_integration/stage4_diagnostic_two_phase_test.shs
- test/02_integration/tool/renderdoc_exporter_contract_test.shs
- test/03_system/app/spipe/feature/spipe_local_knowledge_setup_contract_test.shs
- test/04_smoke/native_parent_parse_closure_scope_test.shs
- test/05_perf/profile_scripts/compiler_loader_retained_contract_test.shs
- test/05_perf/profile_scripts/cross_language_byte_retained_contract_test.shs
- test/05_perf/profile_scripts/cross_language_compile_failure_contract_test.shs
- test/05_perf/profile_scripts/cross_language_compiler_provenance_contract_test.shs
- test/05_perf/profile_scripts/engine2d_vulkan_c_parity_contract_test.shs
- test/05_perf/profile_scripts/gui_perf_bench_terminal_receipt_contract_test.shs
- test/05_perf/profile_scripts/mcdc_k3_dynload_eligibility_contract_test.shs
- test/05_perf/startup/aspect_pack_section_overlap_sweep_contract_test.shs
- test/05_perf/startup/aspect_pack_single_section_scan_contract_test.shs
- test/05_perf/startup/component_dynsmf_binding_index_contract_test.shs
- test/05_perf/startup/component_dynsmf_loaded_index_contract_test.shs
- test/05_perf/startup/dbfs_file_meta_cache_cardinality_contract_test.shs
- test/05_perf/startup/decorators_cache_cardinality_contract_test.shs
- test/05_perf/startup/duplicate_cache_stats_key_snapshot_contract_test.shs
- test/05_perf/startup/dynsmf_autoload_manifest_index_contract_test.shs
- test/05_perf/startup/dynsmf_disabled_policy_index_contract_test.shs
- test/05_perf/startup/dynsmf_dispatch_snapshot_bound_contract_test.shs
- test/05_perf/startup/dynsmf_export_witness_single_parse_contract_test.shs
- test/05_perf/startup/dynsmf_frozen_payload_handoff_contract_test.shs
- test/05_perf/startup/dynsmf_library_facet_revocation_index_contract_test.shs
- test/05_perf/startup/dynsmf_loaded_membership_index_contract_test.shs
- test/05_perf/startup/dynsmf_section_overlap_sweep_contract_test.shs
- test/05_perf/startup/dynsmf_startup_settings_join_contract_test.shs
- test/05_perf/startup/dynsmf_trust_admission_index_contract_test.shs
- test/05_perf/startup/dynsmf_trust_digest_validator_contract_test.shs
- test/05_perf/startup/dynsmf_trust_parse_index_contract_test.shs
- test/05_perf/startup/dynsmf_trusted_binding_owner_index_contract_test.shs
- test/05_perf/startup/dynsmf_trusted_facet_index_contract_test.shs
- test/05_perf/startup/http_response_cache_admission_contract_test.shs
- test/05_perf/startup/sql_stmt_cache_admission_contract_test.shs

## (c) needs special env (left alone)
- scripts/check/bootstrap_compiler_ceiling_wrapper_test.shs
- scripts/resource/kill_simple_monitor_test.shs
- test/00_unit/scripts/devhub_wrapper_runtime_selection_test.shs
- test/00_unit/scripts/windows_stable_journal_recovery_test.shs
- test/01_unit/app/compiler_entrypoint/lockless_refresh_stress_test.shs
- test/01_unit/app/debug/remote/protocol/gdb_mi_transport_path_contract_test.shs
- test/01_unit/compiler/backend/backend_aot_object_path_source_contract_test.shs
- test/01_unit/compiler/backend/llvm_actual_join_close_path_test.shs
- test/01_unit/compiler/backend/llvm_codegen_pool_ir_scope_source_contract_test.shs
- test/01_unit/compiler/backend/simpleos_cranelift_target_normalization_source_contract_test.shs
- test/01_unit/compiler/backend_plugin/backend_plugin_v1_windows_bridge_test.shs
- test/01_unit/compiler/native_all_link_order_contract_test.shs
- test/01_unit/compiler/perf/demand_compile_production_integration_contract_test.shs
- test/01_unit/compiler/plugin_arch/kernel_phase7_strict_capability_regression_test.shs
- test/01_unit/compiler/plugin_arch/kernel_relocation_module_resolution_test.shs
- test/01_unit/compiler/stage4_archive_closure_target_source_contract_test.shs
- test/01_unit/freebsd_bootstrap_qemu_cloudinit_iso_path_test.shs
- test/01_unit/freebsd_bootstrap_qemu_tcg_isa_test.shs
- test/01_unit/os/aarch64_limine_lane_fail_closed_test.shs
- test/01_unit/os/kernel/arch/arm64_runtime_ownership_contract_test.shs
- test/01_unit/os/kernel/arch/riscv64_unwrap_or_trap_contract_test.shs
- test/01_unit/os/kernel/loader/rv64_streamed_fat_elf_loader_contract_test.shs
- test/01_unit/os/port/make_os_disk_capacity_receipt_contract_test.shs
- test/01_unit/os/port/simpleos_arch_runtime_owner_split_contract_test.shs
- test/01_unit/os/port/simpleos_sysroot_runtime_provider_test.shs
- test/01_unit/os/qemu/x86_32_fat_listing_contract_test.shs
- test/01_unit/os/qemu/x86_32_nonce_candidate_scan_contract_test.shs
- test/01_unit/os/qemu_lane_wiring_reserved_identifier_test.shs
- test/01_unit/os/riscv64_display_abi_contract_test.shs
- test/01_unit/os/riscv64_full_networking_runtime_compile_test.shs
- test/01_unit/os/services/vfs/arm64_qemu_nonce_root_route_contract_test.shs
- test/01_unit/os/simpleos_core_archive_tool_discovery_test.shs
- test/01_unit/os/simpleos_server_authenticated_entries_test.shs
- test/01_unit/os/simpleos_ud2_fault_link_contract_win_test.shs
- test/01_unit/runtime/mingw_ucrt_runtime_compile_contract_test.shs
- test/01_unit/runtime/native_all_struct_receiver_provider_contract_test.shs
- test/01_unit/runtime/rt_fork_crash_handler_darwin_test.shs
- test/01_unit/runtime/run_file_stat_capsule_test.shs
- test/01_unit/runtime/run_process_piped_cold_handle_budget_test.shs
- test/01_unit/runtime/run_process_piped_handle_stress_test.shs
- test/01_unit/runtime/run_thread_local_scalar_provider_test.shs
- test/01_unit/runtime/runtime_any_ops_contract_test.shs
- test/01_unit/runtime/runtime_bdd_native_exports_contract_test.shs
- test/01_unit/runtime/runtime_math_classification_parity_test.shs
- test/01_unit/scripts/backend_artifact_identity_target_environment_test.shs
- test/01_unit/scripts/backend_evidence_branch_coverage_gate_test.shs
- test/01_unit/scripts/bootstrap_abi_policy_contract_test.shs
- test/01_unit/scripts/bootstrap_build_jobs_policy_contract_test.shs
- test/01_unit/scripts/bootstrap_build_jobs_provenance_contract_test.shs
- test/01_unit/scripts/bootstrap_cache_hir_controls_test.shs
- test/01_unit/scripts/bootstrap_cache_lineage_resume_test.shs
- test/01_unit/scripts/bootstrap_cache_rust_source_refresh_test.shs
- test/01_unit/scripts/bootstrap_cache_source_refresh_test.shs
- test/01_unit/scripts/bootstrap_cargo_lock_host_policy_test.shs
- test/01_unit/scripts/bootstrap_cargo_prune_targets_test.shs
- test/01_unit/scripts/bootstrap_centralized_storage_roots_test.shs
- test/01_unit/scripts/bootstrap_compare_files_test.shs
- test/01_unit/scripts/bootstrap_composition_source_scope_test.shs
- test/01_unit/scripts/bootstrap_deploy_tx_provider_entry_test.shs
- test/01_unit/scripts/bootstrap_freebsd_cargo_bounded_contract_test.shs
- test/01_unit/scripts/bootstrap_git_state_dialect_test.shs
- test/01_unit/scripts/bootstrap_host_config_home_projection_test.shs
- test/01_unit/scripts/bootstrap_hosted_runtime_authority_contract_test.shs
- test/01_unit/scripts/bootstrap_jobs_propagation_test.shs
- test/01_unit/scripts/bootstrap_k1_composition_receipt_test.shs
- test/01_unit/scripts/bootstrap_linux_glibc_link_compat_test.shs
- test/01_unit/scripts/bootstrap_llvm_static_cli_provider_test.shs
- test/01_unit/scripts/bootstrap_llvm23_platform_detection_test.shs
- test/01_unit/scripts/bootstrap_macos_cocoa_owner_gate_test.shs
- test/01_unit/scripts/bootstrap_managed_readobj_authority_test.shs
- test/01_unit/scripts/bootstrap_module_init_aggregate_contract_test.shs
- test/01_unit/scripts/bootstrap_msvc_environment_contract_test.shs
- test/01_unit/scripts/bootstrap_native_aot_evidence_contract_test.shs
- test/01_unit/scripts/bootstrap_native_toolchain_fingerprint_test.shs
- test/01_unit/scripts/bootstrap_nested_guard_contract_test.shs
- test/01_unit/scripts/bootstrap_parent_msvc_env_test.shs
- test/01_unit/scripts/bootstrap_phase_evidence_workflow_test.shs
- test/01_unit/scripts/bootstrap_phase_stage1_native_build_authority_test.shs
- test/01_unit/scripts/bootstrap_phase_tool_cache_contract_test.shs
- test/01_unit/scripts/bootstrap_phase_unix_toolchain_test.shs
- test/01_unit/scripts/bootstrap_phase_windows_toolchain_test.shs
- test/01_unit/scripts/bootstrap_phase2_capsule_consumer_compat_test.shs
- test/01_unit/scripts/bootstrap_preflight_disk_early_test.shs
- test/01_unit/scripts/bootstrap_preflight_evidence_contract_test.shs
- test/01_unit/scripts/bootstrap_private_rust_stage2_contract_test.shs
- test/01_unit/scripts/bootstrap_progress_watch_macos_test.shs
- test/01_unit/scripts/bootstrap_progress_watch_tree_test.shs
- test/01_unit/scripts/bootstrap_release_attempt_archive_test.shs
- test/01_unit/scripts/bootstrap_resume_stage2_from_cache_contract_test.shs
- test/01_unit/scripts/bootstrap_resume_stage4_from_admitted_contract_test.shs
- test/01_unit/scripts/bootstrap_rust_authority_incremental_cache_contract_test.shs
- test/01_unit/scripts/bootstrap_rust_native_probe_test.shs
- test/01_unit/scripts/bootstrap_rust_policy_relocation_test.shs
- test/01_unit/scripts/bootstrap_rust_toolchain_diagnostics_contract_test.shs
- test/01_unit/scripts/bootstrap_rust_toolchain_resolution_test.shs
- test/01_unit/scripts/bootstrap_stage2_llvm_receiver_admission_contract_test.shs
- test/01_unit/scripts/bootstrap_stage2_mimalloc_env_contract_test.shs
- test/01_unit/scripts/bootstrap_stage2_retry_help_cleanup_contract_test.shs
- test/01_unit/scripts/bootstrap_stage2_timeout_cascade_test.shs
- test/01_unit/scripts/bootstrap_stage3_abi_forwarding_test.shs
- test/01_unit/scripts/bootstrap_stage3_actual_peer_identity_contract_test.shs
- test/01_unit/scripts/bootstrap_stage3_darwin_rss_cap_contract_test.shs
- test/01_unit/scripts/bootstrap_stage3_heavy_process_admission_contract_test.shs
- test/01_unit/scripts/bootstrap_stage3_receipt_reuse_test.shs
- test/01_unit/scripts/bootstrap_stage3_resume_exit_propagation_contract_test.shs
- test/01_unit/scripts/bootstrap_stage3_rss_evidence_contract_test.shs
- test/01_unit/scripts/bootstrap_stage3_runner_publication_contract_test.shs
- test/01_unit/scripts/bootstrap_stage3_seed_tuple_projection_test.shs
- test/01_unit/scripts/bootstrap_stage3_shared_runner_contract_test.shs
- test/01_unit/scripts/bootstrap_stage3_streaming_explicit_entry_contract_test.shs
- test/01_unit/scripts/bootstrap_stage3_transcript_argv_value_test.shs
- test/01_unit/scripts/bootstrap_stage3_windows_bracket_paths_test.shs
- test/01_unit/scripts/bootstrap_stage3_windows_llvm23_dynamic_authority_test.shs
- test/01_unit/scripts/bootstrap_stage3_windows_llvm23_metadata_retry_test.shs
- test/01_unit/scripts/bootstrap_stage3_windows_long_paths_test.shs
- test/01_unit/scripts/bootstrap_stage4_atomic_local_deploy_contract_test.shs
- test/01_unit/scripts/bootstrap_stage4_timeout_descendant_contract_test.shs
- test/01_unit/scripts/bootstrap_strategy_supervisor_test.shs
- test/01_unit/scripts/bootstrap_vector_argument_files_test.shs
- test/01_unit/scripts/bootstrap_windows_c_admission_diagnostics_test.shs
- test/01_unit/scripts/bootstrap_windows_cargo_path_budget_test.shs
- test/01_unit/scripts/bootstrap_windows_cargo_shared_lock_test.shs
- test/01_unit/scripts/bootstrap_windows_cargo_status_test.shs
- test/01_unit/scripts/bootstrap_windows_gnu_tool_authority_test.shs
- test/01_unit/scripts/bootstrap_windows_msvc_tool_authority_test.shs
- test/01_unit/scripts/bootstrap_windows_nested_job_cache_test.shs
- test/01_unit/scripts/bootstrap_windows_rss_contract_test.shs
- test/01_unit/scripts/candidate_frontend_windows_job_policy_test.shs
- test/01_unit/scripts/ci_fast_gates_perf_contract_test.shs
- test/01_unit/scripts/ci_runtime_provisioning_contract_test.shs
- test/01_unit/scripts/cosmos_hal_policy_evidence_contract_test.shs
- test/01_unit/scripts/cpu_backend_artifact_environment_result_test.shs
- test/01_unit/scripts/dynamic_loader_real_execution_contract_test.shs
- test/01_unit/scripts/freebsd_bootstrap_cc_selection_test.shs
- test/01_unit/scripts/freebsd_host_setup_contract_test.shs
- test/01_unit/scripts/freebsd_qemu_arm64_kvm_contract_test.shs
- test/01_unit/scripts/freebsd_qemu_disk_capacity_contract_test.shs
- test/01_unit/scripts/freebsd_qemu_host_free_guard_contract_test.shs
- test/01_unit/scripts/freebsd_qemu_invocation_contract_test.shs
- test/01_unit/scripts/freebsd_riscv_host_platform_test.shs
- test/01_unit/scripts/freebsd_riscv_target_alignment_test.shs
- test/01_unit/scripts/freebsd_selfhost_ci_contract_test.shs
- test/01_unit/scripts/freebsd_source_authority_contract_test.shs
- test/01_unit/scripts/freebsd_source_projection_contract_test.shs
- test/01_unit/scripts/gpu_backend_environment_matrix_accounting_test.shs
- test/01_unit/scripts/host_gpu_backend_fallback_test.shs
- test/01_unit/scripts/io_parity_honesty_contract_test.shs
- test/01_unit/scripts/io_parity_receipt_contract_test.shs
- test/01_unit/scripts/macos_deploy_slot_contract_test.shs
- test/01_unit/scripts/materialize_symlinks_windows_centralized_storage_receipt_root_test.shs
- test/01_unit/scripts/materialize_symlinks_windows_cycle_test.shs
- test/01_unit/scripts/materialize_symlinks_windows_test.shs
- test/01_unit/scripts/mci_v2_qemu_wm_evidence_contract_test.shs
- test/01_unit/scripts/mci_v2_release_orchestrator_contract_test.shs
- test/01_unit/scripts/mci_v2_rendering_bundle_adapter_contract_test.shs
- test/01_unit/scripts/mci_v2_rendering_live_collector_contract_test.shs
- test/01_unit/scripts/mci_v2_simpleos_collector_producer_contract_test.shs
- test/01_unit/scripts/package_phase1_spk_windows_bin_test.shs
- test/01_unit/scripts/phase_ladder_release_manifest_test.shs
- test/01_unit/scripts/phase2_runtime_capsule_contract_test.shs
- test/01_unit/scripts/qemu_virgl_container_contract_test.shs
- test/01_unit/scripts/release_checker_contract_test.shs
- test/01_unit/scripts/release_version_consistency_contract_test.shs
- test/01_unit/scripts/resolve_bootstrap_min_phase_test.shs
- test/01_unit/scripts/riscv_gen2_hwir_qualification_evidence_producer_contract_test.shs
- test/01_unit/scripts/riscv_gen2_hwir_qualification_runner_contract_test.shs
- test/01_unit/scripts/riscv_gen2_writer_red_failpoint_test.shs
- test/01_unit/scripts/riscv_gen2_zca_oracle_gate_test.shs
- test/01_unit/scripts/riscv_gen2_zca_sail_batch_adapter_test.shs
- test/01_unit/scripts/riscv_hardware_gate_provenance_contract_test.shs
- test/01_unit/scripts/riscv_isa_gate_calibration_path_mutation_test.shs
- test/01_unit/scripts/riscv_isa_gate_fixture_mutation_test.shs
- test/01_unit/scripts/riscv_isa_gate_runner_path_mutation_test.shs
- test/01_unit/scripts/run_whole_test_lanes_test.shs
- test/01_unit/scripts/rust_go_benchmark_producer_test.shs
- test/01_unit/scripts/rust_go_benchmark_samples_test.shs
- test/01_unit/scripts/rv64_authenticated_media_contract_test.shs
- test/01_unit/scripts/rv64_generated_smoke_validation_contract_test.shs
- test/01_unit/scripts/seed_backend_module_alias_contract_test.shs
- test/01_unit/scripts/seed_list_comprehension_join_native_test.shs
- test/01_unit/scripts/simpleos_admitted_runtime_contract_test.shs
- test/01_unit/scripts/simpleos_guest_llvm_fs_provision_contract_test.shs
- test/01_unit/scripts/simpleos_nonbootstrap_acceptance_contract_test.shs
- test/01_unit/scripts/simpleos_server_payload_compiler_admission_test.shs
- test/01_unit/scripts/sosix_rebuild_admitted_compiler_forwarding_contract_test.shs
- test/01_unit/scripts/stage3_recovery_authority_guard_test.shs
- test/01_unit/scripts/stage3_serial_low_memory_contract_test.shs
- test/01_unit/scripts/stage4_tooling_named_suites_contract_test.shs
- test/01_unit/scripts/tool_storage_roots_contract_test.shs
- test/01_unit/scripts/windows_ci_clang_authority_test.shs
- test/01_unit/scripts/windows_mingw_bootstrap_env_parity_test.shs
- test/01_unit/scripts/x86_64_authenticated_media_contract_test.shs
- test/01_unit/tool/kernel_plugin_schema/generated_abi_layout_mutation_test.shs
- test/01_unit/tool/kernel_plugin_schema/generated_sdk_conformance_test.shs
- test/02_integration/app/check_phase_profile_test.shs
- test/02_integration/bootstrap_diagnostic_sweep_test.shs
- test/02_integration/bootstrap_diagnostics_mode_test.shs
- test/02_integration/bootstrap_stage3_git_state_materialized_test.shs
- test/02_integration/bootstrap_stage3_resume_from_admitted_test.shs
- test/02_integration/bootstrap_stage3_source_snapshot_scope_test.shs
- test/02_integration/bootstrap_stage4_scheduler_run_allocation_test.shs
- test/02_integration/bootstrap_stage4_tooling_matrix_test.shs
- test/02_integration/compiler/hello_world_positional_one_binary_bootstrap_modes_test.shs
- test/02_integration/freebsd_bootstrap_qemu_cross_arch_contract_test.shs
- test/02_integration/freebsd_bootstrap_qemu_isolation_contract_test.shs
- test/02_integration/lib/slang_prefix_cache_shim_contract_test.shs
- test/02_integration/os/cosmos/run_cosmos_ftl_erase_failure_test.shs
- test/02_integration/os/cosmos/run_cosmos_ftl_nfc_recovery_wrap_test.shs
- test/02_integration/os/cosmos/run_cosmos_nvme_admin_queue_binding_test.shs
- test/02_integration/os/cosmos/run_cosmos_nvme_dispatch_queue_test.shs
- test/02_integration/os/cosmos/run_cosmos_pcie_queue_contract_test.shs
- test/02_integration/os/cosmos/run_cosmos_policy_build_wiring_contract_test.shs
- test/02_integration/simpleos_compiler_filesystem_qemu_contract_test.shs
- test/03_system/check/stage2_command_transcript_contract_test.shs
- test/03_system/check/stage2_exact_source_compile_stack_policy_test.shs
- test/03_system/compiler/feature/kernel_plugin/cross_placement_semantic_conformance_test.shs
- test/03_system/compiler/feature/native_zero_work_process_crash_test.shs
- test/05_perf/profile_scripts/cross_language_average_contract_test.shs
- test/05_perf/profile_scripts/cross_language_compile_matrix_contract_test.shs
- test/05_perf/profile_scripts/cross_language_retained_negative_contract_test.shs
- test/05_perf/profile_scripts/cross_language_retained_schema_contract_test.shs
- test/05_perf/profile_scripts/native_function_value_callback_regression_test.shs
- test/05_perf/profile_scripts/render_8k80_matrix_gate_test.shs
- test/05_perf/profile_scripts/render_8k80_receipt_gate_test.shs
- test/05_perf/scv/cold_inventory_profile_contract_test.shs
- test/05_perf/startup/class_a/startup_class_a_schema_contract_test.shs
- test/fixtures/js/compat_test.shs
- test/system/simpleos/wm_kernel_input_set_gate_test.shs
- test/system/simpleos/wm_native_build_progress_test.shs

## Linux run results (WSL ubuntu-p2, shallow clone, 120s timeout, 16 parallel, TMPDIR on tmpfs)
159 of the 288 (b) candidates are green under sh; 3 more are green only under bash (not wired). 126 fail:

| exit | test |
|---|---|
| 127 | examples/10_tooling/trace32_tools/relay_power/relay_power_cycle_test.shs |
| 1 | scripts/check/bootstrap_compiler_headroom_boundary_test.shs |
| 2 | test/01_unit/app/arch_check_fast_help_contract_test.shs |
| 1 | test/01_unit/app/compiler_entrypoint/demand_entry_path_contract_test.shs |
| 2 | test/01_unit/app/stdio_runtime_owner_contract_test.shs |
| 1 | test/01_unit/compiler/action_graph/demand_compile_integration_contract_test.shs |
| 1 | test/01_unit/compiler/backend/io_mmap_text_abi_runtime_link_contract_test.shs |
| 1 | test/01_unit/compiler/backend_plugin/backend_plugin_v1_native_bridge_test.shs |
| 1 | test/01_unit/compiler/driver/backend_plugin_cli_propagation_contract_test.shs |
| 1 | test/01_unit/compiler/driver/entry_closure_app_doc_source_contract_test.shs |
| 1 | test/01_unit/compiler/driver/memory_snapshot_sink_contract_test.shs |
| 2 | test/01_unit/compiler/hir/conditional_empty_symbol_keys_native_test.shs |
| 1 | test/01_unit/compiler/interp/interpreter_load_facade_contract_test.shs |
| 1 | test/01_unit/compiler/lint/raw_if_chain_lint_walkers_source_test.shs |
| 2 | test/01_unit/compiler/loader/interpreter_loader_production_entrypoint_contract_test.shs |
| 1 | test/01_unit/compiler/mir/demand_mir_integration_contract_test.shs |
| 1 | test/01_unit/compiler/plugin_arch/kernel_plugin_migration_evidence_matrix_test.shs |
| 1 | test/01_unit/compiler/stats_bug_schema_path_contract_test.shs |
| 1 | test/01_unit/os/services/vfs/arm64_fat_raw_capacity_contract_test.shs |
| 1 | test/01_unit/os/x86_64_fs_exec_exit_oracle_test.shs |
| 1 | test/01_unit/perf/live_static_compare_contract_test.shs |
| 1 | test/01_unit/runtime/run_dir_sync_focus_test.shs |
| 1 | test/01_unit/runtime/run_runtime_exception_frame_test.shs |
| 1 | test/01_unit/runtime/runtime_memory_owner_composition_test.shs |
| 1 | test/01_unit/runtime/simple_core_argv_owner_production_link_test.shs |
| 1 | test/01_unit/scripts/admit_simpleos_arm64_server_compiler_contract_test.shs |
| 1 | test/01_unit/scripts/aot_lane_fences_bootstrap_receipt_contract_test.shs |
| 1 | test/01_unit/scripts/aspect_pack_cardinality_contract_test.shs |
| 1 | test/01_unit/scripts/binary_size_go_parity_producer_test.shs |
| 1 | test/01_unit/scripts/bootstrap_authority_target_revalidation_sequence_contract_test.shs |
| 127 | test/01_unit/scripts/bootstrap_authority_target_toctou_contract_test.shs |
| 2 | test/01_unit/scripts/bootstrap_cache_refresh_path_test.shs |
| 1 | test/01_unit/scripts/bootstrap_compile_context_authority_contract_test.shs |
| 1 | test/01_unit/scripts/bootstrap_compiler_inventory_discovery_test.shs |
| 1 | test/01_unit/scripts/bootstrap_compiler_unit_execution_count_test.shs |
| 1 | test/01_unit/scripts/bootstrap_evidence_retention_contract_test.shs |
| 1 | test/01_unit/scripts/bootstrap_frozen_plugin_scope_contract_test.shs |
| 127 | test/01_unit/scripts/bootstrap_module_documentation_classification_test.shs |
| 1 | test/01_unit/scripts/bootstrap_phase1_current_authority_test.shs |
| 1 | test/01_unit/scripts/bootstrap_phase1_tool_containment_test.shs |
| 1 | test/01_unit/scripts/bootstrap_phase2_portable_loader_contract_test.shs |
| 1 | test/01_unit/scripts/bootstrap_release_cache_vector_test.shs |
| 2 | test/01_unit/scripts/bootstrap_sanity_session_scrub_test.shs |
| 2 | test/01_unit/scripts/bootstrap_session_contract_test.shs |
| 1 | test/01_unit/scripts/bootstrap_stage2_positional_stage3_route_contract_test.shs |
| 1 | test/01_unit/scripts/bootstrap_stage2_sanity_output_preflight_contract_test.shs |
| 1 | test/01_unit/scripts/bootstrap_stage2_struct_receiver_gate_test.shs |
| 1 | test/01_unit/scripts/bootstrap_stage3_atomic_generation_publication_test.shs |
| 1 | test/01_unit/scripts/bootstrap_stage3_frontend_cache_off_parity_contract_test.shs |
| 1 | test/01_unit/scripts/bootstrap_stage3_full_src_snapshot_test.shs |
| 70 | test/01_unit/scripts/bootstrap_stage3_helper_capsule_callers_test.shs |
| 1 | test/01_unit/scripts/bootstrap_stage3_manifest_focused_route_contract_test.shs |
| 1 | test/01_unit/scripts/bootstrap_stage3_mode1_admission_contract_test.shs |
| 1 | test/01_unit/scripts/bootstrap_stage3_os_source_snapshot_test.shs |
| 1 | test/01_unit/scripts/bootstrap_stage3_plugin_source_snapshot_test.shs |
| 1 | test/01_unit/scripts/bootstrap_stage3_resume_snapshot_binding_contract_test.shs |
| 1 | test/01_unit/scripts/bootstrap_stage3_resume_source_lineage_contract_test.shs |
| 1 | test/01_unit/scripts/bootstrap_stage3_runtime_policy_source_snapshot_test.shs |
| 1 | test/01_unit/scripts/bootstrap_stage3_snapshot_path_contract_test.shs |
| 1 | test/01_unit/scripts/bootstrap_stage3_unicode_git_state_test.shs |
| 1 | test/01_unit/scripts/bootstrap_stage4_atomic_local_deploy_test.shs |
| 1 | test/01_unit/scripts/bootstrap_stop_after_stage2_contract_test.shs |
| 1 | test/01_unit/scripts/bootstrap_stop_after_stage3_contract_test.shs |
| 1 | test/01_unit/scripts/bootstrap_strategy_fallback_contract_test.shs |
| 1 | test/01_unit/scripts/bootstrap_whole_build_two_worker_floor_test.shs |
| 77 | test/01_unit/scripts/bootstrap_windows_cl_mode_test.shs |
| 2 | test/01_unit/scripts/bootstrap_windows_native_metadata_owner_test.shs |
| 2 | test/01_unit/scripts/bootstrap_windows_output_root_preflight_test.shs |
| 1 | test/01_unit/scripts/bootstrap_windows_startup_owner_test.shs |
| 1 | test/01_unit/scripts/check/cert/freeze_tool_qual_default_path_contract_test.shs |
| 1 | test/01_unit/scripts/check/cert/fuzz_diff_default_path_contract_test.shs |
| 1 | test/01_unit/scripts/check/cert/soundness_diff_default_path_contract_test.shs |
| 1 | test/01_unit/scripts/check/cert/stress_suite_default_path_contract_test.shs |
| 1 | test/01_unit/scripts/check/cert/tool_qual_corpus_default_path_contract_test.shs |
| 1 | test/01_unit/scripts/check/cert/tool_qual_meta_default_path_contract_test.shs |
| 1 | test/01_unit/scripts/check_no_sabotage_residue_contract_test.shs |
| 2 | test/01_unit/scripts/checker_performance_harness_test.shs |
| 127 | test/01_unit/scripts/cli_compileoptions_layer_boundary_test.shs |
| 127 | test/01_unit/scripts/compiler_interpreter_loader_layering_mutation_test.shs |
| 1 | test/01_unit/scripts/completeness_contract_lock_gate_test.shs |
| 1 | test/01_unit/scripts/core_c_capsule_failure_retention_test.shs |
| 1 | test/01_unit/scripts/critical_release_seal_gate_test.shs |
| 1 | test/01_unit/scripts/db_perf_compare_admission_contract_test.shs |
| 1 | test/01_unit/scripts/db_server_request_port_evidence_test.shs |
| 1 | test/01_unit/scripts/demand_driven_smf_evidence_contract_test.shs |
| 1 | test/01_unit/scripts/dynsmf_facet_ref_count_contract_test.shs |
| 1 | test/01_unit/scripts/engine2d_rendering_probe_source_contract_test.shs |
| 127 | test/01_unit/scripts/gdb_inferior_strict_gate_test.shs |
| 1 | test/01_unit/scripts/io_parity_mirror_contract_test.shs |
| 2 | test/01_unit/scripts/macos_process_live_native_test.shs |
| 2 | test/01_unit/scripts/mci_v2_lane_signer_contract_test.shs |
| 1 | test/01_unit/scripts/mir_enum_discriminant_owner_contract_test.shs |
| 1 | test/01_unit/scripts/native_smoke_matrix_progress_contract_test.shs |
| 1 | test/01_unit/scripts/no_refresh_file_lock_test.shs |
| 1 | test/01_unit/scripts/pane_launcher_lifetime_test.shs |
| 1 | test/01_unit/scripts/performance_target_identity_external_test.shs |
| 1 | test/01_unit/scripts/phase2_capsule_schema_layout_contract_test.shs |
| 1 | test/01_unit/scripts/portable_session_exec_contract_test.shs |
| 127 | test/01_unit/scripts/pr_approve_workflow_contract_test.shs |
| 1 | test/01_unit/scripts/process_tree_rss_absolute_limit_test.shs |
| 1 | test/01_unit/scripts/process_tree_rss_watchdog_test.shs |
| 1 | test/01_unit/scripts/rt_unsafe_priority_contract_test.shs |
| 1 | test/01_unit/scripts/runtime_process_owned_linux_random_guard_test.shs |
| 1 | test/01_unit/scripts/sffi_v2_authority_gate_test.shs |
| 1 | test/01_unit/scripts/simple_runtime_provenance_selection_test.shs |
| 1 | test/01_unit/scripts/stage2_parent_receipt_producer_test.shs |
| 1 | test/01_unit/scripts/test_daemon_environment_identity_wiring_test.shs |
| 1 | test/01_unit/tools/mail_cli/account_secret_argv_release_test.shs |
| 1 | test/02_integration/bootstrap_stage3_git_path_bytes_test.shs |
| 1 | test/02_integration/bootstrap_stage3_git_state_paths_test.shs |
| 1 | test/02_integration/bootstrap_stage3_git_state_test.shs |
| 127 | test/02_integration/bootstrap_stage3_retry_preflight_order_test.shs |
| 1 | test/02_integration/compiler/demand_dirty_mixed_scc_publication_contract_test.shs |
| 2 | test/02_integration/compiler/raw_rt_lint_cli_fix_test.shs |
| 1 | test/02_integration/simple_release_wrapper_platform_probe_test.shs |
| 1 | test/02_integration/stage4_diagnostic_two_phase_test.shs |
| 1 | test/02_integration/tool/renderdoc_exporter_contract_test.shs |
| 1 | test/03_system/app/spipe/feature/spipe_local_knowledge_setup_contract_test.shs |
| 2 | test/04_smoke/native_parent_parse_closure_scope_test.shs |
| 1 | test/05_perf/profile_scripts/cross_language_compiler_provenance_contract_test.shs |
| 1 | test/05_perf/profile_scripts/gui_perf_bench_terminal_receipt_contract_test.shs |
| 1 | test/05_perf/profile_scripts/mcdc_k3_dynload_eligibility_contract_test.shs |
| 1 | test/05_perf/startup/dbfs_file_meta_cache_cardinality_contract_test.shs |
| 1 | test/05_perf/startup/decorators_cache_cardinality_contract_test.shs |
| 1 | test/05_perf/startup/duplicate_cache_stats_key_snapshot_contract_test.shs |
| 1 | test/05_perf/startup/dynsmf_trusted_facet_index_contract_test.shs |

Exit 1/2 = assertion or usage failure, 127 = missing tool (jq etc.), 70/77 = other. Wired in batches of 53: PR for batch 1 lists its rows in must_check_gates.sdn as push-unwired-*.
- Batch 01 wired: 53 rows (push-unwired-*).
- Batch 02 wired: 53 rows (push-unwired-*).

## Triage of the 126 failures (2026-11-26, second WSL ubuntu-p2 run, 8 parallel)
Re-run with `build/` and `scratch/` pre-created: 4 green, 122 still fail.
- Green and wired (advisory `push-unwired-bootstrap-*`): `bootstrap_phase1_current_authority`,
  `bootstrap_phase1_tool_containment` (class 1: test assumed `build/native_probe` exists;
  now `mkdir -p`), `bootstrap_stage3_snapshot_path_contract`, `bootstrap_strategy_fallback_contract`
  (first-run failure was load/timeout noise).
- Class 1 environmental, not wired (about 29): 8 exit 127 (rg, jq, gdb, helper functions not on
  PATH), 7 `set -o pipefail` bash-only scripts (green only under bash), and tests needing a
  binary/arguments (`arch_check_fast_help`, `stdio_runtime_owner`, `conditional_empty_symbol_keys_native`,
  `native_parent_parse_closure_scope`, `checker_performance_harness`, `raw_rt_lint_cli_fix`,
  `simple_release_wrapper_platform_probe`), Windows/macOS-only tests, and the read-only `/tmp` test
  `memory_snapshot_sink_contract`.
- Classes 2/3 not yet triaged (about 93): assertion failures where a source-contract test greps
  for text the target no longer contains (for example `entry_closure_app_doc_source_contract`,
  `dynsmf_facet_ref_count_contract`, `aspect_pack_cardinality_contract`). Each needs a
  `git log` check on its target to decide stale test (update) versus real bug (fix + bug doc).

## Batch 2 (2026-11-27): 5 wired, findings on the rest
Wired (advisory `push-unwired-*`), each checked with `git log` on its target:
- `aspect_pack_cardinality_contract` - class 3, real bug in source (host-offer setter
  rematerialized keys); fixed, bug doc `aspect_pack_host_offer_rematerializes_binding_keys_2026-11-27.md`.
- `dynsmf_facet_ref_count_contract` - class 2, test pinned a `retained_count` recount; source keeps the
  counter by increment/decrement, which is the same contract.
- `binary_size_go_parity_producer` - class 2, checker's mutation id is `machine-id-mismatch`.
- `process_tree_rss_absolute_limit`, `process_tree_rss_watchdog` - class 2, the watchdog ceiling was
  deliberately widened eight times (now 58720256 KiB, per-job 1 GiB, wrapper message reworded); the
  limit test now reads the ceiling from the watchdog instead of copying it.
Checked and left (not green, need an owner call or a larger rewrite):
- `no_refresh_file_lock`: real violation, 5 file-lock sites in `src/lib/scv/compile_snapshot_retention_v1.spl`
  (lockless-by-default policy needs a fix or a documented exception).
- `bootstrap_compile_context_authority_contract`: source still transports `(ctx, bool)` tuples; the
  bool-only refactor the test pins was not kept (owner decision: restore it or retire the test).
- `db_server_request_port_evidence`: checker was redesigned (`--source-closure`, `--build-origin`),
  test needs rewriting against the new interface.
- `bootstrap_stop_after_stage2_contract`: help wording changed (stale) and the script hardcodes `/tmp`,
  but it then fails further on `incompatible invocation did not explain rejection`.
- `runtime_memory_owner_composition`: `core_array.spl` no longer carries the documented
  "retain the whole bounded scope" contract.

## Batch 3 (2026-11-27): 3 wired, 4 checked and left
Wired: `dbfs_file_meta_cache_cardinality`, `decorators_cache_cardinality`,
`duplicate_cache_stats_key_snapshot` (class 3, real source fixes, see
`cache_stats_materialize_dict_keys_2026-11-27.md`).
Left, tests ahead of the script (feature never implemented; git history shows no version of the script
ever carried the pinned behaviour):
- `check_no_sabotage_residue_contract`: test expects `PASS - N tracked source file(s) scanned, M marker
  candidate file(s)` verdicts and a primary/worktree split; the guard only reports ERROR when no marker
  file exists (a marker-free tree is "nothing checked").
- `native_smoke_matrix_progress_contract`: expects `NATIVE_SMOKE_BUILD_TIMEOUT` and a
  `[case] START build_deadline=Ns` receipt; `scripts/check/native-smoke-matrix.shs` has neither.
- `phase2_capsule_schema_layout_contract`: `phase2-runtime-capsule.shs verify` rejects the canonical POSIX
  v1 capsule built by the test (identity fixture vs current schema), needs an owner read.
- `performance_target_identity_external`: importer reason for retained build-origin placeholders differs
  (not investigated further).

## Batch 4 (2026-11-27): 7 wired
Six `check/cert/*default_path_contract` (class 3, see
`cert_scripts_hardcoded_author_home_simple_bin_2026-11-27.md`) and `dynsmf_trusted_facet_index_contract`
(class 2: the owner keeps `_trusted_facet_bindings` as the index; the old `_trusted_facet_indices` field was
folded into it, the no-rescan contract still holds). Fresh serial re-run on origin: 13 green of 126 now
(10 earlier-wired plus `bootstrap_stop_after_stage3_contract`, which started passing on its own).
