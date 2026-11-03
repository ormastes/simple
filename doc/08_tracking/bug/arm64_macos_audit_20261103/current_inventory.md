# Current ARM64/macOS bug inventory — 2026-11-03

Snapshot base `15dd3173e19c621396a8a4f0ba817bcc88e460b9` plus this reviewed reconciliation. 73 unique tracked records: 12 closed, 11 fix-implemented-verification-pending, 18 fixed, 2 fixing, 30 open. This is the initial 71-record platform-term inventory plus two newly diagnosed compiler defects; not 73 reproduced native failures. Windows-only historical context is excluded from platform defect totals; Linux Metal emulation is a capability request. Shared language staging and deployment dependencies remain labeled. Historical fixed/closed records are not newly qualified.

Firmware PR [6384](https://github.com/ormastes/simple/pull/6384) merged; real firmware boot remains pending. Registry checkpoint PR [6385](https://github.com/ormastes/simple/pull/6385) merged. The float rejection candidate `f93c5e7dca4` remains unlanded and unexecuted without an admitted full CLI. Seed suffix fix has a native 5-check post-fix pass but rebuilt Phase2 sanity remains pending; its record stays fixing.

Eight historical acceptance followups live in `native_acceptance_followups.sdn`; these do not rewrite closed status or assert recurrence. Only ARM64 PCI/ivshmem was reopened for independently confirmed current source wiring defects.

| Priority | Status | Context/scope | ID |
|---|---|---|---|
| P0 | fix-implemented-verification-pending | ARM64: platform/shared context; native acceptance not inferred | `arm64_framebuffer_color_struct_return_abi_2026-08-21` |
| P0 | fixed | macOS: platform/shared context; native acceptance not inferred | `bootstrap_capsule_permission_scan_failure_admitted_2026-09-21` |
| P0 | fixed | macOS: platform/shared context; native acceptance not inferred | `capsule_immutability_check_fail_open_gnu_find_perm_2026-08-30` |
| P0 | fixed | macOS: platform/shared context; native acceptance not inferred | `macos_bootstrap_lane_platform_defect_cluster_2026-08-30` |
| P0 | fixed | macOS: platform/shared context; native acceptance not inferred | `macos_seed_unbuildable_metal_module_ungated_2026-08-30` |
| P0 | fix-implemented-verification-pending | macOS: shared dependency; not platform-exclusive | `stage3_current_source_hir_rss_termination_2026_08_14` |
| P0 | fix-implemented-verification-pending | macOS, ARM64: platform/shared context; native acceptance not inferred | `stage3_macos_full_graph_hir_sigsegv_2026_09_21` |
| P1 | fixed | macOS: platform/shared context; native acceptance not inferred | `bootstrap_preflight_hardcodes_linux_mnt_data_cargo_dir_2026-08-30` |
| P1 | fixed | macOS: platform/shared context; native acceptance not inferred | `bootstrap_progress_monitor_reports_live_run_as_dead_2026-09-03` |
| P1 | fix-implemented-verification-pending | macOS: platform/shared context; native acceptance not inferred | `macos_bootstrap_capsule_duplicate_native_all_exports_2026_10_12` |
| P1 | fixed | macOS: platform/shared context; native acceptance not inferred | `macos_ctx_hook_gnu_sed_alternation_denies_all_bash_2026-08-30` |
| P1 | fixed | macOS: platform/shared context; native acceptance not inferred | `macos_live_process_stdbuf_required_2026-09-21` |
| P1 | fixed | macOS: platform/shared context; native acceptance not inferred | `macos_live_process_tmpdir_shell_quoting_2026-09-21` |
| P1 | fixed | macOS: platform/shared context; native acceptance not inferred | `macos_seed_st_mtimespec_absent_from_libc_e0609_2026-08-30` |
| P1 | fixed | macOS: platform/shared context; native acceptance not inferred | `macos_seed_variadic_open_mode_t_u16_e0617_2026-08-30` |
| P1 | closed | ARM64: platform/shared context; native acceptance not inferred | `object_format_from_host_not_target_2026_10_26` |
| P1 | fixed | macOS: platform/shared context; native acceptance not inferred | `process_group_setsid_absent_on_macos_2026-08-30` |
| P1 | fix-implemented-verification-pending | ARM64: shared dependency; not platform-exclusive | `rv64_web_gate_arm64_import_leak_and_storage_2026-06-15` |
| P1 | fix-implemented-verification-pending | macOS: platform/shared context; native acceptance not inferred | `test_runner_ulimit_caps_unusable_on_macos_2026-09-05` |
| P1 | fixed | macOS: platform/shared context; native acceptance not inferred | `weak_symbol_detection_elf_only_nm_kinds_macho_2026-08-30` |
| P1 | fixed | macOS: exclude: Windows defect; Mac appears only as deployment context | `windows_build_subcommand_silent_noop_stale_binary_2026-08-05` |
| P2 | fixed | ARM64: platform/shared context; native acceptance not inferred | `aarch64_real_firmware_boot_gap_and_seed_defects_2026-07-14` |
| P2 | fix-implemented-verification-pending | ARM64: platform/shared context; native acceptance not inferred | `app_launchers_no_admitted_runtime_aarch64_linux_2026_10_19` |
| P2 | fix-implemented-verification-pending | ARM64: platform/shared context; native acceptance not inferred | `arm64_efi_real_firmware_lane_unreproducible_and_unified_lane_uses_kernel_2026-08-11` |
| P2 | open | ARM64: platform/shared context; native acceptance not inferred | `arm64_qemu_ivshmem_preboot_2026-07-12` |
| P2 | open | ARM64: platform/shared context; native acceptance not inferred | `arm64_simpleos_virtio_blk_durable_write_gap_2026-08-14` |
| P2 | open | macOS: shared dependency; not platform-exclusive | `char_condition_type_check_staged_2026-11-03` |
| P2 | open | macOS: shared dependency; not platform-exclusive | `char_literal_lexer_switch_staged_2026-11-03` |
| P2 | open | ARM64: platform/shared context; native acceptance not inferred | `comment_cheat_absent_capabilities_2026-08-10` |
| P2 | fix-implemented-verification-pending | macOS: platform/shared context; native acceptance not inferred | `gpu_ffi_loader_probes_linux_sonames_on_macos_2026_09_19` |
| P2 | open | macOS: platform/shared context; native acceptance not inferred | `gui_winit_window_not_registered_window_server_2026-07-06` |
| P2 | fixed | macOS: platform/shared context; native acceptance not inferred | `hermetic_m5_evidence_blocks_runner_checkout_2026_11_03` |
| P2 | closed | macOS: platform/shared context; native acceptance not inferred | `interp_option_struct_semantics_macos_parity_2026-07-25` |
| P2 | fixed | macOS: shared dependency; not platform-exclusive | `llm-caret-tui-extern-gaps` |
| P2 | closed | macOS: platform/shared context; native acceptance not inferred | `macos_bootstrap_copy_mem_provider_gap_2026-07-17` |
| P2 | closed | macOS: platform/shared context; native acceptance not inferred | `macos_stage4_full_cli_low_memory_runaway_2026-07-17` |
| P2 | open | macOS: platform/shared context; native acceptance not inferred | `macos_vulkan_2d_vector_font_empty_batch_native_fault_2026-07-26` |
| P2 | closed | macOS: platform/shared context; native acceptance not inferred | `macos_vulkan_native_entry_blockers_2026-07-24` |
| P2 | closed | macOS: platform/shared context; native acceptance not inferred | `macos_vulkan_provider_availability_live_2026-07-26` |
| P2 | fixed | ARM64: platform/shared context; native acceptance not inferred | `pristine_seed_cargo_build_broken_blocks_virtio_arm64_repro_2026-08-11` |
| P2 | open | ARM64: platform/shared context; native acceptance not inferred | `simpleos_arm64_el0_server_syscall_and_virtio_net_gap_2026-08-14` |
| P2 | open | macOS: platform/shared context; native acceptance not inferred | `wm_metal_glass_multi_receipt_opacity_2026-07-27` |
| P3 | open | ARM64: platform/shared context; native acceptance not inferred | `arm64_attested_build_rejects_rust_seed_by_design_2026-09-01` |
| P3 | open | ARM64: platform/shared context; native acceptance not inferred | `arm64_desktop_engine2d_media_chain_blockers_2026-09-01` |
| P3 | open | ARM64: platform/shared context; native acceptance not inferred | `arm64_desktop_engine2d_seed_codegen_dbd_unresolved_global_2026-09-01` |
| P3 | open | ARM64: platform/shared context; native acceptance not inferred | `arm64_wm_vulkan_real_firmware_lane_blocked_2026-09-01` |
| P3 | open | ARM64: platform/shared context; native acceptance not inferred | `bin_simple_is_seed_aarch64_stage3_blocked_2026-09-04` |
| P3 | open | ARM64: platform/shared context; native acceptance not inferred | `board_vulkan_cross_arch_boundary_only_x86_64_proven_2026-08-11` |
| P3 | open | macOS: platform/shared context; native acceptance not inferred | `bootstrap_macos_blocked_seed_compile_and_linux_only_stage3_authority_2026-09-06` |
| P3 | fix-implemented-verification-pending | ARM64: platform/shared context; native acceptance not inferred | `cargo_test_lib_does_not_compile_on_aarch64_2026-09-13` |
| P3 | open | macOS: platform/shared context; native acceptance not inferred | `crash_handler_and_fork_bridge_absent_from_seed_macos_2026-09-06` |
| P3 | closed | macOS: platform/shared context; native acceptance not inferred | `engine2d_metal_gpu_only_clip_unimplemented_2026-07-06` |
| P3 | closed | macOS, ARM64: platform/shared context; native acceptance not inferred | `gui_smf_dynlib_hot_call_runtime_missing_2026-06-01` |
| P3 | closed | ARM64: platform/shared context; native acceptance not inferred | `lld_defsym_symbol_argv_quoting_2026-07-12` |
| P3 | open | macOS, ARM64: platform/shared context; native acceptance not inferred | `macos_full_cli_gui_admission_process_proof_2026-07-27` |
| P3 | fix-implemented-verification-pending | macOS, ARM64: platform/shared context; native acceptance not inferred | `macos_native_lane_freetype_missing_rust_bootstrap_multiplatform_2026-09-01` |
| P3 | open | macOS: platform/shared context; native acceptance not inferred | `macos_test_runner_blocked_inline_unsafe_and_wrong_deploy_slot_2026-08-31` |
| P3 | closed | macOS: platform/shared context; native acceptance not inferred | `macos_vulkan_host_wm_live_evidence_cpu_mirror_and_input_gap_2026-07-26` |
| P3 | open | macOS: platform/shared context; native acceptance not inferred | `main_test_runnable_unsatisfiable_on_macos_2026-09-03` |
| P3 | open | macOS: capability request: Linux Metal emulation | `metal_backend_no_linux_emulation_lane_2026-08-19` |
| P3 | open | macOS, ARM64: platform/shared context; native acceptance not inferred | `phase2_native_build_hello_world_invalid_heap_and_scorer_segv_2026-09-05` |
| P3 | open | ARM64: platform/shared context; native acceptance not inferred | `phase2_stage2_native_build_len_on_i64_aarch64_linux_2026-09-13` |
| P3 | closed | ARM64: shared dependency; not platform-exclusive | `rv64_host_gpu_real_runtime_exit_facade_2026-07-12` |
| P3 | open | ARM64: platform/shared context; native acceptance not inferred | `simpleos_arm64_qmp_input_transport_missing_2026-07-24` |
| P3 | closed | ARM64: platform/shared context; native acceptance not inferred | `simpleos_arm64_riscv64_embedded_gui_missing_theme_install_call_2026-09-06` |
| P3 | open | macOS: platform/shared context; native acceptance not inferred | `spipe_docgen_deployed_macos_cli_stale_2026-09-09` |
| P3 | open | macOS, ARM64: platform/shared context; native acceptance not inferred | `stage2_link_undefined_cpu_probe_and_surface_symbols_2026-09-13` |
| P3 | open | ARM64: platform/shared context; native acceptance not inferred | `stage2_native_codegen_silent_wrong_values_aarch64_2026-09-05` |
| P3 | open | ARM64: platform/shared context; native acceptance not inferred | `stage2_native_f64_arithmetic_lowered_as_integer_ops_aarch64_2026-09-05` |
| P3 | open | macOS, ARM64: platform/shared context; native acceptance not inferred | `stage3_hard_blocked_on_stage2_admission_2026-08-31` |
| P3 | open | macOS, ARM64: platform/shared context; native acceptance not inferred | `stage3_selfhost_zerokind_compile_specialized_template_release_macos_2026-09-05` |
| P0 | fixing | ARM64: shared seed resolver; ARM64 Linux observed, macOS not reproduced | `seed_native_numeric_conversion_suffix_rebinds_private_reader_2026-11-03` |
| P2 | fixing | ARM64: direct native backend; separate from historical LLVM failure | `native_aarch64_scalar_float_silent_integer_lowering_2026_11_03` |
