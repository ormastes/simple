# Phase-2 bug-ledger verify pass — 2026-09-18

Full-tree verification of every `open` row in the `bugs` table of
`doc/08_tracking/bug/bug_db.sdn` at origin/main, per the restart-plan
procedure (`doc/03_plan/infra/audit/tracking_db_triage_restart_2026-09-13.md`).

## Census

- 496 open rows exported, 496 verdicts, coverage check: 0 missing, 0 duplicate, 0 extra.
- Verify: 20 parallel agents, 25 rows each, read-only against origin/main
  (record + cited code; verdicts `fixed | close_stale | close_invalid | still_open`).
- Review: 2 independent reviewers re-checked every non-still_open verdict;
  6 downgraded (weak or contradicted evidence — see below).

## Outcome (applied in this commit)

- 29 rows -> `fixed`, 1 row -> `closed` (close_stale), updated_at 2026-09-18,
  keyed by id, idempotent (rows not `open` were untouched).
- 466 rows remain `open` — each carries fresh liveness evidence in the verify
  verdict files; they are the honest backlog for future fix waves.

## Confirmed closures (reviewer-verified mechanism, not workarounds)

- `asm_template_placeholders_never_bind_2026-08-07`
- `blink_parse_declarations_cross_module_collision_2026-08-11`
- `disk_image_fat32_builder_defects`
- `engine3d_vulkan_world_font_depth_write_disabled_2026-07-13`
- `fat32_database_atomic_replace_recovery_missing_2026-08-14`
- `interpreter_match_on_option_of_enum_fires_no_arm_2026-08-06`
- `iso_use_after_move_invisible_as_call_argument_2026-08-07`
- `naked_struct_pattern_vs_option_always_wildcard_2026-07-29`
- `native_enum_runtime_type_identity_2026-07-19`
- `native_llvm_f64_enum_payload_argpass_2026-07-19`
- `native_multiple_module_initializers_declaration_order_2026-07-19`
- `native_provider_so_routed_to_simpleos_registry_2026-08-14`
- `native_string_relational_operators_compare_raw_handles_2026-07-17`
- `native_text_eq_any_untagged_smallint_deref_2026-07-23`
- `native_to_i64_nil_coalesce_print_tagbox_leak_2026-07-20`
- `private_helper_name_collision_across_modules_has_2026-08-17`
- `proton_wine_fixture_api_redesign_2026-07-20`
- `pure_simple_untyped_list_element_read_unconditional_int_decode_segv_2026-08-08`
- `rawhandle_generational_id_api_drift_2026-07-20`
- `root_cli_provider_activation_requires_process_callable_loader_2026-08-14`
- `rt_cuda_module_load_data_bytes_cstring_rejects_binary_cubin_2026-08-07`
- `rt_enum_discriminant_is_enum_id_blind_name_hash_2026-08-08`
- `runtime_error_stack_absent_on_live_interpreter_2026-08-17`
- `rust_seed_javanew_heuristic_blocks_identifier_named_new_2026-08-10`
- `rv64_dtb_overlay_not_materialized_in_soc_address_map_2026-07-27`
- `simpleos_ssh_qemu_gate_uses_probe_service_not_sshd_2026-06-06`
- `treesitter_real_specs_150_of_151_tautologies_pythontrue_lint_2026-08-06`
- `two_std_specs_reference_nonexistent_api_and_assert_nothing_2026-08-04`
- `untyped_list_param_census_2026-07-29`
- `wasm_cli_emit_no_artifact_2026-05-30`

## Downgraded by review (stay open)

- `app_modules_referenced_by_specs_exist_nowhere_2026-08-04`
- `host_toolchain_seed_pinned_lint_fmt_doccov_unrunnable_2026-07-17`
- `interp_compositor_backend_put_pixel_clones_framebuffer_2026-07-03`
- `interpreter_binding_class_typed_field_snapshots_instead_of_aliasing_2026-08-10`
- `stage3_current_source_hir_rss_termination_2026-08-14`
- `web_showcase_vector_font_evidence_style_budget_truncation_2026-08-01`

Downgrade rationales (review evidence): cited functions orphaned / live
regression re-appeared (app_modules); dispatch pre-existed at filing,
needs self-hosted redeploy (host_toolchain); record says workaround-not-fix
(interp_compositor); blocked spec still RED with exact signature
(interpreter_binding_class); RSS boundedness explicitly unproven, cited
commit is a different defect (rss_termination); resolver proven but the
budget-truncation fix never landed (vector_font).
