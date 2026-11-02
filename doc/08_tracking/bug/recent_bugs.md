# Recent Bugs

**Generated:** 2026-11-01
**Database:** `doc/08_tracking/bug/bug_db.sdn`
**Open:** 745 | **Closed:** 866

## Open Bugs

| ID | Severity | Status | Title | File |
|----|----------|--------|-------|------|
| jira_search_ignores_next_page_token_2026-10-31 | P1 | open | Jira Data Center search ignores startAt paging; Cloud is fixed | `doc/08_tracking/bug/jira_search_ignores_next_page_token_2026-10-31.md:1` |
| tcp_accept_timeout_nonblocking_stream_windows_2026-10-31 | P2 | open | TCP accept with timeout returns a non-blocking stream on Windows | `doc/08_tracking/bug/tcp_accept_timeout_nonblocking_stream_windows_2026-10-31.md:1` |
| os_crypto_native_failures_2026_10_31 | P1 | open | OS crypto AES-128 GCM and X25519 fail natively and AES-256 GCM cannot link | `doc/08_tracking/bug/os_crypto_native_failures_2026_10_31.md:1` |
| seed_module_name_shadows_match_binding_2026_10_31 | P2 | open | Seed lets a module name shadow a match binding called value | `doc/08_tracking/bug/seed_module_name_shadows_match_binding_2026_10_31.md:1` |
| native_pattern_payload_text_interpolation_2026_10_31 | P2 | open | Native enum text payload interpolates as a raw integer | `doc/08_tracking/bug/native_pattern_payload_text_interpolation_2026_10_31.md:1` |
| devhub_spec_windows_shim_not_executed_2026_10_31 | P2 | open | Windows seed cannot launch extensionless fake CLIs | `doc/08_tracking/bug/devhub_spec_windows_shim_not_executed_2026_10_31.md:1` |
| eprint-noparen-stage2-20261031 | P1 | open | Pinned stage2 rejects no-paren eprint expressions | `src/app/cli/bootstrap_main.spl:427` |
| native_to_i64_compound_receiver_2026_10_31 | P0 | open | Native to_i64 returns 0 on a compound or unproven receiver | `doc/08_tracking/bug/native_to_i64_compound_receiver_2026_10_31.md:1` |
| env_get_cocompiled_signature_collision_2026_10_31 | P1 | open | env_get resolves to the wrong co-compiled definition on the seed | `doc/08_tracking/bug/env_get_cocompiled_signature_collision_2026_10_31.md:1` |
| seed_interpreter_zeroize_not_guaranteed_2026_10_31 | P2 | open | Seed interpreter cannot guarantee zeroization through a parameter | `doc/08_tracking/bug/seed_interpreter_zeroize_not_guaranteed_2026_10_31.md:1` |
| native_tuple_array_local_text_provenance_2026-10-30 | P2 | open | Implicit text locals from tuple-array elements lose native text representation | `src/lib/nogc_sync_mut/http/url.spl:51` |
| mono_preflight_schema_pin_and_mirror_drift_2026_10_27 | P2 | open | Mono preflight schema pin stale since v9; mirrors drifted (E-MONO-SCHEMA on every call) | `src/compiler/40.mono/mono_invocation_preflight_v1.spl:53` |
| hir_shard_worker_alloc_failure_2026_10_27 | P0 | open | HIR shard workers die in alloc abort: warmup admits 8 at static 6 GB, real peak 11 GB exhausts commit | `src/app/cli/shard_mem_clamp.spl:307` |
| strict-field-forwarding-opt-in-20261027 | P2 | open | src-compiler-has-undefined-field-reads (strict field forwarding opt-in) | `src/compiler/20.hir/hir_lowering/_Expressions/accessor_forwarding.spl:13` |
| match_unqualified_imported_enum_variant_default_arms_2026-10-24 | P2 | open | match bare payload variants lowered as binding default arms | `src/plugins/backend_vhdl/vhdl_backend.spl:346` |
| gpu_type_mapper_struct_symbolid_layout_2026-10-24 | P2 | open | GPU type mapper struct symbol id layout | `src/plugins/backend_cuda/cuda_type_mapper.spl:200` |
| mir_unresolved_method_inferred_receiver_2026-10-24 | P2 | open | MIR unresolved method on inferred receiver type | `src/compiler/10.frontend/core/aop_debug_log.spl:114` |
| for_in_dict_values_i64_2026-10-24 | P2 | open | for-in over Dict.values() lowers with I64 collection type | `src/plugins/backend_vhdl/vhdl/vhdl_call_lowering.spl:305` |
| match_nil_subpattern_requires_declared_optional_slot_2026-10-24 | P2 | open | match nil sub-pattern requires declared optional slot | `src/plugins/backend_lean/lean_mir_translate.spl:94` |
| trait_default_inherent_override_duplicate_symbol_2026-10-24 | P2 | open | trait default inherent override emits duplicate symbol | `src/compiler/70.backend/backend/cranelift_type_mapper.spl:83` |
| match_array_literal_patterns_multiple_wildcard_arms_2026-10-24 | P2 | open | array literal case patterns lowered as wildcard arms | `src/plugins/backend_vulkan/vulkan/spirv_builder.spl:47` |
| array_eq_lowered_as_identity_compare_2026-10-25 | P2 | open | array eq lowered as identity compare (workaround registered) | `src/app/cli/native_build_parse_closure_owner.spl:30` |
| optional_text_unwrap_truncates_at_nul_2026-10-25 | P2 | open | optional text unwrap truncates at nul (workaround registered) | `src/app/compiler_entrypoint/inventory_scratch.spl:35` |
| ssa_write_count_quadratic_scan_2026_10_25 | P2 | open | ssa write count quadratic scan (workaround registered) | `src/app/io/_CliCompile/compile_targets.spl:736` |
| match_expr_panic_first_arm_drops_result_2026-10-25 | P2 | open | match expr panic first arm drops result (workaround registered) | `src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl:1522` |
| stage2_mir_shard_flat_pool_text_len_minus1_2026_10_22 | P2 | open | stage2 mir shard flat pool text len minus1 (workaround registered) | `src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl:1594` |
| module_static_unresolved_initializer_2026-10-24 | P2 | open | module static unresolved initializer (workaround registered) | `src/compiler/10.frontend/core/parser.spl:161` |
| match_variant_pattern_shadowed_by_struct_name_2026-10-24 | P2 | open | match variant pattern shadowed by struct name (workaround registered) | `src/compiler/10.frontend/desugar/poll_generator.spl:187` |
| stage2_sanity_module_path_naming_probe_segv_2026_10_22 | P2 | open | stage2 sanity module path naming probe segv (workaround registered) | `src/compiler/10.frontend/frontend_parse_cache.spl:93` |
| phase3_result_local_match_owner_2026_10_26 | P2 | open | phase3 result local match owner (workaround registered) | `src/compiler/20.hir/hir_codec_support.spl:540` |
| optional_struct_stored_into_desugared_field_keeps_option_box_2026-10-25 | P2 | open | optional struct stored into desugared field keeps option box (workaround registered) | `src/compiler/20.hir/hir_lowering/_Items/class_declaration_lowering.spl:193` |
| untyped_val_if_expr_struct_boxed_as_int_dict_key_2026-10-25 | P2 | open | untyped val if expr struct boxed as int dict key (workaround registered) | `src/compiler/20.hir/hir_lowering/_Items/module_build.spl:575` |
| enum_payload_type_mismatch_dict_elem_untyped_2026-10-24 | P2 | open | enum payload type mismatch dict elem untyped (workaround registered) | `src/compiler/25.traits/trait_solver.spl:570` |
| enum_payload_type_mismatch_tuple_pattern_binders_2026-10-24 | P2 | open | enum payload type mismatch tuple pattern binders (workaround registered) | `src/compiler/30.types/type_infer/inference_control.spl:78` |
| enum_payload_type_mismatch_untyped_match_value_2026-10-24 | P2 | open | enum payload type mismatch untyped match value (workaround registered) | `src/compiler/30.types/type_infer/inference_expr_calls.spl:27` |
| enum_payload_type_mismatch_untyped_map_2026-10-24 | P2 | open | enum payload type mismatch untyped map (workaround registered) | `src/compiler/30.types/type_infer/traits.spl:110` |
| enum_payload_type_mismatch_untyped_option_match_2026-10-24 | P2 | open | enum payload type mismatch untyped option match (workaround registered) | `src/compiler/35.semantics/resolve.spl:687` |
| native_optional_payload_owner_dispatch_2026_10_26 | P2 | open | native optional payload owner dispatch (workaround registered) | `src/compiler/40.mono/monomorphize/hir_subst/body_subst.spl:357` |
| optional_field_read_after_nil_check_reads_option_box_2026-10-25 | P2 | open | optional field read after nil check reads option box (workaround registered) | `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:670` |
| mir_aggregate_trace_array_receiver_2026_10_25 | P2 | open | mir aggregate trace array receiver (workaround registered) | `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl:49` |
| enum_payload_type_mismatch_unresolved_try_2026-10-24 | P2 | open | enum payload type mismatch unresolved try (workaround registered) | `src/compiler/70.backend/backend/interpreter.spl:201` |
| llvm_bootstrap_string_cache_scope_escape_2026_10_25 | P2 | open | llvm bootstrap string cache scope escape (workaround registered) | `src/compiler/70.backend/backend/llvm_codegen_adapter.spl:165` |
| if_expression_text_result_erased_to_i64_2026-10-25 | P2 | open | if expression text result erased to i64 (workaround registered) | `src/compiler/70.backend/backend/runtime_compiler.spl:692` |
| result_err_unwrap_unsupported_payload_2026-10-24 | P2 | open | result err unwrap unsupported payload (workaround registered) | `src/compiler/70.backend/backend_plugin/loader.spl:44` |
| bare_result_return_type_any_payload_2026-10-24 | P2 | open | bare result return type any payload (workaround registered) | `src/compiler/70.backend/linker/linker_wrapper_helpers.spl:160` |
| result_struct_payload_pushed_into_struct_array_crashes_2026-10-25 | P2 | open | result struct payload pushed into struct array crashes (workaround registered) | `src/compiler/80.driver/cache/cold_hir_semantic_seed_v1.spl:308` |
| one_element_literal_of_loop_text_boxed_as_int_2026-10-25 | P2 | open | one element literal of loop text boxed as int (workaround registered) | `src/compiler/80.driver/cache/native_interface_slice.spl:247` |
| tldr_future_static_owner_typeparam_2026_10_25 | P2 | open | tldr future static owner typeparam (workaround registered) | `src/compiler/80.driver/cache/reader/tldr_table_v1.spl:62` |
| enum_payload_type_mismatch_optional_text_2026-10-24 | P2 | open | enum payload type mismatch optional text (workaround registered) | `src/compiler/80.driver/driver_aot_codegen_outputs.spl:104` |
| text_method_arg_copied_through_extern_abi_per_call_2026-10-25 | P2 | open | text method arg copied through extern abi per call (workaround registered) | `src/compiler/80.driver/driver_entry_closure_core.spl:631` |
| dict_index_coalesce_text_decoded_before_nil_test_2026-10-25 | P2 | open | dict index coalesce text decoded before nil test (workaround registered) | `src/compiler/80.driver/driver_phase_gates.spl:34` |
| for_in_unresolved_if_match_route_type_2026-10-24 | P2 | open | for in unresolved if match route type (workaround registered) | `src/compiler/80.driver/driver_source_pipeline_loading.spl:441` |
| mir_text_bytes_unresolved_inferred_trim_receiver_2026-10-23 | P2 | open | mir text bytes unresolved inferred trim receiver (workaround registered) | `src/lib/common/sdn/parser.spl:33` |
| hir_generic_enum_self_match_2026-10-23 | P2 | open | hir generic enum self match (workaround registered) | `src/lib/nogc_sync_mut/failsafe/core.spl:132` |
| hir_cache_never_hits_header_rejected_2026_10_26 | P2 | open | HIR cache never hits on repeat build: rejected=header:1, one shared parser-v4.hir overwritten by every target | `src/compiler/80.driver/driver_hir_cache.spl:1` |
| armv7_windows_backend_plugin_target_rejected_2026_10_26 | P2 | open | armv7-w64-mingw32 native-build fails: BACKEND_SESSION_AUTHORITY load rejected: BACKEND_PLUGIN_TARGET | `src/compiler/70.backend/backend_plugin/builtin_adapter.spl:1` |
| object_format_from_host_not_target_2026_10_26 | P1 | open | aarch64-unknown-linux-gnu and x86_64-unknown-simpleos emit COFF instead of ELF: object format derived from host not target triple | `src/compiler/70.backend/backend/llvm_native_link_orchestrator.spl:1` |
| cross_target_link_no_runtime_2026_10_26 | P2 | open | Cross-target link has no runtime/entry: host C runtime/entry compilation unsupported for i686-w64-mingw32 on x86_64-windows | `src/compiler/70.backend/backend/llvm_native_link_orchestrator.spl:1` |
| stage2_exit127_llvm_mingw_path_dll_clash_2026_10_26 | P2 | open | stage2.exe exits 127 silently (0xC0000139 libLLVM-23.dll clash) with llvm-mingw first on PATH or SIMPLE_PROJECT_ROOT set | `src/app/cli/bootstrap_main.spl:1` |
| native_codegen_trait_field_receiver_erased_ambiguous_2026_10_26 | P1 | open | Native codegen erases trait-typed field receiver self.store.read to an ambiguous bare method | `src/compiler/00.common/cache_contract/virtual_source_consumer_v1.spl:39` |
| native_closure_walks_bind_dotted_imports_differently_2026_10_20 | P2 | open | Native closure walks bind imports differently between coordinator and snapshot-root workers | `src/compiler/80.driver/driver_source_pipeline_loading.spl:1060` |
| stage3_closure_loop_rss_growth_after_provider_feed_2026_10_20 | P1 | open | Stage 3 closure loop RSS grows 20-36 MB per module with the provider feed (52 GiB cap nearly exhausted) | `src/compiler/50.mir/_MirLowering/module_lowering.spl:2394` |
| stage3_hir_cache_direct_route_misses_sharded_entries_2026_10_20 | P2 | open | Stage 3 HIR cache: direct route misses every entry the sharded route stored | `src/compiler/80.driver/driver_hir_cache.spl:1` |
| p4p2_flat_parser_noinit_module_var_struct_and_fn_types_2026-10-20 | P2 | open | Self-hosted flat parser synthesizes a zero default only for scalar-element fixed arrays; struct/fn-typed module vars need explicit initializers (@workaround in idt.spl) | `src/os/kernel/interrupts/idt.spl:97` |
| p4p2_cfg_skip_swallows_next_multiline_decl_2026-10-20 | P2 | open | cfg preprocessor counts the next declaration's header bracket before ending a false-@cfg skip, swallowing _map_user_process_image under the deployed producer (@workaround) | `src/os/kernel/scheduler/scheduler_types.spl:400` |
| p4p2_cfg_false_multiline_use_closing_brace_leaks_2026-10-20 | P2 | open | A false @cfg on a multi-line use whose closing brace is alone at column 0 leaks the brace into the parse under the deployed phase-2 producer; gated uses kept single-line (@workaround) | `src/os/kernel/loader/authenticated_fs_exec_submission_service_v1.spl:869` |
| release_stage1_native_build_worker_sigsegv_2026_10_20 | P1 | open | release.yml stage1 native-build worker SIGSEGVs before producing a binary (linux HIR worker, windows immediate); test runner falls back to the bootstrap-only seed (@workaround) | `.github/workflows/release.yml:918` |
| bootstrap_main_closure_pulls_src_os_hir_failures_2026_10_20 | P0 | open | bootstrap_main closure pulls src/os (1316 -> 2280 modules); 21 os modules fail HIR in Stage 3 | `src/lib/common/ui/window_scene_draw_ir.spl:59` |
| stage2_matrix_test_runner_build_no_c_compiler_for_empty_module_object_2026_10_20 | P2 | open | Stage 2 matrix test_runner_build: no C compiler available for empty module object | `src/compiler/80.driver/driver_aot_native_output.spl:4245` |
| stage2_matrix_cg_modules_managed_tool_projection_invalid_2026_10_20 | P2 | open | Stage 2 matrix src/app/_cg modules: managed tool projection role/path/digest invalid | `src/lib/nogc_sync_mut/io/native_tool_authority_v1.spl:93` |
| stage3_hir_cache_reencode_selfcheck_and_low_store_rate_2026_10_19 | P2 | open | Stage 3 HIR cache logs reencode SELFCHECK failures and stores only 25 of 771 lowered modules | `src/compiler/80.driver/driver_hir_cache.spl:1` |
| stage3_bootstrap_closure_lowered_without_providers_2026_10_20 | P1 | open | Stage 3 bootstrap-fixed closure and entry modules lowered with no providers (47,497 MIR errors) | `src/compiler/80.driver/driver_pipeline_lowering.spl:983` |
| stage3_bootstrap_real_llvm_imported_global_undeclared_2026_10_20 | P2 | open | Stage 3 bootstrap real-LLVM entry IR loads imported pub val globals without declaring them | `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl:626` |
| native_build_entry_main_undefined_when_source_path_has_dot_2026_10_20 | P2 | open | native-build of an entry under a dotted directory path links without __simple_main | `scripts/check/check-stage-binaries-runnable.shs:375` |
| stage3_bootstrap_closure_provider_registration_cost_2026_10_20 | P1 | open | Stage 3 bootstrap-fixed closure provider registration costs 12.8 s and RSS +28 MB per module (r8 base) | `src/compiler/50.mir/_MirLowering/module_lowering.spl:2394` |
| test_coverage_wrapper_native_build_refused_by_scv_admission_2026_10_19 | P2 | open | --coverage aborts every spec: wrapper native-build refused by SCV admission | `src/app/compiler_entrypoint/inventory_events.spl:697` |
| bootstrap_frontend_budget_pins_one_hir_worker_2026-10-19 | P2 | open | Bootstrap frontend policy pins SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB=3000000 and tree-rss-policy prices a job at 96 MiB (codegen shard) so the enforced cap sits on the 5.59 GiB floor: the shard clamp admits one HIR worker at any thread count | `scripts/bootstrap/lib/tree-rss-policy.shs:1` |
| hir_shard_worker_repeats_closure_load_sources_2026-10-19 | P2 | open | Each HIR shard worker (simple_bin run native_build_worker.spl, compiled route only under bootstrap_main) re-runs the full native-build front over the whole closure before claiming modules; 8 workers measured 2x the throughput of 1 at 78% CPU and load_sources 15 min vs 5 min with 8 parse shards | `src/app/cli/native_build_worker_entry.spl:53` |
| shard_mem_clamp_ignores_enclosing_cgroup_memory_max_2026-10-19 | P2 | open | Managed Linux worker filters SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB out of the compiler environment and shard_mem_clamp reads no cgroup memory.max, so HIR fanout inside a cgroup-contained build is sized by host MemAvailable | `src/app/cli/shard_mem_clamp.spl:174` |
| mir_shard_worker_budget_16gb_serializes_mir_2026-10-19 | P3 | open | MIR shard worker budget 16000000 kB admits one MIR shard below a 26.7 GB tree budget when SIMPLE_MIR_SHARDING=1; the figure is unmeasured | `src/app/cli/native_build_main.spl:986` |
| parse_shard_warmup_pinned_to_one_worker_2026-10-19 | P3 | open | Product and transcribed lanes pin SIMPLE_PARSE_SHARD_MAX=1 on every host, serializing the parse cache warm-up (interpreter-mode OOM evidence predates the compiled parse shard route) | `scripts/check/lib/bootstrap-stage3/command-snapshot.shs:310` |
| io_facade_exports_undeclared_time_now_unix_micros_2026_10_19 | P2 | open | Native HIR rejects use std.io.{time_now_unix_micros}: io.spl facade exports names it never imports, blocking devhub native-build | `src/lib/nogc_async_mut/io.spl:146` |
| native_parser_nested_quotes_in_interpolation_2026_10_19 | P2 | open | Pure-Simple parser fails on nested string literal inside interpolation ({encoding ?? empty-string}), blocking llm_caret main native-build | `src/lib/gc_async_mut/gpu/browser_engine/net/h1_client.spl:649` |
| native_mir_lambda_and_enum_eq_block_caret_cs_2026_10_19 | P2 | open | Native MIR for llm_caret cs_main: 21 lambdas hit E-MIR-EXPR-Lambda (closure conversion not run), enum == lowered as missing struct __eq__, unresolved close/is_open | `src/lib/nogc_async_mut/io/buffer.spl:130` |
| interp_option_unwrapped_text_starts_with_nil_2026_10_19 | P1 | open | Interpreter returns nil for starts_with/ends_with on text unwrapped from text? (! or ??), breaking storage containment and every MCP caret_* tool | `src/lib/nogc_sync_mut/storage_roots/path_policy.spl:104` |
| devhub_redaction_comma_secret_suffix_leak_2026_10_19 | P2 | open | DevHub diagnostic redaction leaks the suffix of comma-containing quoted secrets and Cookie/Set-Cookie values | `src/app/devhub/redaction.spl:72` |
| devhub_email_contract_drift_2026_10_19 | P2 | open | DevHub email: exit codes, outlook provider mapping, mail-cli inbox path and malformed shared config disagree with their specs | `src/app/devhub/cmd_email.spl:92` |
| app_launchers_no_admitted_runtime_aarch64_linux_2026_10_19 | P2 | open | bin/devhub, bin/caret and 5 sibling launchers never probe bin/release/aarch64-unknown-linux-gnu and reject the seed, so they exit 127 on aarch64 Linux | `bin/devhub:44` |
| llm_caret_unit_specs_rotted_2026_10_19 | P2 | open | llm_caret unit specs fail at source: 4 parse errors (unterminated docstring, stray indent) and claude_cli_spec calls undefined _Q/_escape_json | `test/01_unit/app/llm_caret/claude_cli_spec.spl:195` |
| seed_coalesce_stateful_operand_twice_2026_10_12 | P2 | open | Seed coalesce evaluates a stateful optional operand twice in ast_semantic_hash_finish | `src/compiler/10.frontend/generated/ast_semantic_value.spl:1` |
| pure_simple_nested_extern_registration_2026_10_12 | P2 | open | Pure-Simple compiler does not register a function-nested extern declaration | `src/compiler/00.common/parallel.spl:1` |
| llvm_inline_asm_dialect_false_green_2026_10_12 | P2 | open | LLVM seed drops Intel-syntax inline asm port instructions without an explicit dialect | `src/lib/nogc_async_mut_noalloc/baremetal/x86/io.spl:1` |
| item5_phase3_early_mir_crash_2026_10_14 | P1 | open | Phase3 compiler crashes in early MIR after zero unresolved generic calls | `doc/08_tracking/bug/item5_phase3_open_failures_2026_10_14.md:1` |
| item5_generic_optional_payload_acceptance_2026_10_14 | P1 | open | Generic specialization accepts wrong optional enum payload | `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:1` |
| item5_cranelift_module_data_support_2026_10_14 | P2 | open | Cranelift cannot declare imported globals or non-scalar module statics | `src/compiler/70.backend/backend/cranelift_codegen_adapter.spl:1` |
| item5_native_object_resource_growth_2026_10_14 | P1 | open | Native object collection exceeds diagnostic memory reserve | `doc/08_tracking/bug/item5_phase3_open_failures_2026_10_14.md:1` |
| item5_native_build_threads_ineffective_2026_10_14 | P2 | open | Native builder thread option does not parallelize module compilation | `doc/08_tracking/bug/item5_phase3_open_failures_2026_10_14.md:1` |
| item5_backend_error_opaque_enum_2026_10_14 | P2 | open | Backend AOT diagnostics discard structured error details | `src/compiler/70.backend/backend_plugin/session_authority_v2.spl:1` |
| explicit_generic_interpolation_transport_2026_10_14 | P1 | open | Canonical interpolation loses explicit helper type arguments | `doc/08_tracking/bug/explicit_generic_interpolation_transport_2026_10_14.md:1` |
| bare_enum_pattern_binding_in_compiler_2026_10_14 | P1 | open | Contested bare Function enum pattern becomes a binding | `doc/08_tracking/bug/bare_enum_pattern_binding_in_compiler_2026_10_14.md:1` |
| mir_json_c0_escaping_2026_10_12 | P1 | open | MIR JSON must escape every C0 control and preserve Unicode | `src/compiler/50.mir/mir_json.spl:693` |
| imported_generic_native_callee_owner_loss_2026_10_12 | P1 | open | Imported generic native call loses defining module owner | `src/compiler/40.mono/monomorphize_integration.spl:2064` |
| nul_literal_double_box_constructor_2026_10_12 | P1 | open | NUL literal double boxing copies string metadata into content | `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:5000` |
| runtime_byte_text_utf8_invariant_2026_10_12 | P1 | open | Byte-to-text decoder constructs invalid UTF-8 RuntimeString | `doc/08_tracking/bug/runtime_byte_text_utf8_invariant_2026_10_12.md:3` |
| archive_owner_source_grammar_2026_10_12 | P1 | open | Archive owner source grammar blocks compiler discovery | `src/compiler/80.driver/cache/hir_body_semantic_lease_v1.spl:151` |
| block_error_span_source_metadata_loss_2026_10_12 | P1 | open | Block error spans lose source filename | `src/compiler/15.blocks/blocks/error_helpers.spl:39` |
| block_highlighting_raw_escape_native_hex_2026_10_12 | P1 | open | Block highlighting raw escapes and missing native hex method | `src/compiler/15.blocks/blocks/highlighting.spl:85` |
| result_err_missing_native_projection_2026_10_12 | P1 | open | Result.err missing native typed error projection | `doc/08_tracking/bug/result_err_missing_native_projection_2026_10_12.md:3` |
| enum_payload_declaring_owner_binding_2026_10_12 | P1 | open | Imported enum payload type lacks declaring owner qualified binding | `doc/08_tracking/bug/enum_payload_declaring_owner_binding_2026_10_12.md:3` |
| windows_terminal_raw_bytes_crlf_translation_2026_10_12 | P1 | open | Windows raw terminal write translates LF and misreports output byte count | `doc/08_tracking/bug/windows_terminal_raw_bytes_crlf_translation_2026_10_12.md:3` |
| windows_piped_process_cold_handle_growth_2026_10_12 | P1 | open | Windows piped process cold handle growth blocks resource qualification | `doc/08_tracking/bug/windows_piped_process_cold_handle_growth_2026_10_12.md:3` |
| process_stdout_result_eof_drain_race_2026_10_12 | P1 | open | Stdout Result facade loses buffered data when child exits | `doc/08_tracking/bug/process_stdout_result_eof_drain_race_2026_10_12.md:3` |
| mcp_score_tagged_text_local_provenance_2026_10_12 | P1 | open | Native MCP score formatter converts tagged text local as integer | `doc/08_tracking/bug/mcp_score_tagged_text_local_provenance_2026_10_12.md:3` |
| phase1_docstring_trim_start_dispatch_2026_10_12 | P2 | open | Phase1 source doctest inventory cannot dispatch str.trim_start | `src/lib/nogc_sync_mut/test_runner/doctest_runner.spl:93` |
| optional_array_ifval_type_and_nil_constant_2026_10_12 | P1 | open | Guarded Optional array loses payload type then emits invalid LLVM nil pointer constant | `src/compiler/20.hir/hir_lowering/statements.spl:594` |
| mir_struct_literal_kind_unimplemented_2026_10_12 | P1 | open | MIR rejects supported brace struct literal expression | `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:6030` |
| lsp_mcp_text_stdout_tagged_value_abi_2026_10_12 | P1 | open | LSP MCP raw text reaches tagged-value print ABI | `src/app/simple_lsp_mcp/json_helpers.spl:13` |
| test_whole_cli_scope_provenance_2026_10_12 | P1 | open | Whole test CLI omits documentation scope provenance | `src/lib/nogc_sync_mut/test_runner/test_runner_args.spl:364` |
| windows_collector_named_file_digest_escape_2026_10_12 | P1 | open | Windows collector rejects GNU escaped filename digest | `scripts/bootstrap/bootstrap-logged-process.shs:21` |
| test_runner_process_limit_overflow_2026_10_12 | P1 | open | Test runner accepts overflowing process limit | `src/lib/nogc_sync_mut/test_runner/resource_policy.spl:7` |
| windows_spipe_gitlink_alias_pending_policy_missing_2026_10_12 | P1 | open | Windows SPipe gitlink aliases omitted from pending policy | `scripts/setup/windows-materialized-pending-policy.tsv:5` |
| windows_materializer_genuine_symlink_conversion_unsupported_2026_10_12 | P1 | open | Materializer rejects genuine tracked Windows symlinks | `scripts/setup/materialize-symlinks-windows.shs:1490` |
| windows_native_checkout_symlinks_materializer_contract_2026_10_12 | P1 | open | Windows native checkout violates materializer placeholder contract | `scripts/setup/materialize-symlinks-windows.shs:1490` |
| bootstrap_llvm_cli_static_provider_rejected_2026_10_12 | P1 | open | Bootstrap CLI backend incorrectly requires a shared LLVM provider | `scripts/setup/platform-detect.shs:129` |
| mcp_native_score_conversion_2026_10_12 | P1 | open | Native score to_int unresolved in MCP | `src/app/mcp/main_lazy_ctx_tools.spl:597` |
| mcp_native_array_extend_2026_10_12 | P1 | open | Native array extend unresolved in MCP | `src/app/mcp/main_lazy_caret_tools.spl:94` |
| transient_empty_scope_highwater_scan_2026_10_12 | P1 | open | Empty transient scopes scan prior allocation high water | `src/runtime/runtime_native.c:2005` |
| bounded_read_limit_allocation_2026_10_12 | P1 | open | Bounded regular-file reads eagerly allocate the policy limit | `src/runtime/runtime_native.c:11834` |
| hir_imported_generic_owner_method_scope_2026_10_12 | P1 | open | Imported generic method signatures lose owner binders | `src/compiler/20.hir/hir_lowering/_Items/module_callable_types.spl:0` |
| core_c_archive_failure_diagnostics_2026_10_12 | P1 | open | Bootstrap core-C archive failures lose actionable diagnostics | `src/compiler_rust/compiler/src/pipeline/native_project/tools.rs:0` |
| macos_bootstrap_capsule_duplicate_native_all_exports_2026_10_12 | P1 | open | macOS Stage2 bootstrap capsule duplicates native-all ABI file and snapshot providers | `src/compiler_rust/compiler/src/pipeline/native_project/tools.rs:2402` |
| atomic_write_tagged_text_abi_2026_10_12 | P1 | open | Atomic snapshot write receives raw pointers instead of tagged text | `src/compiler/50.mir/text_extern_abi.spl:213` |
| mir_json_quadratic_identity_allocation_2026_10_12 | P1 | open | MIR identity JSON serialization copies quadratic prefixes | `src/compiler/50.mir/mir_json.spl:658` |
| linux_bootstrap_llvm18_vs_llvm23_authority_2026_10_12 | P1 | open | Linux native bootstrap LLVM18 conflicts with LLVM23 authority | `.github/workflows/rust-bootstrap-multiplatform.yml:291` |
| mir_json_unescaped_control_bytes_2026_10_12 | P1 | open | MIR JSON string escaping leaves control bytes unescaped | `src/compiler/50.mir/mir_json.spl:0` |
| bootstrap_portability_k1_static_gate_drift_2026_10_12 | P2 | open | Static portability gate rejects canonical and alternate K1 selection source | `scripts/check/check-bootstrap-portability.shs:114` |
| bootstrap_portability_prefix_owner_drift_2026_10_12 | P2 | open | Portability gate rejects current frontend milestone matrix and FreeBSD source owners | `scripts/check/check-bootstrap-portability.shs:133` |
| linux_phase2_backend_fixture_drift_2026_10_12 | P2 | open | Linux Phase2 contract fixture omits mandatory backend and bound receipt fields | `test/01_unit/scripts/linux_phase2_false_pass_contract_test.shs:127` |
| bootstrap_portability_stale_owner_contracts_2026_10_12 | P2 | open | Portability gate retains retired compiler source owners | `scripts/check/check-bootstrap-portability.shs:731` |
| self_hosted_rc1_hir_codec_segv_native_build_2026_10_11 | P1 | open | Self-hosted rc.1 binary SIGSEGVs in HIR codec on any native-build of the current tree | `src/compiler/20.hir/generated/hir_codec.spl:0` |
| bootstrap_imported_free_method_rebind_2026_10_12 | P1 | open | Imported libc free rebinds to RtStringBuilder.free in bootstrap closure | `src/compiler_rust/compiler/src/pipeline/native_project/imports.rs:476` |
| sheets_ascii_width_ambiguous_string_builder_owner_2026_10_12 | P1 | open | Spreadsheet ASCII width HIR import selects wrong string builder owner | `src/app/office/sheets/ascii_width.spl:2` |
| borrowed_dict_index_owner_2026_10_11 | P1 | open | Borrowed Dict indexing lowers text keys as array offsets | `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:635` |
| mcp_record_array_owner_loss_2026_10_11 | P1 | open | MCP declared record arrays lose field and loop element owners | `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:940` |
| mcp_native_source_form_gaps_2026_10_11 | P1 | open | MCP native StructLit extend aggregate map and float conversion gaps | `src/app/mcp/main_static_tools.spl:228` |
| BUG-SCV-BOOTSTRAP-COMPOSITION-SCOPE-20261011 | P1 | open | Bootstrap generated CUDA selector is outside canonical SCV inventory scope | `src/app/compiler_entrypoint/source_authority.spl:108` |
| result_err_record_owner_erased_2026_10_11 | P1 | open | Imported Result Err record field loses provider ownership | `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:3693` |
| redis_tagged_text_runtime_abi_2026_10_11 | P1 | open | Redis tagged text and listener contracts block startup | `src/compiler/50.mir/text_extern_abi.spl:194` |
| enum_static_receiver_owner_erasure_2026_10_11 | P1 | open | MIR drops exact static enum receiver authority | `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:4709` |
| result_tuple_unwrap_payload_2026_10_11 | P1 | open | Result tuple unwrap rejects the ranking pair payload | `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:704` |
| pure_database_total_conversion_as_optional_2026_10_11 | P1 | open | PureDatabase numeric validation uses total conversions as Optional | `src/lib/nogc_sync_mut/database/pure_sql/_PureDatabase/row_value_helpers.spl:222` |
| hir_primitive_field_reexport_advisory_2026_10_11 | P2 | open | Imported primitive fields trigger false reexport advisories | `src/compiler/20.hir/hir_lowering/_Items/module_import_registration.spl:136` |
| mono_match_capability_owner_2026_10_11 | P1 | open | Match-result ReferenceCapability loses nominal owner | `src/compiler/40.mono/monomorphize/util.spl:0` |
| native_cache_contract_mir_lowering_gaps_2026_10_11 | P1 | open | Cache codec and TLD MIR owner lowering gaps | `src/compiler/00.common/cache_contract/canonical_cache_codec_v1.spl:0` |
| deferred_optional_tuple_owner_2026_10_11 | P1 | open | Deferred optional tuple payload loses definition owner | `src/compiler/40.mono/monomorphize/deferred.spl:0` |
| stringlit_optional_array_owner_2026_10_11 | P1 | open | String interpolation optional array loses traversal type | `src/compiler/40.mono/monomorphize/type_subst.spl:0` |
| layout_symbol_function_pattern_owner_2026_10_11 | P1 | open | Optional symbol Function pattern loses enum owner | `src/compiler/20.hir/hir_symbol_table_methods.spl:0` |
| mir_ret_optional_operand_owner_2026_10_11 | P1 | open | Optional return operand coalescing loses MIR owner | `src/compiler/50.mir/mir_instruction_graph.spl:0` |
| runner_callback_field_owner_2026_10_11 | P1 | open | Callback field dispatch and indirect return owner loss | `src/app/io/env_access_host.spl:0` |
| native_enum_nil_payload_pattern_2026_10_11 | P1 | open | Nested nil enum payload and optional text provenance | `src/app/io/rt_hal_isolated_host.spl:0` |
| native_sdn_empty_payload_owner_2026_10_11 | P1 | open | Empty SDN enum containers lose payload type | `src/lib/common/sdn/value.spl:0` |
| parser_contextual_new_index_2026_10_11 | P1 | open | Contextual new identifier indexing emits unsupported allocation AST | `src/compiler/00.common/cache_contract/semantic_facet_manifest_v1.spl:0` |
| native_deferred_range_index_2026_10_11 | P1 | open | Native range indexing blocks deferred deserialization | `src/compiler/40.mono/monomorphize/deferred_deserialize.spl:0` |
| native_optional_struct_pointer_nil_2026_10_11 | P1 | open | Optional struct binding emits invalid pointer nil constant | `src/compiler/40.mono/monomorphize/tracker.spl:0` |
| native_identity_i64_receiver_type_loss_2026_10_11 | P1 | open | Known i64 identity receivers lose MIR method provenance | `src/compiler/80.driver/native_capsule_mir_identity.spl:0` |
| native_huffman_untyped_return_guard_2026_10_11 | P1 | open | Native Huffman untyped returns block normal object generation | `src/lib/nogc_sync_mut/compression/gzip/huffman.spl:393` |
| native_huffman_bitstream_nested_array_abi_2026_10_11 | P1 | open | Native Huffman bitstream nested array ABI crashes | `src/lib/nogc_sync_mut/compression/gzip/huffman.spl:393` |
| mir_custom_slice_string_dispatch_2026_10_11 | P1 | open | Custom slice receiver incorrectly dispatched to string runtime | `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:0` |
| hir_imported_generic_owner_scope_2026_10_11 | P1 | open | Imported composite fields lose owner type parameter scope | `src/compiler/20.hir/hir_lowering/_Items/module_import_registration.spl:0` |
| caret_cs_host_provider_exports_2026_10_11 | P1 | open | CS host provider aliases and missing sleep owner | `src/lib/nogc_sync_mut/io.spl:126` |
| hir_tui_builtin_len_resolution_2026_10_10 | P1 | open | CS native closure cannot resolve TUI builtin len | `src/lib/nogc_sync_mut/tui/widgets/input.spl:297` |
| mir_chained_named_receiver_owner_2026_10_10 | P1 | open | MIR loses ByteSpan owner on chained slice equals call | `src/lib/common/bytes/span.spl:116` |
| web_tls_helper_imports_and_sha256_alias_2026_10_10 | P1 | open | Web TLS consumers lack canonical helper imports and SHA256 alias | `src/lib/nogc_sync_mut/tls/utilities.spl:24` |
| caret_essential_leaf_provider_gaps_2026_10_10 | P1 | open | Caret essential closure has missing leaf providers and manager adapters | `src/app/llm_caret/tui_io.spl:173` |
| BUG-MIR-OPTION-NIL-ARM-STALE-PRODUCER-20261010 | P1 | open | Retained80030 rejects optional nil absence pattern | `src/lib/common/binary_io.spl:145` |
| native_negative_literal_match_patterns_2026_10_10 | P1 | open | Negative integer patterns become multiple wildcard arms | `src/app/cli/native_build_exit_status.spl:3` |
| class_scoped_visibility_parser_failure_2026_10_10 | P1 | open | Class scoped visibility parser rejects WEB package members | `src/compiler/10.frontend/core/_ParserDecls/fn_struct_decls.spl:1093` |
| std_io_runtime_ranged_read_export_missing_2026_10_10 | P1 | open | Root io_runtime facade omits checked ranged read | `src/lib/io_runtime.spl:19` |
| http_response_missing_utf8_provider_import_2026_10_10 | P1 | open | HTTP response imports absent base_encoding byte conversion | `src/lib/nogc_sync_mut/http_server/response.spl:11` |
| phase3_prescan_symbolkind_workaround_2026_10_10 | P1 | open | Prescan SymbolKind bare unit OR loses owner | `src/compiler/50.mir/_MirLowering/module_lowering.spl:1323` |
| native_result_try_payload_text_type_lost_2026_10_10 | P1 | open | Result try payload loses text provenance | `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:0` |
| mutex_lock_return_only_generic_needs_call_type_2026-10-10 | P1 | open | Return-only mutex generic needs explicit value annotation | `src/lib/nogc_sync_mut/rt_hal/boundary.spl:138` |
| phase3_global_pool_generic_inference_workaround_2026_10_10 | P1 | open | Global array generic inference fails and typed local control crashes | `src/compiler/10.frontend/core/types.spl:1517` |
| plugin_bare_unit_or_owner_workaround_2026_10_10 | P1 | open | Plugin bare unit OR alternatives lose enum owner | `src/plugins/backend_vulkan/vulkan_backend.spl:0` |
| phase3_compiler_unit_or_workaround_2026-10-10 | P1 | open | Compiler bare unit OR alternatives lose payload binding owner | `src/compiler/20.hir/hir_lowering/_Expressions/expression_components.spl:0` |
| cuda_unary_mir_type_or_owner_2026_10_10 | P1 | open | CUDA unary MIR type OR alternatives lose enum ownership | `src/plugins/backend_cuda/cuda_backend.spl:358` |
| BUG-MIR-ENUM-FIELD-RECEIVER-20261010 | P1 | open | Native80030 loses enum field receiver for TrustAuditStatus.name | `src/compiler/00.common/assurance/trust_audit.spl:0` |
| BUG-WIN-HIR-WORKER-DIAGNOSTICS-20261010 | P1 | open | Windows HIR worker exits before inventory without retained child diagnostics | `src/app/cli/native_build_main.spl:0` |
| hir_empty_worker_startup_overhead_2026-10-05 | P1 | open | Explicit HIR parallelism starts nineteen empty workers for one module | `src/app/cli/native_build.spl:0` |
| seed_global_interface_cache_rebuild_latency_2026-10-05 | P1 | open | Seed global interface cache key rebuilds unchanged modules | `src/compiler_rust/compiler/src/pipeline/native_project/mod.rs:1246` |
| mono_return_context_and_fixed_nominal_binding_2026-10-05 | P1 | open | Monomorphization loses generic result context and compares module-local nominal IDs | `src/compiler/40.mono/monomorphize_integration.spl:532` |
| parse_disable_suppresses_explicit_hir_parallelism_2026-10-05 | P1 | open | Disabling parse warmup suppresses explicitly enabled HIR parallel workers | `src/app/cli/native_build_main.spl:768` |
| parse_closure_directory_root_validation_2026-10-05 | P1 | open | Parallel parse closure rejects source directory selectors | `src/compiler/80.driver/driver_build/native_entry_closure_receipt.spl:1` |
| early_let_aggregate_metadata_transport_2026-10-05 | P1 | open | Early Let transports aggregate receiver metadata across staged ABI | `src/compiler/50.mir/mir_lowering_stmts.spl:1` |
| result_bool_array_unwrap_payload_rejected_2026-10-05 | P1 | open | Native Result unwrap rejects boolean and array payloads | `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:1` |
| scv_chunk_publication_concurrent_reader_2026-10-05 | P1 | open | SCV final chunk names become visible before complete publication | `src/lib/scv/compile_snapshot.spl:1` |
| phase2_subsystem_helper_mir_failures_2026-10-05 | P1 | open | Phase 2 test generator and verdict helpers fail MIR lowering | `src/compiler/10.frontend/core/flat_pool_codec.spl:37` |
| p4_gui_browser_missing_owner_imports_2026-10-05 | P1 | open | Phase 4 GUI browser modules omit implementation owner imports | `src/app/editor/gui_shell.spl:1` |
| mcp_t32_module_owner_omissions_2026-10-05 | P1 | open | Phase 4 TRACE32 modules omit shared owner declarations | `examples/10_tooling/trace32_tools/t32_mcp/action_tools.spl:1` |
| phase3_post_hir_owner_transport_av_2026-10-05 | P1 | open | Phase 3 access violation after successful HIR collection | `src/compiler/80.driver/driver_hir_pipeline_lowering.spl:1077` |
| windows_runtime_object_cache_2026-10-05 | P1 | open | Windows runtime objects are rebuilt for unchanged compilation inputs | `src/compiler/70.backend/backend/runtime_compiler.spl:483` |
| brace_dictionary_type_tags_discarded_2026-10-05 | P1 | open | Brace dictionary annotations discard key and value type tags | `src/compiler/10.frontend/core/parser.spl:1090` |
| native_dictionary_array_value_erasure_2026-10-05 | P1 | open | Native dictionary array value erasure blocks trait fixture | `src/compiler/00.common/cache/reverse_reference_facts.spl:144` |
| windows_production_dynamic_backend_provider_incomplete_2026-10-05 | P1 | open | Windows production dynamic backend providers are incomplete | `src/runtime/runtime_backend_plugin.c:161` |
| comment_only_block_swallows_next_statement_2026-10-04 | P1 | open | Comment-only block body silently swallows the next statement: `if false:` + comment-only body makes the following sibling statement the if body (pure-Simple parse_block flat-body rule; seed same) | `src/compiler/10.frontend/core/parser_stmts.spl:391` |
| bug_add_rename_path_recursion_rewrites_db_2026-10-04 | P1 | open | bug-add crashes with rename_path infinite recursion, and its bug_db.sdn.tmp drops ~1700 existing lines | `src/lib/nogc_sync_mut/io_runtime.spl:469` |
| stage3_scv_inventory_noncanonical_2026_09_20 | P1 | open | Stage 3 SCV source inventory is noncanonical on admitted FreeBSD Stage 2 compiler | `src/lib/scv/compile_source_inventory.spl:257` |
| stage3_macos_full_graph_hir_sigsegv_2026_09_21 | P0 | open | macOS Stage3 full-graph HIR crashes with SIGSEGV after 104 of 848 modules | `src/compiler/20.hir/hir_lowering/types.spl:0` |
| gpu_ffi_loader_probes_linux_sonames_on_macos_2026_09_19 | P2 | open | gpu_lib_candidates probes Linux sonames on macOS (SIMPLE_OS_TYPE never set) and spl_dlopen raises where DynLib.load expects nil | `src/lib/nogc_sync_mut/gpu/engine2d/ffi_dispatch.spl:60` |
| after_each_captured_var_compound_assignment_lost_2026-08-04 | P2 | open | Write in after_each that reads the captured var is lost; constant write is not | `src/lib/nogc_sync_mut/spec.spl:0` |
| any_slot_holds_untagged_scalar_2026-08-05 | P2 | open | ANY-typed slots hold raw untagged scalars on the JIT lane | `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl:0` |
| app_mcp_intensive_spec_is_84s_not_a_hang_eight_real_failures_2026-08-10 | P2 | open | app_mcp_intensive_spec is not hung: 84s spec, RED with 8 real failures | `test/02_integration/app/app_mcp_intensive_spec.spl:0` |
| app_modules_referenced_by_specs_exist_nowhere_2026-08-04 | P2 | open | Spec-referenced app symbols missing: handle_os_inline / handle_os_build_inline | `src/app/cli/main.spl:0` |
| architecture_rule_audit_2026-08-10 | P3 | open | Two Perl scripts violate the 'ALL code in .spl/.shs' rule | `scripts/check/lib/portable-hardlink-lock.pl:0` |
| architecture_rule_audit_2026-08-11 | P3 | open | Architecture audit of 2026-08-10-11 window: 4 findings need a decision | `src/compiler/35.semantics/gc_boundary_check.spl:0` |
| arity_census_reaudit_declaration_side_defects_2026-08-04 | P3 | open | Arity census re-audit: declaration side is not ground truth, remainder filed | `src/lib/common/wine_vm_adapter.spl:0` |
| arm64_efi_real_firmware_lane_unreproducible_and_unified_lane_uses_kernel_2026-08-11 | P2 | open | Unified arm64 lane still boots with QEMU -kernel instead of real firmware | `scripts/check/check-simpleos-arm64-unified-live.shs:233` |
| arm64_simpleos_virtio_blk_durable_write_gap_2026-08-14 | P2 | open | ARM64 SimpleOS VirtIO-BLK durable-write gap | `src/os/apps/servers_user/database_persistence_adapter.spl:0` |
| artifact_manifest_signature_verification_no_trust_anchor_2026-08-07 | P2 | open | SimpleArtifactManifest.signature has no trust-anchor or key-distribution infra | `src/os/kernel/loader/artifact_manifest.spl:0` |
| backend_capability_spec_fictional_test_builder_api_2026-07-30 | P3 | open | backend_capability_spec: 34 commented tests target a never-built capability API | `test/01_unit/compiler/backend/backend_capability_spec.spl:0` |
| backend_interpreter_symbol_type_unresolved_monomorphize_2026-08-11 | P2 | open | backend/interpreter.spl `unresolved type: Symbol` at stage4 native-build | `src/compiler/backend/backend/interpreter.spl:0` |
| bare_field_reference_in_methods_is_illegal_but_pervasive_2026-08-10 | P2 | open | Bare field reference inside methods illegal in every lane yet ~740 product sites use it | `src/compiler/20.hir/hir_lowering/expressions.spl:0` |
| baremetal_entry_closure_class_instantiation_fault_2026-07-06 | P1 | open | Baremetal --entry-closure imported-class instantiation faults at runtime | `src/app/cli/native_build_main.spl:0` |
| bare_name_registry_collision_trigger_conditions_2026-07-30 | P2 | open | Bare-name type registry collision real in situ but trigger conditions unreproduced | `src/compiler/10.frontend/core/types.spl:733` |
| board_vulkan_cross_arch_boundary_only_x86_64_proven_2026-08-11 | P3 | open | Board-Vulkan cross-arch boundary capture proven only on x86_64 | `src/os/drivers/gpu/board_vulkan/boundary_arch.spl:0` |
| board_vulkan_independence_group_is_unverified_declaration_2026-08-11 | P3 | open | independence_group is an unverified pub val; a mislabel is undetectable | `src/os/drivers/gpu/board_vulkan/provider_inventory.spl:0` |
| board_vulkan_lanes_fabricated_counterpart_output_despite_available_exec_api_2026-08-11 | P2 | open | Board-Vulkan lanes compared against fabricated counterpart output | `src/os/drivers/gpu/board_vulkan/boundary_enumeration_provider.spl:104` |
| board_vulkan_no_headless_lavapipe_pixel_dump_binary_2026-08-11 | P3 | open | No installed CLI can drive lavapipe to a raw pixel dump without new host code | `src/os/drivers/gpu/board_vulkan/boundary_readback_gate.spl:0` |
| bool_typed_parameter_accepts_non_bool_and_jit_corrupts_it_2026-08-04 | P2 | open | A bool-declared parameter silently accepts a non-bool (rejection half still open) | `src/compiler_rust/compiler/src/interpreter_call/core/arg_binding.rs:68` |
| bootstrap_stage4_selfhost_parse_memory_blowup_2026-07-20 | P1 | open | Stage-4 self-host parse-phase memory blowup; native scale admission pending | `src/compiler/80.driver/driver_source_pipeline_parsing.spl:0` |
| borrow_check_spurious_errors_refuted_and_two_fail_opens_2026-08-08 | P2 | open | Borrow-check driver fail-opens (primary spurious-error claim refuted) | `src/compiler/55.borrow/borrow_check/nll.spl:363` |
| browser_dom_event_object_gc_retention_2026-07-31 | P2 | open | Browser DOM event object GC reachability reclamation not implemented | `src/lib/gc_async_mut/gpu/browser_engine/script/event_api.spl:0` |
| browser_engine_css_contain_size_unimplemented_2026-08-08 | P2 | open | CSS contain:size parses but is never consulted by the sizing pass | `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl:1140` |
| browser_engine_css_position_fixed_not_viewport_anchored_2026-08-08 | P2 | open | position:fixed resolves against nearest ancestor not the viewport | `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl:440` |
| browser_engine_text_metrics_api_drift_2026-07-20 | P3 | open | browser_engine text-metrics spec: residual API gaps after content_x/y landed | `src/lib/gc_async_mut/gpu/browser_engine/browser_renderer.spl:15` |
| browser_engine_wikipedia_render_perf_2026-07-11 | P2 | open | Real-page software render is ~176s interpreted; 10s budget always degrades | `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl:0` |
| browser_layout_module_exceeds_128kib_parser_limit_2026-07-31 | P1 | open | Four browser layout modules exceed the 128 KiB parser limit | `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl:0` |
| browser_renderer_linux_pre_exec_sandbox_gap_2026-07-28 | P3 | open | Source fixed; runtime evidence pending for browser renderer Linux pre-exec sandbox | `src/runtime/runtime_process.c:0` |
| browser_renderer_spec_sequence_failures_2026-06-11 | P2 | open | browser_renderer_spec 22 residual failures (sequence-dependent + :has(> )) | `src/lib/gc_async_mut/gpu/browser_engine/browser_renderer.spl:0` |
| browser_seccomp_denylist_and_inprocess_unjailed_2026-08-15 | P1 | open | In-process browsers under src/app/browser never enter the seccomp jail | `src/runtime/runtime_process.c:2384` |
| browser_webgpu_js_wasm_spec_perf_2026-06-14 | P3 | open | WebGPU JS/WASM system spec sits near its perf threshold | `test/03_system/app/browser/feature/webgpu_js_wasm_simple_spec.spl:0` |
| builtin_dict_set_silent_insert_audit_2026-07-31 | P2 | open | Builtin Dict .set() silently fails to insert when the receiver is not scope-resolved to a | `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl:0` |
| bytespan_starts_with_dropped_from_kernel_closure_weak_nil_stub_2026-07-28 | P1 | open | ByteSpan.starts_with is dropped from the SimpleOS kernel closure and replaced by a nil-ret | `src/compiler_rust/compiler/src/pipeline/native_project/stubs.rs:0` |
| cache_v2_first_milestone_known_gaps_2026-08-10 | P2 | open | Cache v2 interface-compat milestone ships with known unfixed gaps (GC admission, lease, ap | `src/compiler/80.driver/cache/gc/admission.spl:0` |
| capability_group_from_unsound_under_value_semantics_2026-08-09 | P2 | open | Capability-group .from() is unsound because classes are value types, so the group copies n | `src/compiler/35.semantics/lint/dynamic_capability_acquire.spl:0` |
| cargo_test_lib_129_failures_triage_2026-08-10 | P2 | open | cargo test -p simple-compiler --lib has 129 remaining unit-test failures after 6 were fixe | `src/compiler_rust/compiler/src/lint/checker_core.rs:0` |
| char_code_at_quadratic_scan_and_core_string_ascii_probe_2026-07-30 | P2 | open | char_code_at is quadratic on non-ASCII text and core_string's ASCII fast path is itself O( | `src/runtime/simple_core/core_string.spl:0` |
| check_costs_two_seconds_per_function_decl_2026-08-10 | P2 | open | `simple check` costs ~2s per function declaration plus ~20s fixed per worker process | `src/app/check/main.spl:0` |
| check_guard_wiring_48_unwired_triage_2026-08-08 | P3 | open | 48 check-guard scripts are wired into no caller, so their failures can never gate anything | `scripts/check/check-guard-wiring.shs:0` |
| check_run_diagnostics_help_text_and_type_check_gaps_2026-07-20 | P2 | open | `simple check` misses help: annotations and does not detect type mismatches at all | `src/app/check/main.spl:0` |
| check_script_wiring_orphans_2026-08-01 | P3 | open | 364 of 413 check scripts are invoked by nothing, so their gates never run | `scripts/check/check-guard-wiring.shs:0` |
| cli_dispatch_perf_spec_failure_2026-06-21 | P3 | open | test/05_perf/cli_dispatch_perf_spec.spl fails its dispatch latency budget | `test/05_perf/cli_dispatch_perf_spec.spl:0` |
| cmdstream_boundary_no_intel_gpu_on_capture_host_2026-08-11 | P3 | open | vulkan.submit.command_stream@1 boundary has no Intel Gen12 encoder implementation anywhere | `src/os/drivers/gpu/board_vulkan/backend_intel_gen12.spl:0` |
| codegen_rt_prefix_local_function_collision_sigsegv_2026-07-12 | P1 | open | A local function whose name matches a runtime SFFI symbol compiles to a SIGSEGV, not a cal | `src/compiler_rust/compiler/src/codegen/instr/calls.rs:0` |
| code_quality_specs_import_modules_that_do_not_exist_2026-08-04 | P2 | open | code_quality specs import std.common.set_utils/iterable and Set type that do not exist | `test/system/code_quality/deprecated_removed_spec.spl:32` |
| comment_cheat_absent_capabilities_2026-08-10 | P2 | open | ARM64 EL0 handoff concurrency contract unimplemented (comment-cheat ABSENT family) | `src/os/kernel/arch/arm64/user_entry.spl:68` |
| compatibility_aliases_retained_unreachable_targets_2026-07-19 | P3 | open | Alias _stubs.o section retention: ELF fixed, Mach-O/COFF still pending | `src/compiler/70.backend/linker/obj_taker.spl:0` |
| compiler_driver_v1_bootstrap_activation_blocked_on_callable_loader_2026-08-14 | P2 | open | CompilerDriverV1 activation blocked on a callable provider loader | `src/app/cli/bootstrap_main.spl:11` |
| compiler_test_sweep_residuals_2026-08-16 | P2 | open | Compiler test sweep residuals: 8 interpreter gaps plus backend integration fails | `src/compiler/10.frontend/core/parser.spl:0` |
| const_generic_argument_rejected_in_constructor_call_2026-08-17 | P3 | open | Const-generic argument rejected in constructor-call position (feature gap) | `src/compiler/10.frontend/core/parser_expr.spl:767` |
| core_c_stdin_fgetc_hang_2026-06-02 | P3 | open | json_helpers.spl still uses the C fgetc-based stdin_read_char (proper fix pending) | `src/runtime/runtime_native.c:0` |
| core_intensive_spec_tests_local_stubs_not_database_core_2026-08-04 | P2 | open | core_intensive_spec.spl is vacuous - tests local stubs, not std.database.core | `test/02_integration/compiler/core_intensive_spec.spl:5` |
| core_purity_runtime_split_blocked_native_const_resolution_2026-07-08 | P2 | open | Cross-module NATIVE_* constant resolution blocks the runtime.spl core-purity split | `src/lib/common/js/engine/runtime.spl:0` |
| coverage_probe_plan_skips_struct_method_decisions_2026-08-15 | P3 | open | Coverage probe plan skips struct-method decisions; SIMPLE_COVERAGE on run writes nothing | `src/compiler_rust/compiler/src/mir/lower/lowering_coverage.rs:0` |
| coverage_tooling_does_not_instrument_spl_2026-08-07 | P2 | open | No branch probes from MIR lowering; no coverage artifact on the .spl runner path | `src/compiler_rust/compiler/src/mir/lower/lowering_coverage.rs:0` |
| cover_gate_fails_every_system_test_without_running_one_2026-08-04 | P2 | open | # @cover gate marks 227 system tests FAILED without running one | `src/lib/nogc_sync_mut/test_runner/test_runner_files.spl:203` |
| c_parser_library_specced_but_never_implemented_2026-08-04 | P2 | open | src/lib/common/c_parser/ specced by 56 system-test examples but never existed | `test/03_system/compiler/c_parser_spec.spl:16` |
| cpu_hotloop_gate_red_key_churn_and_prose_scoring_2026-08-01 | P3 | open | CPU hot-loop idiom gate red at new=158 from key churn, not new debt | `scripts/check/cpu_lane_hotloop_baseline.txt:0` |
| cranelift_ssa_phi_nary_join_guard_now_fires_2026-08-17 | P2 | open | cranelift __simple_ssa_phi N-ary-join guard fires in sugar_plugin_spec | `src/compiler/70.backend/backend/cranelift_codegen_adapter.spl:728` |
| credential_v1_records_have_no_upgrade_on_write_owner_2026-08-08 | P3 | open | v1 credential records never rewritten; no config writer owns the upgrade | `src/lib/nogc_sync_mut/terminal/credential/config_parser.spl:0` |
| cross_engine_value_semantics_harness_known_red_2026-08-10 | P2 | open | Cross-engine value-semantics differential harness landed KNOWN-RED | `test/03_system/language/value_semantics/cross_engine_value_semantics_spec.spl:0` |
| cross_language_actual_execution_mode_receipt_missing_2026-08-12 | P3 | open | Cross-language source/SMF actual execution-mode receipt missing | `src/app/cli/_CliMain/main_and_help.spl:0` |
| cross_module_collisions_debugconfig_and_pub_shell_entangled_2026-08-15 | P3 | open | DebugConfig and public shell collisions too entangled to rename | `src/lib/nogc_sync_mut/io/process_ops.spl:434` |
| cross_module_public_symbol_collisions_2026-08-16 | P3 | open | Cross-module public symbol collisions (bootstrap warnings, wrong-dispatch risk) | `src/lib/nogc_sync_mut/tooling/easy_fix/types.spl:135` |
| cuda_gpu_gated_spec_defects_2026-08-09 | P2 | open | CUDA/GPU defects uncovered by opening the P15 env gates | `src/lib/gc_async_mut/gpu_lane/cuda_vm_executor.spl:0` |
| cuda_lane_conflates_svmg_budget_sentinel_with_device_timeout_2026-08-09 | P2 | open | CUDA lane reads SVM-G budget sentinel as a device timeout | `src/lib/gc_async_mut/gpu_lane/cuda_lane_session.spl:292` |
| curve448_x448_scalarmult_kat_mismatch_2026-07-20 | P1 | open | Curve448/X448 scalar-mult and ECDH mismatch every RFC 7748 KAT vector | `src/lib/common/crypto/typed/ctypes.spl:0` |
| dashboard_cli_stub_no_log_mode_support_2026-07-20 | P3 | open | dashboard app CLI is a no-op stub; log-mode spec tests removed functionality | `src/app/dashboard/main.spl:0` |
| dashboard_main_lost_table_model_2026-08-04 | P2 | open | app.dashboard.main no longer defines the table model its siblings import | `src/app/dashboard/main.spl:0` |
| direct_arch_imports_outside_arch_2026-08-11 | P2 | open | 7 modules outside arch/ import arch-family modules directly, violating AC-3 portability | `src/os/services/audio/audio_service.spl:29` |
| disk_image_builder_unbuildable_regression | P2 | open | os.port.disk_image fails semantic cannot iterate over this type and llc l5 name | `src/os/port/disk_image.spl:0` |
| di_test_tag_env_not_inherited_by_subprocess_2026-07-02 | P2 | open | Spawned test child never sees SIMPLE_DI_TEST=1, so the # @di_test tag cannot bypass the | `src/app/test_runner_new/test_runner_main.spl:695` |
| divergence_byte_char_find_option_sweep_2026-08-01 | P2 | open | find/rfind/index_of return a raw i64 -1 sentinel but are consumed as Option across src/** | `src/lib/common/text.spl:0` |
| draw_ir_8k_native_evidence_blocked_2026-08-12 | P2 | open | No native DrawIR 8K benchmark row obtainable: simple_native --version dies with SIGSEGV | `test/05_perf/graphics_2d/draw_ir_damage_8k_bench.spl:0` |
| duplicate_backend_types_terminal_declarations | P2 | open | Enums declared in multiple terminal modules with divergent variant orders are undetected | `src/compiler/70.backend/backend_types.spl:40` |
| duplicate_check_eager_semantic_native_closure_2026-07-24 | P2 | open | Native entry-closure pulls semantic/Ollama modules despite `use lazy`, failing link on | `src/compiler/90.tools/duplicate_check/main.spl:0` |
| duplicate_impl_method_definitions_silent_first_wins_2026-08-08 | P2 | open | Duplicate impl method definitions across files silently first-win with no dedup and no | `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:0` |
| duplicate_type_name_collision_audit_2026-07-17 | P2 | open | Flat global class/enum registries let same-named types in different modules collide at | `src/compiler/10.frontend/core/interpreter/eval_tables.spl:163` |
| dynsmf_session_spec_pinned_to_a_6_entry_manifest_that_grew_to_12_2026-08-04 | P2 | open | dynsmf_session_unload_reload_spec pins a 6-entry autoload manifest the product grew to 12 | `test/03_system/stdlib/dynload/dynsmf_session_unload_reload_spec.spl:0` |
| editor_jit_run_route_blockers_2026-05-28 | P2 | open | editor `bin/simple run` JIT route still blocked on item 2 (deferred), items 1/3 addressed | `src/app/editor/main.spl:0` |
| engine2d_draw_ir_free_function_state_visibility_2026-06-05 | P2 | open | Draw-IR executor free-function mutations are not visible to the caller | `src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl:0` |
| engine2d_vulkan_physical_display_8k_gate_2026-08-12 | P2 | open | Engine2D Vulkan 8K physical-display gate has never passed | `scripts/check/check-engine2d-vulkan-window-8k.shs:0` |
| engine3d_ext_impl_blocks_never_imported_2026-07-02 | P2 | open | engine3d *_ext.spl plain impl blocks are never imported, leaving trait impls incomplete | `src/lib/gc_async_mut/gpu/engine3d/engine.spl:0` |
| entry_closure_dedup_spec_red_on_origin_2026-07-30 | P2 | open | entry_closure_physical_source_dedup_spec.spl is red on origin (closure load parse + HIR... | `test/01_unit/compiler/bootstrap/entry_closure_physical_source_dedup_spec.spl:202` |
| entry_closure_runs_global_stdlib_pass_regardless_of_imports_2026-08-08 | P2 | open | native-build --entry-closure runs a fixed global stdlib pass no matter what the program... | `src/compiler/80.driver/driver.spl:0` |
| enum_bare_name_collision_registry_2026-08-01 | P1 | open | Pure-Simple named-type, interpreter enum, and MIR registries remain keyed by bare names; TypeId-scoped Rust MIR validation fixes only one consumer | `src/compiler/10.frontend/core/types.spl:735` |
| enum_discriminant_convention_split_hashed_seed_vs_positional_pure_simple_2026-08-08 | P2 | open | Rust seed hashes enum discriminants while pure-Simple uses positional index; nothing detects a mix | `src/compiler_rust/compiler/src/codegen/instr/result.rs:102` |
| env_gated_spec_switches_are_inert_under_test_daemon_2026-08-09 | P2 | open | Env vars set by the caller never reach the spec body under bin/simple test so gates fail open | `src/app/test_runner_new/test_runner_client.spl:0` |
| executable_checker_failed_only_retry_peak_rss_2026-08-02 | P3 | open | Failed-only executable-checker retry peaked at 40.6 GiB RSS across four workers | `src/lib/nogc_sync_mut/js/engine/interpreter_native.spl:0` |
| f64_self_hosted_call_result_codegen_2026-06-21 | P1 | open | f64 returned from a non-inlined function is corrupted in self-hosted cranelift codegen | `src/compiler/70.backend/backend/cranelift_codegen_adapter.spl:0` |
| fat32_microbench_jit_mut_capability_2026-05-27 | P2 | open | fat32_microbench segfaults / hits W1006 mutation-without-mut before entering Fat32Core.write | `test/05_perf/bench/fat32_microbench.spl:0` |
| freestanding_text_local_recompare_flips_material_admission_2026-08-10 | P2 | open | freestanding x86_64 text local re-comparison flips WM material admission; layers 1-2 only | `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core.spl:0` |
| freestanding_u64_cross_fn_range_compare_miscompile | P1 | open | freestanding native-build returns 0 from a u64 range helper for an argument provably in | `src/compiler/50.mir/mir_lowering_stmts.spl:0` |
| fs_exec_ring3_fork_unreachable_spawnwait_2026-08-06 | P2 | open | fork(57) is unreachable from ring-3 FS-exec because the process is never a scheduler Task | `src/os/kernel/loader/x86_64_fs_exec_ring3.spl:311` |
| full_bootstrap_blocked_rust_inputs_changed_concurrent_sessions_2026-08-15 | P2 | open | bootstrap-from-scratch exits 1 silently when invoked via a symlinked repo root (pwd vs | `scripts/bootstrap/bootstrap-from-scratch.sh:0` |
| gate_oracle_soundness_census_2026-08-11 | P3 | open | census of check scripts whose oracle is exit-code-only, so a silent no-op run reads as a | `scripts/check/check-jit-unresolved-symbol-guard.shs:0` |
| gc_async_mut_missing_facade_wrapper_modules_2026-07-20 | P2 | open | std.gc_async_mut.compression.lz4 and database.sql.escape resolve to nothing; no facade | `src/lib/gc_async_mut/__init__.spl:0` |
| generator_intensive_spec_shadows_generatorstate_variants_2026-08-10 | P3 | open | generator_intensive_spec declares its own GeneratorState so it tests a local model, not | `test/unit/lib/nogc_async_mut/generator_intensive_spec.spl:17` |
| gpu_compute_offload_not_wired_to_sffi_launch_2026-07-06 | P2 | open | std.compute offload always computes on CPU and only reports GPU provenance from an env | `src/lib/nogc_async_mut/compute/backend_dispatch.spl:0` |
| gpu_probe_then_create_toctou_2026-08-04 | P2 | open | GPU probe-then-create TOCTOU: probe answer is a prediction that does not survive to the | `src/lib/gc_async_mut/gpu/engine2d/engine.spl:0` |
| gpu_scheduler_diag_counter_readback_type_infer_2026-07-06 | P2 | open | Dict<text,i64>.get(k) ?? i64 infers the KEY type on first monomorphization and rejects | `src/lib/nogc_sync_mut/diag.spl:372` |
| guard_wiring_optout_false_exemptions_2026-08-06 | P2 | open | guard_wiring_optout.txt exempts 20+ gates on false reasons, hiding 8 RED and 2 fail-open | `scripts/check/guard_wiring_optout.txt:0` |
| gui_8k_native_renderer_artifact_build_timeout_2026-08-13 | P1 | open | Native renderer artifact build exceeds 30s bound so 8K/80 GUI rows report | `src/app/wm_compare/backend_measurement_software_export.spl:0` |
| gui_renderdoc_feature_coverage_spec_daemon_timeout_2026-06-28 | P3 | open | gui_renderdoc_feature_coverage_status_spec.spl times out under the SPipe test daemon | `test/03_system/check/gui_renderdoc_feature_coverage_status_spec.spl:0` |
| gui_web_2d_retained_metal_simd_wm_perf_evidence_gap_2026-07-06 | P2 | open | No retained Metal/SIMD WM perf evidence row exists for hosted WM or SimpleOS WM | `src/lib/gc_async_mut/gpu/engine2d/engine.spl:0` |
| gui_web_2d_vulkan_browser_backing_2026-06-23 | P2 | open | Electron reports hardwareSupportsVulkan=false and skiaBackendType=None so browser-backing | `scripts/setup/setup-gui-web-2d-vulkan-env.shs:0` |
| gui_web_2d_vulkan_renderdoc_blockers_2026-06-23 | P2 | open | RenderDoc .rdc capture gates for Simple/Electron/Chrome remain blocked with nonzero | `scripts/tool/renderdoc-evidence.shs:0` |
| gui_winit_window_not_registered_window_server_2026-07-06 | P2 | open | winit window composites on macOS but has no Aqua activation so clicks and drags never land | `scripts/gui/macos-gui-run.shs:0` |
| host_2d_vulkan_and_simd_spec_reds_2026-08-08 | P2 | open | Vulkan draw_rect_filled writes 0xAF828DFF at interior pixel (4,4) instead of the | `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl:0` |
| hosted_wm_glyph_oracle_uncalibratable_2026-08-01 | P2 | open | check-linux-hosted-wm-live-window-evidence.shs:18 still hard-fails on | `scripts/check/check-linux-hosted-wm-live-window-evidence.shs:18` |
| hosted_wm_runtime_dso_unadmitted_security_evidence_2026-07-29 | P2 | open | A bootstrap DSO copied from elsewhere can be presented with a caller-supplied matching | `scripts/check/check-linux-hosted-wm-live-window-evidence.shs:0` |
| host_toolchain_seed_pinned_lint_fmt_doccov_unrunnable_2026-07-17 | P1 | open | No pure-Simple binary can run lint/fmt/doc-coverage; seed treats doc-coverage as a script | `src/app/cli/_CliMain/main_and_help.spl:270` |
| host_vulkan_lavapipe_graphics_entry_points_stubbed_without_vulkan_feature_2026-08-11 | P1 | open | Vulkan graphics entry points return 0 with empty rt_vulkan_get_last_error because | `src/compiler_rust/runtime/Cargo.toml:19` |
| host_wm_cached_chrome_full_frame_blit_2026-07-06 | P3 | open | Host WM blits the entire cached desktop frame every repaint instead of dirty subrects | `src/os/compositor/host_compositor_entry.spl:0` |
| image_builder_nvfs_rootfs_marker_preexisting_2026-06-28 | P2 | open | image_builder nvfs rootfs backend marker assertion fails (pre-existing red) | `src/os/installer/image_builder.spl:0` |
| image_wrapper_close_needs_live_handle_fixture_2026-08-07 | P3 | open | Image/FileLock wrapper double-close on a genuinely-acquired handle has no test fixture | `src/lib/nogc_sync_mut/io/image_sffi.spl:0` |
| img_bxe_submit_encoder_envelope_only_no_kernel_uapi_verification_2026-08-11 | P3 | open | IMG BXE encoder submit builds envelope only; no kernel UAPI submission is verified | `src/os/drivers/gpu/board_vulkan/encoder_img_bxe.spl:0` |
| impl_to_free_fn_refactor_family_still_incomplete_2026-08-08 | P1 | open | impl-to-free-fn refactor left ~40 zero-definition call sites in live compiler passes | `src/compiler/00.common/predicate_parser.spl:0` |
| indexed_char_to_i64_silent_zero_family_2026-08-10 | P1 | open | String indexing still returns STRING, leaving digit-character to_i64 ambiguous (7 instead of codepoint 55) after non-digit fallback was fixed | `src/compiler_rust/compiler/src/hir/lower/expr/index.rs:0` |
| interp_class_name_collision_breaks_test_db_persistence_2026-08-10 | P2 | open | Interpreter resolves a class by name across modules, breaking test-DB run persistence | `src/compiler/10.frontend/core/interpreter/eval_tables.spl:0` |
| interp_compositor_backend_put_pixel_clones_framebuffer_2026-07-03 | P2 | open | CompositorBackend.put_pixel clones the entire framebuffer on every pixel write | `src/compiler_rust/compiler/src/interpreter_method/collections.rs:0` |
| interp_index_of_digit_leading_literal_2026-07-22 | P1 | open | Flat i64? optional lane collides with tagged values; payload 3 reads as nil in seed JIT | `src/runtime/runtime_native.c:0` |
| interp_module_global_stale_read_in_spec_blocks_2026-07-05 | P2 | open | Module global read inside a spec block returns a stale value | `src/lib/nogc_sync_mut/diag.spl:0` |
| interpreter_bdd_missing_structured_test_evidence_2026-07-19 | P2 | open | Pure-Simple BDD consumer still cannot authenticate interpreter results via --assert-ran | `src/lib/nogc_sync_mut/spec.spl:0` |
| interpreter_binding_class_typed_field_snapshots_instead_of_aliasing_2026-08-10 | P1 | open | Binding a class-typed field to a local snapshots it instead of aliasing (interpreter only) | `src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs:0` |
| interpreter_bytes_u64_false_green_memory_2026-08-11 | P2 | open | Interpreter byte allocation reports a U64 false-green and blows up memory on 1MiB push bench | `src/compiler_rust/compiler/src/value.rs:0` |
| interpreter_eval_access_calls_drifted_duplicate_definitions_2026-08-11 | P2 | open | Ten drifted duplicate interpreter fn definitions exist and the STALE copies win name resolution | `src/compiler/80.driver/driver_source_loading.spl:0` |
| interpreter_module_array_stale_read_via_free_fn_helper_2026-07-29 | P1 | open | Instance method reads a stale module-level array through a free-function helper (interpreter) | `src/lib/nogc_async_mut/async/cancellation.spl:0` |
| interpreter_pending_skip_dsl_intercept_bypasses_spl_body_2026-08-07 | P2 | open | Rust seed interpreter intercepts pending/skip_it/skip before the .spl body in spec.spl ever runs | `src/compiler_rust/compiler/src/interpreter_call/bdd.rs:0` |
| interpreter_result_match_return_sigsegv_2026-07-17 | P2 | open | RunningType::Interpreter SIGSEGVs on a match over a Result with a return inside an arm | `src/compiler_rust/compiler/src/interpreter_call/block_execution.rs:0` |
| interpreter_struct_in_dict_with_closure_field_reads_nil_2026-08-10 | P2 | open | Struct stored in a Dict reads back nil on a field that has a closure-typed sibling field | `src/lib/nogc_async_mut/actors/actor.spl:0` |
| interp_use_as_alias_not_visible_in_function_body_2026-07-20 | P2 | open | Module-level use <module> as <alias> is not resolvable inside a function body: variable <alias> not found | `src/compiler/90.tools/verify/checker.spl:0` |
| is_nil_is_not_a_language_builtin_2026-07-27 | P2 | open | is_nil is not a language builtin and fails on every ordinary receiver, differently per engine | `src/compiler/70.backend/backend_types.spl:0` |
| iso_borrow_check_unreachable_from_interpret_pipeline_2026-08-09 | P2 | open | iso/borrow-check pass is unreachable from the interpret pipeline so bin/simple test never runs it | `src/compiler/80.driver/driver_pipeline_passes.spl:0` |
| isolated_thread_raw_worker_argument_heuristic_flake_2026-08-12 | P2 | open | Isolated-thread raw worker argument heuristic is test-order dependent (flaky) | `src/runtime/runtime_thread.c:0` |
| iterator_collect_generic_restoration_2026-07-17 | P3 | open | Iterator.collect loses its generic type parameter and needs restoration across the three vec types | `src/compiler_rust/lib/std/src/core/list.spl:0` |
| jit_class_mutation_drop_characterization_2026-07-04 | P1 | open | Mutations to class instances read out of an array are silently dropped in interpret mode | `src/compiler/70.backend/backend/mod.spl:0` |
| jit_closure_abi_refuses_lambdas_and_miscompiles_fn_refs_2026-08-06 | P2 | open | JIT refuses whole module containing a lambda, demoting it to the interpreter | `src/compiler_rust/compiler/src/codegen/jit.rs:0` |
| jit_corrupts_i64_array_returned_from_sha1_bytes_2026-08-04 | P1 | open | JIT returns tag-corrupted [i64] from sha1_bytes: floats/nil/heap tags inside an i64 list | `src/compiler_rust/compiler/src/codegen/instr/methods.rs:0` |
| jit_dispatch_worklist_2026-07-29 | P3 | open | JIT builtin-method dispatch worklist: text.reverse arm is a no-op, rt_string_reverse does not exist | `src/compiler_rust/compiler/src/codegen/instr/methods.rs:0` |
| jit_layout_run_full_with_ports_nil_receiver_2026-08-02 | P1 | open | layout_run_full_with_ports core-dumps on nil-receiver field access under JIT | `src/lib/gc_async_mut/gpu/browser_engine/gpu_web/layout/cuda_execution_port.spl:0` |
| jit_lowering_clamp_f_engine_color_2026-07-02 | P3 | open | JIT lowering cannot resolve a nested fn inside an impl method (Unknown variable: clamp_f) | `src/lib/common/engine/color.spl:0` |
| jit_lowering_module_alias_and_panic_2026-07-02 | P2 | open | JIT HIR lowering rejects module-alias references and the panic intrinsic, forcing interpreter fallback | `src/compiler_rust/compiler/src/hir/lower/expr/mod.rs:0` |
| jit_strict_coverage_gap_2026-07-30 | P2 | open | SIMPLE_JIT_STRICT fails open on unresolved globals: lowering proceeds and the error only surfaces at call time | `src/compiler_rust/driver/src/exec_core.rs:0` |
| jit_struct_assignment_aliases_not_copies_2026-08-10 | P2 | open | JIT struct assignment aliases instead of copying; interpreter copies (residual cases after 2026-08-10) | `src/compiler_rust/compiler/src/mir/lower/lowering_stmt.rs:0` |
| jit_test_suite_blind_spot_2026-07-30 | P3 | open | Spec suite runs only one engine, so JIT-only divergences are structurally invisible to it | `scripts/check/check_jit_interpreter_differential.spl:0` |
| jit_text_repeat_dispatch_and_silent_error_substitution_2026-08-01 | P2 | open | JIT text-method dispatch gap substitutes the literal string 'error'; 2 of 51 sibling methods still unwired | `src/compiler_rust/compiler/src/codegen/instr/methods.rs:0` |
| js_engine_es2015_parser_gaps_2026-07-05 | P2 | open | JS engine es2015 conformance: 13 of 38 cases fail on parser gaps | `src/lib/nogc_sync_mut/js/engine/parser.spl:0` |
| js_engine_missing_builtins_regex_promise_prototype_2026-07-11 | P2 | open | JS engine String.replace with a regex is a silent no-op | `src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl:0` |
| js_engine_no_dom_bom_globals_2026-07-11 | P2 | open | JS engine binds no DOM/BOM globals, so real-page DOM JS silently no-ops | `src/lib/gc_async_mut/gpu/browser_engine/script/script_runner.spl:0` |
| js_subset_interpreter_limitations_2026-06-30 | P3 | open | Browser-session JS subset interpreter gaps worked around in the ES-module transform instead of the engine | `src/lib/gc_async_mut/web/browser_session_modules.spl:0` |
| js_vm_dom_bridge_retention_quadratic_2026-07-30 | P2 | open | JS VM DOM bridge retention is frame-linear and property scan is quadratic | `src/lib/nogc_sync_mut/js/engine/vm_object_store.spl:0` |
| kv260_ps_bd_pl_clk0_unreachable_jtag_bringup_2026-07-24 | P2 | open | KV260 PS block-design pl_clk0/pl_resetn0 are unreachable in JTAG-only bring-up | `scripts/fpga/build_k26_rv32.shs:0` |
| kv260_rv32_fabric_uart_not_routed_golden_is_sim_2026-07-25 | P2 | open | rv32 soak fabric UART (H12/PMOD J2) is unrouted so board golden 0x7EB5A8A9 is sim-only | `scripts/fpga/soak_rv32_board.shs:0` |
| layoutglyph_struct_array_i64_field_tag_shift_readback_2026-07-20 | P2 | open | LayoutGlyph struct-in-array i64 fields read back tag-shifted on freestanding native lane | `src/lib/nogc_sync_mut/text_layout/font_renderer.spl:0` |
| layout_gpu_semantic_device_boundary_2026-07-31 | P3 | open | GPU layout semantic/device boundary only partially completed (bounded device slices) | `src/lib/gc_async_mut/gpu/browser_engine/layout_paint.spl:0` |
| lean_parser_bitwise_pipe_precedence_divergence_2026-06-11 | P3 | open | Lean-exported parser gives bitwise-or and pipe operators divergent precedence vs parser_expr.spl | `src/compiler/10.frontend/core/parser_expr.spl:0` |
| legacy_import_string_namespace_dict_ignores_source_content_2026-08-11 | P2 | open | import string builds a namespace dict that ignores src/lib/string.spl contents (char_at missing) | `src/lib/string.spl:0` |
| legacy_mcp_feature_tests_target_removed_api_and_assert_nothing_2026-08-04 | P3 | open | MCP bootstrap feature tests import a removed api_tools API and assert nothing (vacuous green) | `test/03_system/feature/lib/mcp/bootstrap_e2e_test.spl:0` |
| lib_specs_import_133_modules_that_do_not_exist_2026-08-04 | P3 | open | 199 lib specs import 133 std.* modules that exist nowhere in the tree | `test/01_unit/lib/math/bignum/bignat_spec.spl:0` |
| lint_native_fast_path_activation_blocked_seed_uncompilable_2026-08-07 | P2 | open | lint native fast path landed but never activated; seed rebuild blocked by pre-existing E0425s | `scripts/build/build-lint-native.shs:0` |
| lint_single_file_superlinear_timeout_on_line_count_2026-08-06 | P2 | open | bin/simple lint cost is superlinear in line count (~3.3-4.0s per fn decl), 120-line file ~119s | `src/compiler/90.tools/lint/main.spl:0` |
| linux_secure_server_perf_runtime_blockers_2026-08-14 | P2 | open | Native PureDatabase fails first post-insert check with invalid-array-handle; HTTP server installs no listener | `src/app/postgres_mimic_server/main.spl:0` |
| list_first_returns_raw_value_not_option_2026-07-20 | P2 | open | List<T>.first returns a raw nilable value instead of Option<T> as documented | `src/compiler_rust/compiler/src/interpreter_method/collections.rs:139` |
| llm_caret_codex_app_server_piped_stdio_2026-08-02 | P3 | open | codex app-server --listen stdio:// spawned via app.io piped façade dies before first response | `src/app/llm_caret/messaging/cli.spl:0` |
| llm_caret_compiled_carrier_build_latency_2026-08-02 | P2 | open | LLM Caret compiled carrier link fails on unresolved stdlib symbols (trim/starts_with/unwrap_err) | `src/app/llm_caret/messaging/hook_worker.spl:0` |
| llm_caret_http_attempt_timeout | P2 | open | http_request_raw has no timeout parameter so with_retry cannot cancel a blocked transport | `src/lib/nogc_sync_mut/io/http_sffi.spl:184` |
| llm_caret_index_of_optioni64_tagbox_2026-07-07 | P2 | open | text.index_of returns nil for a present substring (Option<i64> tag-box mangled) | `src/app/llm_caret/json_helpers.spl:0` |
| llm_caret_native_closure_admission_2026-08-11 | P2 | open | LLM Caret native closure admission fails on missing artifacts and unresolved Caret ABI symbols | `scripts/check/check-llm-caret-native-closure.shs:0` |
| llm_strict_host_completion_blockers_2026-06-29 | P3 | open | LLM strict-host prereq doctor and live-HTTP evidence gates remain incomplete | `scripts/check/check-llm-strict-host-prereq-doctor.shs:0` |
| llvm_backend_yield_silent_noop_2026-07-19 | P3 | open | LLVM codegen matches MirInst::Yield to an empty arm, emitting no code for a yield | `src/compiler_rust/compiler/src/codegen/llvm/functions.rs:1668` |
| llvm_import_path_mangling_os_prefix_mismatch_2026-06-15 | P1 | open | rv64 cross-module calls reference os__kernel__ names while definitions emit bare/weak symbols, link fails | `src/compiler_rust/compiler/src/pipeline/native_project/imports.rs:0` |
| llvm_sys_pinned_to_18x_blocks_newest_msvc_llvm_2026-08-09 | P3 | open | llvm-sys pinned to 18.x prevents building against newer MSVC-built LLVM | `src/compiler_rust/compiler/Cargo.toml:0` |
| lsp_code_action_edit_emit_parse_mismatch_2026-06-16 | P2 | open | LSP code-action edits never apply: emitter output does not round-trip through the edit parser | `src/lib/nogc_sync_mut/lsp/lsp_handlers.spl:0` |
| lsp_mcp_server_process_leak_2026-07-05 | P2 | open | simple-lsp-mcp leaves orphaned server processes with no cleanup (48 observed) | `src/app/simple_lsp_mcp/main.spl:0` |
| macos_full_cli_gui_admission_process_proof_2026-07-27 | P3 | open | macOS GUI admission source contracts pass; live Endpoint Security signing evidence remains unavailable (exit 125) | `scripts/check/build-macos-es-history-collector.shs:0` |
| macos_vulkan_2d_vector_font_empty_batch_native_fault_2026-07-26 | P2 | open | Vulkan 2D vector-font path faults natively on an empty draw batch | `src/os/compositor/host_compositor_core.spl:0` |
| mangler_bare_extern_sibling_split_part_2026-07-30 | P2 | open | Seed mangler emits a bare extern for a free fn shared across sibling split-part modules behind a facade | `src/compiler_rust/compiler/src/pipeline/native_project/mangle.rs:0` |
| map_insert_if_absent_missing_and_map_new_resolves_to_dict_2026-07-20 | P2 | open | Map.new() resolves to a plain dict rather than the Map<K,V> struct due to module-graph shadowing | `src/lib/nogc_sync_mut/src/map.spl:325` |
| markers_module_unparseable_and_spec_drift_2026-07-28 | P3 | open | os.kernel.log.markers does not define NAMESPACE_BOOT that its spec imports | `src/os/kernel/log/markers.spl:0` |
| match_on_enum_native_lowering_status_2026-08-07 | P2 | open | Payload-bearing enum match is still wrong under --native (LLVM AOT); payload-free is fixed | `src/compiler_rust/compiler/src/pipeline/execution.rs:0` |
| match_on_optional_enum_variant_falls_to_wildcard_2026-08-07 | P1 | open | match on an Option<enum> value falls through to the wildcard arm instead of the matching variant | `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:0` |
| mcp_config_raw_source_launch_and_stale_startup_lib_2026-08-11 | P3 | open | MCP server family: obsolete source/SMF startup library deleted and guarded; POSIX T32 wrapper artifacts remain missing | `src/app/simple_lsp_mcp/main.spl:0` |
| mcp_full_program_native_codegen_and_arg_extract_2026-06-16 | P1 | open | Bootstrap stage4 produces a broken full CLI (defect C) and a portability defect D remains | `src/app/cli/main.spl:0` |
| mcp_stdio_interpreter_gate_exceeds_cpu_guard_2026-08-10 | P2 | open | MCP stdio interpreter gate exceeds the CPU guard; rt_file_is_char_device unresolved | `src/compiler/80.driver/driver_source_pipeline_loading.spl:0` |
| me_method_mutation_through_optional_binding_discarded_2026-08-04 | P1 | open | `me`-method mutation through an Option-typed binding is silently discarded (exit 0, no warning) | `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:3124` |
| mem_guard_owner_attribution_trap_report_missing_2026-08-05 | P3 | open | M2 guard-page SIGSEGV trap produces no owner-attribution report on either backend | `src/compiler_rust/compiler/src/interpreter_extern/mem_guard.rs:0` |
| mem_infra_parity_specs_cranelift_arm_demotes_to_interpreter_2026-08-09 | P2 | open | guard/harden backend-parity specs cranelift arm silently demotes to interpreter so cranelift is never measured | `test/01_unit/lib/mem_infra/guard_backend_parity_spec.spl:0` |
| mir_lowering_new_spec_preexisting_failures_2026-08-08 | P2 | open | mir_lowering_new_spec.spl has 19 of 34 examples failing against switch_operators_calls lowering (pre-existing, not a regression) | `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:0` |
| mir_qualified_field_key_namespace_mismatch_2026-08-08 | P1 | open | MIR qualified struct-field key namespace mismatch makes b9e23914a0e new tier a no-op across an import boundary | `src/compiler/50.mir/_MirLowering/function_lowering.spl:0` |
| mir_runtime_call_origin_ambiguity_2026-07-17 | P2 | open | MIR cannot distinguish source calls from compiler-generated runtime calls, colliding generic call origins | `src/compiler/50.mir/_MirLowering/function_lowering.spl:0` |
| missing_cover_annotation_aborts_the_entire_system_test_run_2026-08-04 | P1 | open | A single system spec lacking a # @cover annotation aborts the whole run, so 488 specs in three directories never execute | `src/app/test_runner_new:0` |
| mission_critical_infra_hardening_v2_wave1_red_2026-08-11 | P2 | open | Mission-Critical Infra Hardening V2 Wave 1 is RED across compiler_admission, draw_ir arena v3 and sosix certified_manifest specs | `test/01_unit/compiler/mission_critical/compiler_admission_spec.spl:0` |
| mlkem_ntt_simd_public_interface_probe_crashes_not_pass_2026-08-05 | P2 | open | AC-4 SIMD byte-identity probe crashes on reproduction and the named .spl probe file was never created, so the reported PASS is unsupported | `src/compiler_rust/runtime/src/value/simd_int_ops.rs:0` |
| ml_kem_postfix_to_equal_chained_call_not_found_2026-07-20 | P2 | open | Postfix .to_equal() matcher is unresolved when the receiver is a chained call, blocking ML-KEM algebraic assertions | `src/compiler_rust/lib/std/src/spec/matchers.spl:0` |
| model3d_mut_engine_free_fn_six_dynamic_args_drops_mutation_2026-07-11 | P1 | open | A free-function call taking mut Engine3D silently drops all mutation once 6 or more sibling args are dynamic, rendering empty geometry | `src/app/model3d/main.spl:0` |
| module_load_24s_unless_window_winit_imported_2026-07-25 | P2 | open | Importing std.gpu.engine2d.engine costs 24s unless std.io.window_winit is also imported which drops it to 3s | `src/lib/gc_async_mut/gpu/engine2d/engine.spl:0` |
| module_loader_spec_load_count_and_unload_state_2026-07-20 | P2 | open | ModuleLoader load/unload bookkeeping diverges from documented behavior (13 spec failures incl. resolved-symbol-count) | `src/compiler/99.loader/module_loader.spl:0` |
| module_lowering_byte_vs_char_sanitizer_2026-08-01 | P3 | open | module_lowering path sanitizer counts bytes not chars, miscounting non-ASCII module paths | `src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:0` |
| module_named_like_its_class_shadows_it_inside_it_blocks_2026-08-04 | P2 | open | A module whose basename equals its class name shadows the class inside sspec it blocks (64 failing examples) | `src/compiler/99.loader/module_loader.spl:0` |
| module_namespace_member_call_in_spec_it_block_2026-07-27 | P2 | open | Module-namespace member call fails inside an sspec it block due to implicit-self injection in it-block closures | `src/compiler/10.frontend/core/parser.spl:0` |
| multiarch_boot_evidence_never_produced_2026-08-04 | P3 | open | Multi-arch AC-4/AC-6 specs assert on QEMU boot evidence no lane produces; the --arch dispatch flag they call does not exist | `test/03_system/os/multiarch/six_arch_boot_spec.spl:0` |
| mutex_rwlock_text_value_nulled_by_pure_std_backend_2026-07-28 | P1 | open | Mutex/RwLock silently null non-int/float/bool values (text) under the default PureStd concurrent backend | `src/compiler_rust/compiler/src/concurrent_providers/mod.rs:0` |
| mut_param_annotation_no_reference_propagation_2026-07-20 | P2 | open | fn f(x: mut i64) mutating x does not propagate the write back to the callers variable | `src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:0` |
| native_array_map_text_provenance_2026-07-19 | P3 | open | Native array map loses text ownership and provenance on the mapped result | `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:0` |
| native_bool_result_int_render_and_to_string_gap_2026-07-17 | P2 | open | Native path prints bool-returning string methods as 1/0 and .to_string() on primitives is unresolved outside SIMPLE_BOOTSTRAP=1 | `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:3133` |
| native_build_cache_scope_key_renders_corrupt_persistent_cache_2026-08-08 | P2 | open | Persistent native-build cache has no GC, leaking unbounded disk on an already 95%-full volume | `src/compiler/80.driver/driver_build/incremental.spl:198` |
| native_build_cross_module_result_payload_struct_name_collision_2026-08-09 | P2 | open | Cross-module Result<T,E> payload struct-name recovery collides or misses across modules (6th layer still open) | `src/lib/nogc_sync_mut/io/file.spl:0` |
| native_build_cross_module_trait_only_and_unimported_method_gaps_2026-07-17 | P2 | open | native-build fails with unresolved method call for trait-only and unimported cross-module methods (lowered to const-0 placeholder) | `src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:0` |
| native_build_entry_closure_slow_2026-07-31 | P3 | open | --entry-closure BFS averages 1-2s per file, dominating native-build wall time | `src/app/io/_CliCompile/compile_targets.spl:0` |
| native_build_nested_replace_method_resolution_2026-07-26 | P2 | open | Stage4 compiler cannot resolve .replace(...) on an erased receiver in nested call context | `src/lib/nogc_sync_mut/database/pure_sql/_PureDatabase/row_value_helpers.spl:0` |
| native_build_reports_success_for_functionless_artifact_2026-08-10 | P1 | open | native-build exits success for an artifact containing zero emitted functions | `src/compiler_rust/driver/src/cli/native_build.rs:0` |
| native_build_self_hosted_mir_infer_type_crash_2026-07-30 | P2 | open | self-hosted native-build crashes on module-level globals with a binary-expression initializer | `src/compiler/20.hir/hir_lowering/expressions.spl:0` |
| native_cache_mir_fingerprint_prerequisite_blocked_2026-08-02 | P2 | open | Native-cache MIR fingerprint is not representable, so cache correctness cannot be validated | `src/compiler/80.driver/driver_build/incremental.spl:0` |
| native_class_array_field_mutation_segfault_2026-07-17 | P2 | open | Class array-field mutation via .push()/index-assign segfaults on the bootstrap-seed JIT path | `src/compiler_rust/compiler/src/mir/lower/lowering_expr_struct.rs:0` |
| native_cli_run_std_hardware_brace_import_unresolved_2026-07-24 | P2 | open | bin/simple run leaves brace-imports from std.hardware.* unresolved (transport_sim_loopback, tap_create, CH_JTAG) | `src/app/io/cli_ops.spl:0` |
| native_empty_dict_text_value_sigsegv_2026-07-20 | P1 | open | A text value stored into an empty-literal {} dict SIGSEGVs on read or compare under native-build | `src/runtime/runtime_native.c:8008` |
| native_entry_closure_common_import_type_loss_2026-07-27 | P2 | open | Entry-closure build loses declared types on symbols imported from common modules (draw_ir into draw_ir_adv) | `src/lib/common/ui/draw_ir.spl:0` |
| native_entry_closure_struct_return_by_value_fields_read_as_one_2026-08-17 | P1 | open | Struct returned by value reads every field as 1 under native-build --entry-closure | `src/compiler/20.hir/hir_lowering/_Items/declaration_lowering.spl:0` |
| native_env_closure_unsupported_methods_2026-07-16 | P2 | open | native-build of a std.env closure fails: array/text methods unsupported in MIR lowering | `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:0` |
| native_exists_check_struct_payload_becomes_bool_2026-07-25 | P2 | open | Native ExistsCheck uses its presence boolean as the struct payload for optional.?.field | `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:0` |
| native_first_class_lambda_values_unsupported_2026-07-11 | P2 | open | CallIndirect through a non-inlined first-class lambda value fails on the native path | `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:0` |
| native_inlined_option_return_representation_mismatch_2026-08-02 | P1 | open | Inlined Option return uses a different representation than the caller expects on native | `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:0` |
| native_interp_logical_and_or_llc_type_mismatch_2026-07-16 | P2 | open | Interpolating '{a() and b()}' fails llc with a ptr vs i64 type mismatch on strict-llvm | `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:0` |
| native_isel_and_c_backend_tuple_field_type_reconciliation_gap_2026-08-08 | P2 | open | Native isel lanes mis-reconcile float tuple/struct field types (register-class gap) | `src/compiler/70.backend/backend/_CBackendTranslate/instruction_lowering.spl:0` |
| native_jit_crypto_tls13_pbkdf2_no_extern_c_implementation | P3 | open | TLS1.3/PBKDF2/Ed25519 runtime symbols in the ABI list have no extern C impl | `src/compiler_rust/common/src/runtime_symbols.rs:0` |
| native_method_text_return_prints_handle_2026-07-16 | P2 | open | Method returning text prints a raw handle integer instead of the string on non-llvm lanes | `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:0` |
| native_module_var_text_global_type_mismatch_2026-07-16 | P2 | open | Module-level text global var s = empty emits 'global i64 <ptr>' and llc fails | `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl:0` |
| native_new_keyword_identifier_silent_wrong_value_2026-07-17 | P2 | open | 'new' used as a plain identifier gives the wrong value and SIGSEGVs as a method arg | `src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl:0` |
| native_object_cache_whole_build_fingerprint_granularity_2026-08-02 | P3 | open | Native object cache invalidates the whole build when any compiler byte changes | `src/compiler_rust/driver/src/cli/native_build.rs:0` |
| native_primitive_to_i64_ufcs_collision_2026-07-24 | P2 | open | Primitive to_i64 collides with an imported custom to_i64 method under native lowering | `src/lib/nogc_sync_mut/failsafe/core.spl:0` |
| native_scalar_spill_clobber_loop_intervening_calls_2026-07-20 | P2 | open | Freestanding native: outer-scope scalar vals read corrupted in a while loop with calls | `src/lib/common/ui/window_scene_draw_ir.spl:0` |
| native_selfhosted_run_segfault_startup_normalize_2026-07-24 | P1 | open | Deployed self-hosted bin/simple segfaults on run/test/native-build at startup normalize | `src/app/cli/bootstrap_main.spl:0` |
| native_slice_splits_utf8_three_divergent_policies_2026-08-01 | P2 | open | Mid-codepoint text slicing has three divergent policies, one emitting invalid UTF-8 | `src/runtime/runtime_native.c:0` |
| native_spl_lane_runtime_c_legacy_value_representation_divergence | P3 | open | native.spl lane compiles legacy runtime.c while the Rust lane compiles runtime_native.c | `src/app/compile/native.spl:0` |
| native_theme_package_aggregate_return_nil_2026-07-24 | P2 | open | Native theme-package aggregate return value comes back nil in theme_sync compile-to-spl | `src/app/cli/theme_sync.spl:0` |
| native_trait_typed_return_receiver_unresolved_2026-08-09 | P2 | open | native-build MIR lowering fails when a trait-typed return value is used as a method rece | `test/fixtures/native_trait_receiver_resolution/main.spl:0` |
| native_try_op_on_option_silent_wrong_2026-07-14 | P1 | open | ? applied to an Option inside a Result-returning fn silently miscompiles (rc 208 vs 209) | `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:0` |
| native_tuple_spill_clobber_across_call_2026-07-19 | P2 | open | Native tuple stack spill clobbered by intervening method call; derefs ASCII text as poin | `src/lib/nogc_sync_mut/sffi/spl_fonts.spl:0` |
| native_with_trait_impl_no_vtable_duck_trap_2026-07-28 | P1 | open | class X with Trait registers no vtable; native trait calls execute ud2 and trap | `src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs:0` |
| native_zero_arg_method_receiver_not_marshalled_2026-07-19 | P2 | open | Zero-arg method call reads wrong object or nil receiver (cr2=0) in Engine2D._draw_font_b | `src/lib/gc_async_mut/gpu/engine2d/engine.spl:0` |
| nested_fn_cannot_mutate_enclosing_it_block_var_2026-08-04 | P2 | open | Nested fn assigning an enclosing it-block var does not update it; compound assign says v | `src/compiler_rust/compiler/src/interpreter/expr/control.rs:0` |
| nested_fn_in_spec_block_loses_captured_local_2026-08-04 | P1 | open | Nested fn inside a spec it block does not capture block locals: silently reads zero | `src/compiler_rust/compiler/src/interpreter/expr/control.rs:0` |
| network_coverage_illusion_and_spec_tree_duplication_2026-08-05 | P3 | open | Network e2e specs assert on source-text substrings, not sockets; spec tree duplicated 5, | `src/lib/nogc_sync_mut/io/tcp.spl:0` |
| no_general_spl_to_svmg_path_blocks_dap_gpu_attach_2026-08-09 | P3 | open | lower_svmg_program has no callers outside 70.backend so DAP GPU attach is routing-only | `src/compiler/70.backend/svmg_lowering.spl:0` |
| non_discriminating_spec_family_2026-08-08 | P2 | open | Enumerated family of vacuous specs that pass regardless of implementation behavior | `scripts/check/check-vacuous-specs.shs:0` |
| no_self_hosted_binary_deployed_blocks_bootstrap_gate_2026-08-09 | P1 | open | check-bootstrap-essential-tools-smoke.shs fails on a clean tree with error=rust_seed_bin | `scripts/check/check-bootstrap-essential-tools-smoke.shs:0` |
| notebook_cuda_exec_jit_lane_not_implemented_2026-08-08 | P3 | open | CudaExec cannot back jit(remote(cuda(...))) cells: no per-cell PTX compile path exists | `src/lib/nogc_sync_mut/notebook/cuda_exec.spl:0` |
| nvme_fw_rv64_direct_build_timeout_2026-07-07 | P2 | open | fw_rv64/build.shs native-build terminates before emitting an ELF at 120s timeout | `examples/09_embedded/simpleos_nvme_fw/fw_rv64/build.shs:0` |
| nvme_rv32_firmware_build_timeout_2026-07-05 | P2 | open | rv32 firmware wrapper times out before producing build/nvme_fw_rv32.elf | `scripts/check/check-nvme-rv32-minimal-live.shs:0` |
| on_is_an_undocumented_reserved_word_2026-08-02 | P3 | open | val on = ... fails to parse because 'on' is a hard keyword, with an error that never nam | `src/compiler_rust/parser/src/lexer/identifiers.rs:329` |
| option_pattern_accepted_on_non_option_scrutinee_2026-07-27 | P1 | open | Some(_) patterns and .unwrap_or are silently accepted on non-Option values; engines disa | `src/compiler/10.frontend/core/interpreter/eval_calls.spl:0` |
| os_crypto_jit_unresolved_symbol_rootcause_2026-07-30 | P2 | open | Any probe against os.crypto.* triggers a module-wide 'unresolved external symbol' JIT fa | `src/compiler_rust/compiler/src/codegen/jit.rs:0` |
| os_namespace_uninitialized_array_module_var_not_found_2026-08-02 | P2 | open | Module-level uninitialized array var is unresolvable in the os.* namespace only | `src/compiler_rust/compiler/src/interpreter/node_exec.rs:0` |
| parse_claude_json_response_name_collision_2026-07-20 | P2 | open | parse_claude_json_response defined in two modules; registry mis-dispatch fails 8 examples | `src/lib/nogc_async_mut/llm/claude_cli.spl:0` |
| parse_family_strips_option_jit_native_2026-08-02 | P1 | open | parse_i64/parse_f64 text-method family silently strips the Option under JIT and native | `src/compiler_rust/compiler/src/interpreter_method/string.rs:0` |
| placeholder_lambda_as_fn_param_callback_unevaluated_2026-07-20 | P1 | open | Placeholder lambda (_1 + 1) passed to a user free-function param is never invoked | `src/lib/nogc_async_immut/combinators/__init__.spl:0` |
| prelude_builtins_rebindable_by_transitive_import_2026-08-10 | P2 | open | 50 prelude builtins beyond `exit` remain silently shadowable by a transitive top-level fn | `src/compiler_rust/compiler/src/interpreter_call/mod.rs:0` |
| prevention_mock_deferred_arming_impossible_2026-08-07 | P3 | open | std.spec prevent/prevent_at_most cannot defer arming; no module state across it examples | `src/lib/nogc_sync_mut/spec.spl:0` |
| primitive_api_lint_ac_d1_and_ac_d2_are_contradictory_2026-08-04 | P3 | open | primitive_api lint AC-D1 and AC-D2 demand opposite verdicts on the same signature shape | `src/compiler/90.tools/fix/rules/impl_/lint_primitive_api.spl:160` |
| primitive_receiver_trait_impl_dispatch_2026-08-07 | P1 | open | Trait impl on primitive Self honoured only by interpreter; JIT fails open, native SIGSEGVs | `src/compiler/35.semantics/resolve_strategies.spl:0` |
| private_symbol_collision_sshd_four_names_2026-07-28 | P2 | open | Private cross-module symbol collision mis-dispatches silently under JIT; C1/C2 not landed | `src/compiler/35.semantics/resolve.spl:0` |
| process_transfer_session_replay_identity_2026-08-12 | P2 | open | Transfer session identity uses FNV-1a over 31 PID bits, which is not authentication | `test/03_system/feature/language/parent_commit_piped_result_spec.spl:0` |
| project_statistics_selfhosted_generation_blocked_2026-08-13 | P3 | open | bin/simple stats --quality=summary refuses to run because the binary is the Rust seed | `src/app/stats/db_aggregator.spl:0` |
| promise_new_push_reassign_same_scope_as_nested_closure_2026-07-29 | P1 | open | Module-array push+reassign reads stale when the same fn also defines a nested closure | `src/lib/nogc_async_mut/async/promise.spl:0` |
| provider_loader_path_digest_toctou_2026-08-16 | P2 | open | provider_admit_dynamic_v1 hashes the declared path then reopens it, so digest is not | `src/os/smf/provider_loader.spl:148` |
| pure_nn_layers_mix_autograd_tensor_and_puretensor_2026-07-25 | P2 | open | std.pure.nn Linear.forward mixes autograd Tensor with raw PureTensor so it cannot be | `src/lib/gc_async_mut/pure/nn.spl:43` |
| pure_simple_ctype_perf_gap_2026-05-18 | P3 | open | Pure-Simple ctype predicates run 0.07x-0.46x of C under Cranelift with no inlining | `src/lib/common/ctype.spl:0` |
| pure_simple_hir_untyped_return_tuple_2026-07-31 | P2 | open | Cache-free pure-Simple execution of a dynamic frontend-to-HIR path crashes on an untyped | `test/01_unit/compiler/backend/vulkan_source_storage_buffer_abi_spec.spl:0` |
| pure_simple_provider_host_runtime_capsule_link_required_2026-08-14 | P2 | open | Pure Simple provider host proof needs an admitted runtime capsule; --export-dynamic on | `src/os/smf/provider_loader.spl:0` |
| redeploy_out_simple_stage2_stale_missing_landed_fix_markers_2026-08-10 | P3 | open | build/redeploy_out/simple_stage2 lacks marker strings for two already-landed fixes | `scripts/check/check-compiler-provenance.shs:0` |
| renderdoc_electron_html_gate_spec_daemon_timeout_2026-06-28 | P3 | open | renderdoc_electron_html_gate_spec.spl times out under the SPipe test daemon though the | `test/03_system/check/renderdoc_electron_html_gate_spec.spl:0` |
| resource_borrow_pinning_not_enforced_2026-08-07 | P2 | open | borrow_graph.record_move checks only moved_now, never borrows_of, so borrow pinning | `src/compiler/55.borrow/borrow_check/borrow_graph.spl:0` |
| resource_decl_and_sffi_attribute_not_parsed_2026-08-07 | P2 | open | resource_sffi_pilot_spec stays RED for a structural reason after WP-A landed the | `test/01_unit/compiler/resource/resource_sffi_pilot_spec.spl:0` |
| return_type_result_mismatch_class_audit_2026-08-08 | P3 | open | Non-Result declared return types whose bodies return Ok()/Err() remain in owned src after partial fix | `src/lib/common/validation.spl:0` |
| riscv64_arch_unit_specs_fail_interpreter_2026-06-06 | P2 | open | RV64 arch unit specs (boot/interrupt/trap_frame/trap_model) fail under interpreter mode | `test/01_unit/os/kernel/arch/riscv64_boot_spec.spl:0` |
| riscv_gate_evidence_seed_attributed_bin_release_clobbered_2026-07-27 | P2 | open | Every RISC-V gate result is attributed to bin/release/<triple>/simple which is a Rust seed, not self-hosted | `scripts/setup/setup.shs:0` |
| riscv_gen2_raw_artifact_writer_provenance_2026-08-12 | P2 | open | vhdl_render/write_production_artifacts are still exported and will pair valid provenance with arbitrary VHDL | `src/compiler/80.driver/driver_vhdl_artifacts.spl:904` |
| riscv_gen2_stateful_retire_lineage_contract_2026-08-12 | P3 | open | Gen2 parcel frontend cannot reject a pre-reset stale retirement without an architectural retirement producer | `src/compiler/50.mir/hwir/sequential.spl:0` |
| riscv_qemu_lanes_boot_bare_kernel_without_opensbi_2026-08-09 | P2 | open | RISC-V QEMU scenario lanes still push -kernel instead of an OpenSBI firmware proxy | `src/os/_QemuRunner/scenario_exec.spl:461` |
| rt_file_read_bytes_declared_with_six_return_types_2026-08-09 | P2 | open | rt_file_read_bytes extern is redeclared repo-wide with four mutually incompatible return types | `src/lib/nogc_sync_mut/io/file_ops.spl:0` |
| rtl_mdsoc_phase5_modules_never_created_2026-08-04 | P2 | open | vhdl_emit_{fp,simd,cache,hart}_stub.spl were never created; 68 rtl-mdsoc system examples red | `src/compiler/70.backend/backend/vhdl/mod.spl:0` |
| rtl_mdsoc_reorg_fpga_linux_split_never_executed_2026-08-04 | P2 | open | fpga_linux split never executed: orchestrator/data/manifest modules absent, 94 examples red per tree | `src/lib/hardware/fpga_linux/riscv_fpga_linux.spl:0` |
| rust_seed_run_help_treated_as_source_filename_2026-09-09 | P2 | open | Rust seed run --help is treated as a source filename instead of subcommand help | `src/compiler_rust/driver/src/main.rs:0` |
| rv32_exec_core_no_external_debug_ports_2026-07-22 | P3 | open | rv32_exec_core lacks a halt port and SBA-into-fetch for external JTAG hart debug | `examples/09_embedded/fpga_riscv/rtl/rv32_exec_core.vhd:0` |
| rv64_compliance_spec_missing_core_ext_pkg_modules_2026-07-20 | P2 | open | rv64_compliance_spec imports hardware.rv64gc.core.rv64_execute, which does not exist | `src/lib/hardware/rv64gc/top/rv64_machine.spl:0` |
| rv64_ed25519_alpha_pure_sha512_timeout_2026-06-12 | P2 | open | RV64 SSH alpha: pure-Simple Ed25519 signature does not match the runtime/C backend | `src/os/crypto/dual_backend.spl:0` |
| rv64gc_core64_step_removed_dangling_export_2026-07-21 | P2 | open | core64_step is defined nowhere in rv64gc_rtl yet spec files still import and call it | `src/lib/hardware/rv64gc_rtl/core.spl:0` |
| rv64_memory_ops_spec_missing_rv64ram_2026-07-20 | P2 | open | rv64_memory_ops_spec imports hardware.rv64gc.mem.rv64_ram.Rv64Ram, never implemented | `test/unit/hardware/rv64gc/rv64_memory_ops_spec.spl:0` |
| rv64_web_gate_arm64_import_leak_and_storage_2026-06-15 | P1 | open | RV64 HTTP+NVFS gate gets zero GET-200: arm64 import leaks into the link, storage unavailab | `src/os/kernel/arch/riscv64/boot.spl:0` |
| s68_cranelift_interpcall_boxed_result_generic_return_gap_2026-07-18 | P2 | open | Seed cranelift InterpCall returns wrong Object/Enum(Option) values in composite returns | `src/compiler_rust/compiler/src/codegen/instr/core.rs:0` |
| sci_launcher_policy_projection_owner_api_missing_2026-08-14 | P2 | open | SCI launcher rejects whole images: no owner API for path-scoped caps and file associations | `src/os/services/launcher/launcher_registry.spl:0` |
| scram_sha1_examples_exceed_interpreter_10m_op_budget_2026-08-04 | P2 | open | SCRAM-SHA-1 RFC 5802 spec exceeds the interpreter's 10M-operation budget once PBKDF2 runs | `src/compiler_rust/compiler/src/interpreter_state.rs:0` |
| screenshot_sffi_api_declared_but_never_implemented_2026-08-04 | P3 | open | No rt_screenshot_* implementation exists in the C runtime, so native/baremetal links canno | `src/compiler_rust/runtime/src/value/screenshot_sffi.rs:0` |
| seed_constructor_static_method_no_literal_coercion_2026-07-20 | P2 | open | Seed constructor dispatch needs an exact runtime type: an int literal will not coerce to a | `src/compiler_rust/compiler/src/interpreter_method/special/objects.rs:0` |
| seed_emit_object_superlinear_hang_large_module_2026-07-20 | P1 | open | native-build --emit-object never emits IR for a 479-fn module; runs killed at 1h, 3h and 6 | `src/compiler/70.backend/backend/_MirToLlvm:0` |
| seed_interp_ecs_lower_and_freefn_closure_byref | P2 | open | Seed interpreter cannot lower ECS Entity/ComponentStore<T>; free-fn mutation lost inside | `src/os/services/devfs_service.spl:0` |
| seed_interp_explicit_i64_default_arg_poisons_render_backgrounds_2026-07-11 | P1 | open | Passing explicit i64 budget_ms arg to software_pixels renderer paints all backgrounds | `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl:0` |
| seed_jit_lsu64_load_lowering_forces_interpreter_2026-07-22 | P2 | open | Seed JIT HIR lowering reports Unknown variable lsu64_load for a valid cross-module | `src/lib/hardware/rv64gc_rtl/lsu.spl:0` |
| seed_overload_score_option_bytes_misleading_unknown_static_2026-07-20 | P2 | open | Static-call overload scoring reports unknown static method object on class | `src/compiler_rust/compiler/src/interpreter_method/special/objects.rs:0` |
| seed_return_bare_value_next_line_ambiguity_2026-07-31 | P3 | open | `return` with its value entirely on the next line fails with UnexpectedToken expected | `src/compiler_rust/parser/src/stmt_parsing/jump.rs:0` |
| self_error_used_where_error_fatal_intended_family_2026-08-08 | P2 | open | MirLowering.error() sites intended as fatal stay non-fatal, so builds exit rc=0 on | `src/compiler/50.mir/_MirLowering/asm_and_targets.spl:264` |
| self_hosted_cli_native_build_silent_no_artifact_2026-08-14 | P1 | open | Self-hosted CLI native-build exits 0 in ~1.4s printing nothing and writing no output file | `src/app/cli/native_build_main.spl:0` |
| self_hosted_font_renderer_optional_field_shape_2026-07-11 | P1 | open | Self-hosted resolver reports class FontRenderer has no field ttf_rasterizer though it is | `src/lib/nogc_sync_mut/text_layout/font_renderer.spl:0` |
| self_hosted_simpleos_target_native_build_crash_2026-07-11 | P1 | open | native-build --target x86_64-unknown-simpleos dumps core before writing any cache file or | `src/app/cli/native_build_main.spl:0` |
| self_hosted_sspec_describe_colon_parser_2026-08-08 | P2 | open | Self-hosted parser reports unexpected token in expression: ':' at every standard SSpec | `src/compiler/10.frontend/core/parser.spl:0` |
| selfhosted_stage4_interpreter_string_interpolation_broken_2026-07-30 | P1 | open | Self-hosted stage4 `run` prints the literal placeholder x={x} instead of interpolating | `src/compiler/10.frontend/core/lexer_struct.spl:0` |
| selfhost_names_with_no_import_path_masked_by_seed_flat_resolution_2026-08-01 | P2 | open | 66 compiler names are declared in one module with no import path on any importer's graph | `src/compiler/80.driver/driver_source_loading.spl:0` |
| selfhost_noimport_carveouts_error_panic_blockdsl_nilname_2026-08-01 | P2 | open | `error` and `panic` are not both builtins in the self-hosted front end: both lower to | `src/compiler_rust/compiler/src/hir/lower/expr/calls.rs:0` |
| set_method_route_dict_returns_nil_array_tuple_silent_noop_2026-08-02 | P1 | open | dict .set() returns nil under the seed JIT while the mutation lands; array/tuple .set | `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:0` |
| sfnt_fvar_option_match_nil_baremetal_2026-08-04 | P2 | open | val-assigned Option match yields nil on freestanding native lane; table.offset faults | `src/lib/common/encoding/sfnt.spl:85` |
| shim_init_keepalive_function_ptr_cast_breaks_interpreter_2026-08-06 | P2 | open | shim_init calls _shim_keepalive whose fn-ptr-to-u64 casts fail: cannot cast function to... | `src/os/kernel/abi/syscall_shim.spl:248` |
| simple_check_diagnostics_contract_raw_parser_error_not_stable_format_2026-07-20 | P2 | open | simple check prints raw legacy parser text instead of error[Exxxx]; all 10 contract exa... | `src/app/check/main.spl:0` |
| simple_compiler_select_promotes_stage2_binary_without_run_subcommand_2026-08-06 | P2 | open | simple-compiler-select promotes a stage2 bootstrap CLI that answers `run` with unknown... | `src/app/cli/bootstrap_main.spl:492` |
| simple_cli_invocation_attempts_user_gitconfig_lock_2026-09-09 | P1 | open | Simple CLI invocation attempts to lock the user's .gitconfig during a read-only smoke probe | `src/compiler_rust/driver/src/main.rs:0` |
| simpleos_arm64_el0_server_syscall_and_virtio_net_gap_2026-08-14 | P2 | open | _forward_net_ipc unconditionally returns -38 so mounted EL0 apps cannot bind/listen/accept | `src/os/kernel/ipc/syscall_net.spl:136` |
| simpleos_baremetal_backend_resolve_empty_override_rt_process_run_trap_2026-08-11 | P2 | open | After metal/cuda/rocm probes are fixed, boot dies in 21 repeated FAULT @ 0x49bacXXX (ca... | `src/lib/gc_async_mut/gpu/browser_engine/web_render_backend.spl:0` |
| simpleos_bump_heap_no_free_interactive_session_2026-07-26 | P2 | open | x86_64 bump allocator never frees: the first post-boot keypress panics heap exhausted | `examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c:0` |
| simpleos_direct_lfb_blend_span_qemu_gate_2026-08-12 | P2 | open | Direct-LFB blend-span gate reports skip: SIMPLEOS_KERNEL_ELF unset, so no boot evidence... | `scripts/check/check-simpleos-x86-64-wm-qemu-readiness.shs:0` |
| simpleos_freestanding_kernel_elf32_wrap_and_weak_gate_overbroad_2026-08-06 | P2 | open | In-guest /usr/bin/simple hello.spl exits rc=70 with str.clear on a non-text receiver=0x0 | `src/compiler/10.frontend/core/lexer.spl:0` |
| simpleos_freestanding_nil_array_init_optimizer_guard_fold | P1 | open | Freestanding one-binary builds never run module-global array initializers; nil reaches | `scripts/os/fsexec_mkimg_simple.spl:0` |
| simpleos_harden_probe_build_target_2026-06-28 | P2 | open | Harden probe ELF and FAT32 image targets do not exist so AC-1/2/8/9/10 specs are | `src/os/qemu_systest_contract.spl:0` |
| simpleos_harness_silent_native_build_2026-07-26 | P3 | open | WM harness emits zero output during 2h+ kernel build because trace gates are never | `scripts/check/check-simpleos-wm-fullscreen-evidence.shs:0` |
| simpleos_in_guest_toolchain_execution | P2 | open | Guest proves clang/rust fixtures exist but cannot execute a real compiler process or | `src/os/port/guest_toolchain_execution_gate.spl:0` |
| simpleos_native_build_entry_closure_codegen_defects_2026-07-17 | P1 | open | Entry-closure cranelift drops module-global call initializers, nils if-val hits, and | `src/compiler_rust/compiler/src/mir/lower/lowering_core.rs:0` |
| simpleos_physical_board_bringup_hardware_blocked_2026-08-11 | P3 | open | No physical SimpleOS board in this environment so every board-runnable claim stays | `src/os/machine_profile.spl:0` |
| simpleos_qemu_virtio_serial_host_gpu_transport_2026-07-30 | P2 | open | No VirtIO console device or framed host-GPU port exists so x86_64 and RISC-V have no | `src/os/lib/gpu_bridge/host_gpu_ivshmem.spl:0` |
| simpleos_scenario_runner_no_selfhosted_binary_deployed_2026-08-06 | P1 | open | os test --scenario fails with no runnable pure-Simple compiler because every candidate | `src/os/_QemuRunner/os_build_run.spl:0` |
| simpleos_server_credential_zeroization_gap_2026-08-14 | P2 | open | Server credential read into immutable [u8]/text has no compiler-resistant zeroization on | `src/lib/nogc_sync_mut/database/server/capability.spl:0` |
| simpleos_simple_web_decode_string_fault_storm_2026-07-12 | P2 | open | Baremetal decode_string faults on heap-like tagged values so the canonical renderer | `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl:0` |
| simpleos_ssp_codegen_feature_lag_2026-06-28 | P2 | open | No stack-smashing protector anywhere: clang invocation lacks -fstack-protector-strong and | `src/app/compile/native.spl:0` |
| simpleos_toolchain_deployment_desktop_boot_blockers_2026-08-14 | P2 | open | Six named blockers (host CLI crash, target payload, guest lld, image manifest, desktop | `src/compiler/50.mir/mir_lowering_types.spl:414` |
| simpleos_vulkan_board_gap_venus_is_qemu_only | P3 | open | Venus is a command-forwarding protocol with no host on a physical board, so Vulkan has no | `src/os/drivers/virtio/virtio_gpu_init.spl:0` |
| simpleos_wm_gate_provenance_reject_after_boot_chain_fixes_2026-08-04 | P2 | open | After the boot-chain fixes the WM gate still rejects every window with | `src/os/compositor/simple_web_window_renderer.spl:0` |
| simpleos_wm_lane_not_board_runnable_2026-08-08 | P2 | open | No SimpleOS image exists in which a WM actually runs and renders; every gate is preflight | `scripts/check/check-simpleos-x86-64-wm-render-event-evidence.shs:0` |
| simpleos_x64_ssh_live_banner_exchange_timeout_2026-06-29 | P2 | open | OpenSSH times out during banner exchange against the guest sshd; serial shows rt-net | `test/03_system/os/ssh_live_login_in_qemu_spec.spl:0` |
| simpleos_x86_64_baremetal_link_ud2_fault_symbol_2026-07-17 | P1 | open | C fallback and fatal UD2 hook are restored; post-restore SysV stack pad is covered by a focused contract, but guest QEMU evidence remains blocked by VirtioGpuDriver kernel compilation | `src/os/kernel/arch/x86_64/interrupt.spl:372` |
| simple_test_nested_runner_timeout_2026-06-28 | P2 | open | A spec that shells out to a nested `bin/simple test` times out the outer test daemon | `src/app/test_runner_new/test_runner_client.spl:0` |
| simple_web_html_layout_renderer_layout_paint_coverage_gap_2026-08-07 | P3 | open | Layout renderer line coverage measured 40% against a 90% target, a 50-point gap | `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl:0` |
| simple_web_layout_corpus_perf_2026-05-31 | P3 | open | famous_site_corpus_spec takes 86222ms and the runner flags it PERF BUG | `test/03_system/gui/wm_compare/famous_site_corpus_spec.spl:0` |
| simple_web_text_decoration_geometry_clip_2026-06-25 | P2 | open | text-decoration-thickness and text-underline-offset produce no visibly changed pixels due | `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl:0` |
| smf_header_wire_layout_diverges_rust_vs_simple_2026-08-10 | P1 | open | Simple and Rust SMF headers disagree on every offset from section_table_offset onward | `src/compiler/70.backend/linker/smf_header.spl:0` |
| smf_writer_kernel_trailer_layout_skew | P2 | open | No compiler-emitted .smf is accepted as a role-2 library: writer and kernel trailer | `src/os/kernel/loader/smf.spl:27` |
| sosix_qemu_matrix_remaining_owners_2026-08-14 | P2 | open | RV64/x86_32/ARM32 SOSIX QEMU rows lack an admitted Stage-4 runner so no exit-37 reap | `scripts/check/check-sosix-qemu-matrix.shs:0` |
| sosix_qemu_v2_admission_record_hash_binding_2026-08-16 | P2 | open | v2 matrix manifest recorded admission_record_path_b64 without a sha256 binding the | `src/os/sosix/qemu_evidence/trusted_importer.spl:0` |
| source_fixture_spec_unescaped_interpolation_and_content_drift_2026-07-20 | P2 | open | Source-guard specs put {ident} in interpolating strings so they die with `variable | `test/01_unit/compiler/hir/module_lowering_dict_keys_source_spec.spl:0` |
| spec_cross_module_eval_warnings_not_observed_2026-08-05 | P3 | open | A spec importing eval_tables and eval separately reads eval_warnings back as 0 after a | `src/compiler/10.frontend/core/interpreter/eval.spl:0` |
| specs_assert_against_nonexistent_product_paths_2026-08-10 | P2 | open | 835 specs read 949 absent product paths so their negative to_equal(false) legs pass | `scripts/check/check-spec-missing-path-vacuity.shs:0` |
| spipe005_residual_assertion_free_examples_2026-08-01 | P3 | open | SPIPE005 still fires 1790 times across 196 files for assertion-free SPipe examples | `src/compiler/90.tools/lint/_LintMain/traceability_and_assertions.spl:0` |
| spirv_builder_module_drops_to_interpreter_via_unresolved_jit_symbol_2026-08-11 | P2 | open | Any module using SpirvBuilder drops whole-module to interpreter on unresolved JIT symbol | `src/compiler/70.backend/backend/vulkan/spirv_builder.spl:1` |
| ssh_daemon_baremetal_only_and_duplication_2026-08-05 | P2 | open | sshd cannot bind a host socket because its network layer is baremetal-only | `src/os/apps/sshd/mod.spl:1` |
| sspec_no_dir_wide_prevention_scope_2026-08-07 | P3 | open | SSpec has no per-directory config hook so directory-wide prevention-mock scope is | `src/lib/nogc_sync_mut/spec.spl:1` |
| stage2_binary_vulkan_backend_init_segfault_2026-08-09 | P2 | open | Stage2 self-hosted binary SIGSEGVs in VulkanBackend.init while the Rust seed runs the | `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl:1` |
| stage2_cross_module_codec_result_field_inference_2026-08-14 | P2 | open | Stage 2 cannot infer field type of a cross-module codec result struct field | `src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:1` |
| stage3_current_source_hir_rss_termination_2026-08-14 | P1 | open | Current-source Stage 3 terminates at status 143 after unbounded HIR-build RSS growth with | `src/compiler/80.driver/driver_hir_pipeline_lowering.spl:1` |
| stage3_native_build_segv_generic_codegen_link_path_2026-08-06 | P1 | open | Self-hosted stage3 SIGSEGVs in SymbolTable.lookup on essentially every native-build | `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:1` |
| stage3_numeric_interpolation_slot_corruption_2026-08-13 | P1 | open | Numeric interpolation of rt_heap_registry_count overwrites the ast_gen_harden_slot array | `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl:1` |
| stage3_post_file_copy_exit139_2026-08-14 | P1 | open | Stage 3 exits 139 in MirLowering.remember_local_hir_type via maybe_copy_array_value after | `src/compiler/50.mir/mir_lowering_types.spl:414` |
| stage3_post_folded_const_diagnostics_sigsegv_2026_08_14 | P1 | open | Stage 3 peaks near 7.7 GiB RSS and exits 139 right after post-folded-constant | `src/app/cli/bootstrap_main.spl:1` |
| stage3_selfhost_exit_139_2026-08-14 | P1 | open | Fresh pure-Simple Stage 2 segfaults (exit 139) while compiling Stage 3 before writing any | `src/app/cli/bootstrap_main.spl:1` |
| stage3_selfhost_nil_receiver_sigill_in_lower_expr_caller_2026-08-05 | P1 | open | Stage 3 self-host dies at exit 139 with the bare leaf 'bytes' hijacked to | `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:1` |
| stage3_selfhost_phase3_error_array_index_after_struct_reassign_silently_noops_2026-08-10 | P1 | open | Indexing self.ctx.errors right after self.ctx = returned struct emits no output natively | `src/compiler/80.driver/driver_orchestration.spl:0` |
| stage3_selfhost_post_hir_segfault_2026-08-14 | P1 | open | Stage3 crashes after HIR: CompileContext.error_count() from lower_and_check_impl segfaults | `src/compiler/80.driver/driver_hir_pipeline_lowering.spl:0` |
| stage3_selfhost_vtable_field_offset_relro_segv_2026-08-06 | P1 | open | Cross-module field read on vtable-bearing class uses wrong offset and writes into RELRO | `src/compiler_rust/compiler/src/pipeline/native_project/compiler.rs:0` |
| stage3_symboltable_lookup_ud2_field_access_nil_receiver_2026-08-06 | P1 | open | SymbolTable.lookup traps ud2 field access on nil receiver during stage3 native-build | `src/compiler/20.hir/hir_types.spl:0` |
| stage3_unresolved_call_warning_family_2026-08-07 | P2 | open | run_check unresolved because Rust seed source collector hardcodes a *check.spl exclusion | `src/app/cli/check.spl:0` |
| stage4_post_hir_corrupt_module_runaway_2026-08-02 | P2 | open | Stage4 post-HIR pass loops unbounded on a corrupt module instead of aborting | `src/compiler/20.hir/hir_lowering/module_surface.spl:0` |
| stage4_resume_from_admitted_gap_2026-08-14 | P2 | open | Stage4 cannot continue from an already-admitted resumed Stage 3 artifact | `src/compiler/80.driver/driver.spl:0` |
| starfive_check_deployed_simple_segv_2026-08-15 | P1 | open | Deployed simple check segfaults on StarFive implementation files | `src/lib/nogc_async_mut/fs_driver/ramfs.spl:0` |
| stress_f03_manycall_sum_2026-07-17 | P2 | open | 300-call-chain sum diverges on the interpreter path only; compiled/JIT already correct | `src/compiler_rust/compiler/src/interpreter_call/mod.rs:0` |
| string_interpolation_silently_evaluates_literal_braces_2026-07-28 | P2 | open | Interpolation evaluates literal brace content with no guard or diagnostic | `src/compiler_rust/parser/src/lexer/strings.rs:0` |
| struct_dict_field_mutation_engine_divergence_2026-08-10 | P1 | open | Dict-in-struct field mutation through a by-value receiver diverges by engine, silently losing writes | `src/lib/nogc_sync_mut/service/lease_manager.spl:126` |
| svmg_d4_lowering_deferred_subset_2026-08-07 | P3 | open | SVM-G D4 lowering leaves 2 in-subset constructs unimplemented | `src/compiler/70.backend/svmg_lowering.spl:0` |
| svmg_device_arena_code_coresidency_diverges_from_ref_vm_2026-08-07 | P2 | open | Device single-buffer code/data co-residency diverges from ref_vm's separate code array | `src/lib/common/svmg/ref_vm.spl:0` |
| system_cover_gate_reports_791_legacy_feature_specs_as_failures_2026-08-04 | P2 | open | @cover gate marks 791 un-annotated test/03_system/feature specs as FAILURES not skips | `src/app/test_runner_new/test_runner_main.spl:0` |
| t15_hir_forward_decl_target_pass_does_not_exist_2026-08-07 | P3 | open | HirForwardDecl lowering pass has zero production callers; src/app/desugar unreachable from | `src/compiler/20.hir/hir_forward_decl.spl:0` |
| tautology_guarded_skip_specs_false_green_family_2026-08-04 | P2 | open | Tautology-guarded skip specs report green without executing; repo-wide family, census inco | `src/compiler/95.interp/interpreter/pattern.spl:65` |
| test_daemon_freezes_env_binary_override_dead_2026-08-02 | P2 | open | Long-lived light daemon freezes env, so SIMPLE_* binary override is silently ignored | `src/app/test_daemon/light_daemon.spl:0` |
| test_invocation_fixed_setup_cost_caps_every_sweep_2026-08-17 | P1 | open | bin/simple test pays ~310s fixed setup per invocation; directory targets rejected, capping | `src/app/test_daemon/light_daemon.spl:132` |
| test_only_functions_family_census_2026-08-04 | P3 | open | 197 test-only functions shipped in production modules; census is a floor, items unfiled | `src/compiler/30.types/type_system/effects.spl:0` |
| test_runner_env_passthrough_2026-07-29 | P2 | open | Custom env vars set before bin/simple test are stale inside it bodies (daemon-frozen env) | `src/lib/nogc_sync_mut/test_runner/test_runner_args.spl:250` |
| test_runner_reports_only_last_failure_per_example_2026-08-04 | P3 | open | Runner reports only the LAST failure per example, hiding earlier assertion failures | `src/app/test_runner_new/test_runner_main.spl:0` |
| test_tree_divergence_982_diagnosis_2026-08-08 | P2 | open | check-test-tree-divergence reports 982 diverged (1 new, 1 stale-baselined) against baselin | `scripts/check/test_tree_divergence_baseline.txt:0` |
| theme_ipc_k2_review_hard_stop_2026-07-27 | P2 | open | Theme IPC K2 stays fail-closed: no accepted design, K2 transport unimplemented | `src/lib/common/ui/theme_package_wire.spl:0` |
| theme_snapshot_catalog_review_hard_stop_2026-07-27 | P3 | open | theme snapshot catalog design fail-closed after three exhausted review cycles | `src/lib/common/ui/theme_package_wire.spl:0` |
| three_computedstyle_concepts_2026-08-10 | P2 | open | three unrelated ComputedStyle types coexist (blink entity, browser_engine style, ui) with | `src/lib/blink/entity/computed_style.spl:0` |
| tierless_std_import_ambiguity_resolves_by_registration_order_2026-07-29 | P1 | open | tier-less `use std.X` picks a module by registration order, silently selecting the wrong | `src/compiler/99.loader/module_resolver/resolution.spl:0` |
| tls_signature_positive_verification_blockers_2026-06-06 | P2 | open | TLS signature verification has no positive test: ed25519/RSA-PSS/cert-chain specs cannot | `test/03_system/os/os_tls_cert_chain_spec.spl:0` |
| trait_conformance_check_ignores_arity_2026-08-04 | P1 | open | trait conformance matches by method NAME only; parameter types are never compared | `src/compiler/25.traits/trait_impl.spl:0` |
| trait_default_body_segfaults_via_trait_object_2026-08-06 | P1 | open | a trait method with a default body segfaults when invoked through a trait object | `src/os/compositor/input_backend.spl:0` |
| trait_group_with_sugar_status_f5_2026-08-09 | P3 | open | trait-group `with` sugar status remeasured: parser-rejection claim superseded, wiring | `src/app/desugar/trait_desugar.spl:0` |
| trait_group_with_sugar_unwired_and_from_aot_if_val_2026-08-09 | P2 | open | trait-group `with` desugar is unreachable and its generated .from() capability check is | `src/app/desugar/trait_desugar.spl:0` |
| treesitter_node_module_missing_and_spec_tautological_2026-08-04 | P2 | open | std.parser.treesitter_node does not exist and its spec asserts nothing, so the red is | `test/01_unit/std/parser/treesitter_node_spec.spl:0` |
| tree_wipe_module_damage_census_2026-08-04 | P1 | open | tree-wipe left 39 truncated modules; only 3 restored, the rest still short of their | `src/lib/common/format_utils.spl:0` |
| type_alias_static_dispatch_unresolved_2026-08-04 | P2 | open | `type X = Y` does not resolve as a static-call receiver — X.new() sees nil | `src/compiler/35.semantics/lint/semantic_api/alias_registry.spl:0` |
| type_alias_swapped_winner_is_inert_2026-08-01 | P3 | open | a swapped duplicate-`type` alias winner is inert: the alias target is never stored | `src/compiler/35.semantics/lint/semantic_api/alias_registry.spl:0` |
| u64_collections_clobber_recurrence_engine_2026-08-11 | P1 | open | the collections.rs stale-snapshot clobber is one commit replayed six times and still armed | `src/compiler_rust/runtime/src/value/collections.rs:0` |
| u64_range_for_loop_checksum_mismatch_2026-05-14 | P3 | open | u64 range for-loop checksum is correct again but the lane remains materially slower than | `src/compiler/50.mir/mir_lowering_stmts.spl:0` |
| ui_scene_route_owner_lookup_ignores_producer_scope_2026-08-08 | P1 | open | ui_scene_route_event resolves owners by a producer-private id with no producer scope, so | `src/lib/common/ui/ui_scene_event_route.spl:0` |
| undeclared_imported_symbols_census | P2 | open | Imported symbols declared nowhere in repo are silently accepted instead of erroring | `src/compiler/20.hir/hir_lowering/types.spl:0` |
| unregistered_extern_backlog_enumeration_2026-08-01 | P2 | open | Externs declared in .spl are absent from the extern registry, so lanes silently drop them | `scripts/check/check-extern-registration.shs:0` |
| unresolved_type_declared_nowhere_family_2026-08-01 | P2 | open | lower_named_kind whitelist drift: cross-module struct fallback still reports unresolve... | `src/compiler/20.hir/hir_lowering/types.spl:0` |
| unwired_extractions_audit_2026-08-11 | P3 | open | Deduplication extractions were authored and announced Resolved but never wired to consu... | `src/compiler/70.backend/linker/reloc_engine.spl:0` |
| vacuous_spec_corpus_census_and_inert_assertion_forms_2026-08-02 | P2 | open | 5,095 spec files contain inert assertion forms that pass without exercising anything | `test/01_unit/compiler/backend/vhdl_backend_spec.spl:0` |
| verification_layer_orphans_and_dangling_refs_2026-08-02 | P3 | open | Guard scripts under scripts/check are unreachable from any root (orphaned) and refs dangle | `scripts/check/check-extern-registration.shs:0` |
| vhdl_backend_block_temps_emit_process_variables_not_signals_2026-08-04 | P2 | open | VHDL backend emits block-level MIR temps as process variables (:=) not signals (<=) | `src/compiler/70.backend/backend/vhdl_expr.spl:0` |
| vhdl_design_catalog_dict_to_i64_cast_2026-07-30 | P2 | open | A second pre-existing defect under the dict->i64 cast remains open after the cast fix | `test/01_unit/compiler/backend/vhdl_design_catalog_spec.spl:0` |
| virtio_gpu_capset_qemu_smoke_needs_guest_probe_image_2026-08-08 | P3 | open | virtio-gpu capset QEMU smoke has no guest probe image, so the device path is never exer... | `src/os/drivers/virtio/virtio_gpu_capset.spl:0` |
| v_lane_suite_occlusion_spec_times_out_under_shared_wc_contention_2026-08-07 | P3 | open | compositor_occlusion_spec times out at the V-lane 600s floor under shared-WC contention | `scripts/check/check-render-perf-v-lane-suite.shs:64` |
| vulkan_8k_jit_retained_host_buf_sample_crash_2026-08-12 | P2 | open | Strict-JIT 8K retained host-buffer sample crashes on a retained u32 array read | `test/fixtures/jit_class_u32_array_retained_read/main.spl:0` |
| vulkan_ffi_ledger_lost_under_spec_harness_2026-08-09 | P2 | open | VulkanFfi rejection ledger never accumulates under the spec harness but works under `run` | `src/lib/nogc_sync_mut/gpu/engine2d/ffi_vulkan.spl:0` |
| vulkan_icd_virtio_and_gpu_probe_report_no_real_device_enumeration_2026-08-11 | P2 | open | vulkan_icd_virtio and gpu_vendor_probe report no real device enumeration data | `src/lib/nogc_async_mut/gpu/vulkan_icd_virtio.spl:52` |
| vulkan_web_fullpage_cpu_fallback_demotion_2026-08-10 | P2 | open | Vulkan engine2d web lane reports source=cpu_fallback at 800x2600 but device_readback at | `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl:0` |
| web_css_package_authority_adapter_2026-07-27 | P3 | open | generate_package_authoritative_css emitted literal n and dropped traffic-light ::before | `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl:0` |
| web_paint_wallclock_budget_flake_2026-07-31 | P1 | open | Web paint path aborts on a wall-clock deadline, making every pixel-verifying spec | `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_layout.spl:0` |
| web_render_backend_api_spec_perf_2026-06-05 | P3 | open | Web render backend API spec exceeds the test runner's per-spec perf threshold | `src/lib/gc_async_mut/ui/web_render_pixel_backend.spl:0` |
| web_showcase_vector_font_evidence_style_budget_truncation_2026-08-01 | P1 | open | CSS style pass truncates on wall-clock budget so the vector-font marker node keeps | `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core.spl:0` |
| web_software_oracle_blanks_text_on_budget_exhaustion_2026-08-04 | P1 | open | Software web-render oracle silently blanks all text when its wall-clock budget is | `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl:0` |
| web_style_producer_4s_per_node_interpreted_lane_2026-07-29 | P2 | open | Web style producer costs ~4s per DOM node on the interpreted lane, blocking the showcase | `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core.spl:0` |
| widget_draw_ir_panel_title_not_rendered_2026-08-09 | P3 | open | Panel titles are never emitted by the pixel Draw-IR pipeline, so titled panels look | `src/lib/common/ui/widget_draw_ir.spl:0` |
| wildcard_import_c_backend_stubs_function_to_int_2026-07-30 | P2 | open | use compiler.backend.backend.c_backend_stubs.* poisons the session with cannot convert | `src/compiler_rust/compiler/src/value_impl.rs:0` |
| wine_vm_module_family_destroyed_by_tree_wipe_2026-08-04 | P2 | open | wine_vm module family lost to a tree wipe and partly rebuilt by guess, so contents are | `src/lib/common/wine_vm_adapter.spl:0` |
| wm_action_applier_window_surface_session_and_web_window_request_2026-08-10 | P2 | open | wm_action_applier_spec: 2 of 17 examples RED — window-surface session and | `src/os/compositor/wm_action_applier.spl:0` |
| wm_content_kind_render_runtime_gate_2026-07-29 | P2 | open | DesktopShell.run() still calls render_all() compatibility path instead of shared frame | `src/os/compositor/compositor.spl:0` |
| w_mc_res_001_overfires_verb_only_heuristic_2026-08-07 | P2 | open | W-MC-RES-001 verb-only heuristic over-fires ~208 findings, cannot separate acquires from | `src/compiler/35.semantics/lint/unwrapped_foreign_resource.spl:0` |
| wm_glass_qemu_evidence_contract_p1_2026-07-27 | P2 | open | WM glass QEMU x86/ARM evidence rows lack frozen-source manifest and parity receipts, fail | `scripts/check/check-simpleos-wm-fullscreen-evidence.shs:0` |
| wm_guest_css_var_unresolved_blocks_material_admission_2026-08-09 | P1 | open | Guest renders theme sheet with var() UNRESOLVED, failing two material-admission terms not | `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl:0` |
| wm_host_external_content_owner_2026-07-29 | P2 | open | Remote application presentation still RED after content_owner scalar fix for external | `src/os/compositor/host_compositor_core.spl:0` |
| wm_lane_boundary_7_new_violations_2026-08-08 | P3 | open | check-wm-lane-boundary.shs reports 7 NEW portable-lane violations; nothing runs this gate | `scripts/check/check-wm-lane-boundary.shs:0` |
| wm_metal_glass_multi_receipt_opacity_2026-07-27 | P2 | open | Metal glass: inactive-opacity offscreen is gpu_only=false so device-glass rejects it | `src/os/compositor/compositor.spl:0` |
| wm_native_regression_gate_blocked_2026-07-29 | P3 | open | Capped full WM native source closure never retried after ot_layout_shaper Unexpected | `src/lib/skia/feature/shaper/ot_layout_shaper.spl:0` |
| wm_production_fullscreen_evidence_security_registry_any_field_infer_2026-08-09 | P2 | open | check-wm-production-fullscreen-evidence.shs still fails; fix 7fa2d06aaa8 not in deployed | `src/compiler_rust/compiler/src/mir/lower/lowering_expr_control.rs:0` |
| wm_protocol_status_event_symbols_never_implemented_2026-07-28 | P1 | open | 8 WM IPC status/event symbols imported by live code exist in no source file | `src/lib/common/window_protocol/window_protocol.spl:0` |
| wm_scene_css_render_perf | P3 | open | WM scene CSS pixel render too slow above 10000 px; path capped by | `src/os/compositor/wm_scene.spl:0` |
| wm_scene_web_lane_layout_scrambled_2026-07-03 | P3 | open | backdrop-filter blur unimplemented so WM glass shows sharp detail instead of frosted | `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl:0` |
| wm_taskbar_pin_persistence_transaction_2026-07-29 | P3 | open | Taskbar pin rollback fix has no live native persistence evidence; blocked by VFS global | `src/os/compositor/compositor.spl:0` |
| x25519mlkem768_jit_fallback_interpreted_execution_2026-08-05 | P2 | open | All X25519MLKEM768 hot-path operations run interpreted; JIT lost on the entire hybrid-KEM | `src/os/crypto/x25519_mlkem768/execution_policy.spl:93` |
| x25519mlkem768_neon_rvv_ntt_not_implemented_2026-08-08 | P2 | open | NEON and RVV ML-KEM NTT candidates are declared but only the AVX2 i32x8 butterfly exists | `src/lib/nogc_sync_mut/simd.spl:767` |
| x64_freestanding_char_code_at_dynamic_text | P1 | open | x86_64 freestanding char_code_at mis-decodes at scattered indices on dynamically built | `examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c:0` |
| x64_freestanding_push_byte_reassign_byte_packed | P2 | open | u8.to_i64() mis-dispatches to VfsFileSize.to_i64() — frontend method-name collision | `src/os/apps/sshd/ssh_session.spl:0` |
| x64_freestanding_text_char_at_starts_with | P2 | open | x86_64 freestanding starts_with mis-decodes; residual after char_at and from_byte_array | `examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c:0` |
| zstd_brotli_encoders_are_stored_only_2026-08-17 | P2 | open | zstd and brotli encoders emit container-only output LARGER than input (310/304 bytes for | `src/lib/common/compress/zstd.spl:0` |
| native_build_print_drops_newline_2026-08-17 | P2 | open | print drops its newline under native-build only | `NONE:0` |
| prepush_hook_unpassable_native_build_oom_2026-08-17 | P1 | open | Pre-push hook is unpassable: check-native-extern-fabrication depends on native-build which is SIGKILLed at >24 | `scripts/check/check-native-extern-fabrication.shs:0` |
| spkc_p2_authority_publication_journal_first_use_mkdir_race_2026-08-26 | P1 | open | SPKC P2 authority-publication journal first-use mkdir race | `examples/05_stdlib/spipe/src/storage/authority_publication_journal.js:0` |
| macos_live_process_stdbuf_required_2026-09-21 | P1 | open | Stock macOS live process runner required GNU stdbuf; source fixed, native qualification pending | `src/lib/nogc_sync_mut/io/process_ops.spl:1414` |
| macos_live_process_tmpdir_shell_quoting_2026-09-21 | P1 | open | Live process TMPDIR crossed two shells without quoting; source repaired and pathological-path regressions added; native gate pending SCV memory fix | `src/lib/nogc_sync_mut/io/process_ops.spl:1426` |
| windows_scv_inventory_cold_init_untracked_walk_slow_2026-09-13 | P1 | open | Windows SCV cold initialization retains digest events and canonicalizes facets once, but repeated untracked walking still lacks RSS/wall proof | `src/app/compiler_entrypoint/inventory_events.spl:0` |
| mcp_interpreter_startup_12s_2026-09-14 | P2 | open | MCP interpreter startup spends roughly 11-13 seconds in eager module loading | `src/app/mcp/main.spl:0` |
| beta1_tag_cannot_bootstrap_on_windows_2026-09-14 | P1 | open | Beta release produced Windows bootstrap artifacts but release publication was skipped because failed matrix legs gated downstream jobs | `.github/workflows/release.yml:0` |
| logical_source_path_v1_value_projection_drift_2026-09-14 | P1 | open | Virtual-source registration integration reaches summary projection then accesses absent LogicalSourcePathV1.value | `src/compiler/00.common/cache_contract/virtual_source_registration_v1.spl:0` |
| bin_caret_dropped_native_only_launcher_policy_2026-09-06 | P3 | open | bin/caret dropped its native-only launcher policy (2 of 3 committed spec examples fail; deliberately not fixed) | `bin/caret:0` |
| stage2_test_runner_imported_enum_owner_text_corrupt_2026_10_19 | P1 | open | Stage 2 test-runner build reads overwritten imported-enum owner text (schema=...) and fails MIR enum lowering | `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:240` |
| bug_add_seed_rename_path_stack_overflow_2026_10_19 | P2 | open | bug-add on the Rust seed overflows the stack in rename_path and saves nothing | `src/lib/nogc_sync_mut/io_runtime.spl:493` |
| bootstrap_dual_planner_receipts_share_planner_artifact_2026_10_19 | P1 | open | Producing the Stage 3 and managed Stage 4 planner receipts in one run overwrites the shared planner binary and unbinds the Stage 3 receipt | `scripts/bootstrap/bootstrap-from-scratch.sh:4590` |
| stage2_matrix_full_cli_build_exceeds_40g_2026_10_19 | P1 | open | Stage 2 matrix full-CLI build peaks above 40 GiB in MIR lowering (41.8 GiB, OOM-killed under a 40G scope) | `src/compiler/50.mir/_MirLowering/module_lowering.spl:1` |
| seed_enum_variant_bare_name_last_registration_wins_2026_10_19 | P1 | open | Seed resolves enum variants by bare enum name (last registration wins); duplicate ByteOrder broke every native-build importing io_runtime | `src/compiler_rust/compiler/src/interpreter_method/mod.rs:1375` |
| seed_hybrid_jit_spliced_u8_array_boxed_elements_2026_10_19 | P2 | open | Seed hybrid JIT returns [u8] through the interpreter splice with boxed elements; indexing and bulk rt_* calls misread it | `src/compiler_rust/runtime/src/value/utf8_kernels.rs:226` |
| pure_simple_native_cache_closure_wide_scope_key_2026_10_20 | P1 | open | Pure-Simple native-build object cache keys the whole source closure: one edited file recompiles every module | `src/compiler/80.driver/driver_build/incremental.spl:1` |
| stage3_bootstrap_closure_mir_lowering_retention_2026_10_20 | P0 | open | Stage 3 bootstrap-fixed closure MIR lowering retains ~36 MB per module (13 GB -> 53 GB over 1100 modules) | `src/compiler/80.driver/driver_pipeline_lowering.spl:938` |
| p4p2_cranelift_verifier_types_2026-10-20 | P1 | open | Cranelift AOT verifier type mismatches in 7 phase-4 tool units (cross-module f64 call ABI, f64.to_i64 text builtin, char cast reduce width, untyped-param value return); gzip/crc.spl carries typed signatures as a workaround until a producer rebuild picks up the source fix | `src/compiler/70.backend/backend/cranelift_codegen_adapter.spl:1719` |
| 2998 | P2 | open | retain array type across optional dictionary lookup | `src/compiler/40.mono/monomorphize/cycle_detector.spl:157` |
| BUG-2026-10-12-CONTEXT-COMPARISON | P2 | open | Rust seed treats a context comparison tail as a context statement | `src/compiler/80.driver/driver_hir_pipeline_lowering.spl:198` |
| BUG-NATIVE-NESTED-STRUCT-NIL-COPY-20261016 | P2 | open | tagged-nil-nested-record-copy-guard | `src/compiler/50.mir/mir_data.spl:203` |
| BUG-NATIVE-RESULT-CHAR-UNWRAP-20261017 | P2 | open | result-char-unwrap-unsupported-use-real-pattern | `test/01_unit/compiler/frontend/unicode_scalar_char_fixture.spl:6` |
| BUG-NATIVE-U8-TO-I64-TEXT-DISPATCH-20261017 | P2 | open | numeric-u8-to-i64-resolves-text-parser | `test/01_unit/compiler/frontend/unicode_scalar_char_fixture.spl:21` |
| BUG-PHASE1-BDD-NEGATED-MATCHERS-20261011 | P2 | open | direct grammar regression remains unchanged. | `test/01_unit/compiler/negated_matcher_consumer_predicate_spec.spl:2` |
| BUG-X86-EVEX-STATIC-ARRAY-INFERENCE-20261017 | P2 | open | producer0015_cannot_infer_register_id_array | `src/compiler/70.backend/backend/native/_X8664Avx512/evex_encoding.spl:82` |
| a174_aggregate_receiver_provenance_2026_10_16 | P2 | open | retain-explicit-aggregate-receiver-type | `src/lib/nogc_sync_mut/database/core.spl:679` |
| a174_enum_scalar_codec_wire_boundary_2026_10_16 | P2 | open | generate-typed-enum-prototypes-and-schema-owned-wire-nil-slots | `src/app/compiler_schema/codec_gen.spl:685` |
| a174_enum_tuple_literal_provenance_2026_10_16 | P2 | open | retain-tuple-payload-type-at-constructor | `test/04_smoke/enum_wire_boundary_native.spl:123` |
| a174_named_enum_payload_owner_2026_10_16 | P2 | open | retain-declared-owner-through-positional-payloads | `src/compiler/20.hir/hir_types.spl:775` |
| a174_nominal_enum_operator_resolution_2026_10_16 | P2 | open | compare-exhaustive-canonical-section-names | `src/compiler/80.driver/smf/runtime_std_package_membership_v1.spl:260` |
| a174_struct_nil_comparison_dispatch_2026_10_16 | P2 | open | old-producer-record-presence-dispatch | `src/app/compiler_schema/codec_gen.spl:436` |
| a174_transient_promote_inference_2026_10_16 | P2 | open | retain-explicit-text-owner-at-generic-promotion | `src/compiler/40.mono/mono_archive_current_registration_seal_v1.spl:54` |
| array_get_contract_drift_crypto_2026-10-18 | P2 | open | use-proven-indexing-until-get-contract-is-resolved | `test/01_unit/os/crypto/curve25519_bigint_nested_return_spec.spl:7` |
| backend_plugin_enum_equality_mir_2026_10_12 | P2 | open | compare_exhaustive_unique_canonical_enum_names_until_enum_equality_lowering_is_fixed | `src/compiler/00.common/backend_plugin/model.spl:75` |
| backend_plugin_result_payload_mir_2026_10_12 | P2 | open | exhaustive_matches_preserve_original_error_payload_and_role_checks | `src/compiler/70.backend/backend_plugin/builtin_adapter.spl:133` |
| bootstrap-builder-owner-native-string-methods-2026-09-30 | P2 | open | bootstrap-builder-owner-native-string-methods-2026-09-30 | `src/lib/nogc_sync_mut/io/windows_process_owner.spl:91` |
| bootstrap_raw_byte_loop_unbox_2026_10_16 | P2 | open | inspect-codepoints-without-decoding-raw-u8-words-as-tagged-integers | `src/compiler/80.driver/driver_build/native_entry_closure_receipt.spl:87` |
| cmake_array_append_native_2026_10_16 | P2 | open | baked native producer cannot dispatch array append | `src/compiler/70.backend/backend/cmake_gen.spl:120` |
| coherence_optional_payload_owner_2026_10_19 | P2 | open | retain optional text metadata across Some/nil merge before enum construction | `src/compiler/25.traits/trait_coherence.spl:104` |
| cuda_optimizer_surface_owner_2026_10_10 | P2 | open | explicit imported payload owner | `src/compiler/60.mir_opt/mir_opt/auto_vectorize_cost.spl:7` |
| cuda_port_imported_method_surface_type_owner_2026_10_16 | P2 | open | retain owner types projected from CudaBackend methods | `src/plugins/backend_cuda/cuda_backend_port.spl:10` |
| dict_nominal_tuple_binders_any_bootstrap_2026_10_21 | P2 | open | explicit nominal dictionary binder control | `test/fixtures/native_dict_nominal_loop/typed/main.spl:25` |
| enum_named_payload_default_dropped_2026_10_16 | P2 | open | exercise the rich HIR/artifact boundary until flat enum defaults are transported. | `test/fixtures/compiler/archive_enum_declaration_prescan_repro.spl:54` |
| eq_ord_where_bound_unresolved_hir_2026_10_19 | P2 | open | HIR lowers builtin-trait where bounds Eq/Ord as types and fails unresolved type; bounds dropped (erased before 5b649fb61fe) | `src/app/optimize/sprof_collection_profile.spl:257` |
| imported_value_constructor_static_receiver_native_2026_10_16 | P2 | open | baked producer lowers imported enum receiver as runtime value | `src/compiler/70.backend/backend_types.spl:412` |
| lean_native_constructor_default_argument_2026_10_21 | P2 | open | bootstrap seed cannot lower imported constructor-expression defaults | `src/plugins/backend_lean/lean_backend.spl:769` |
| lexer_imported_instance_methods_2026_10_06 | P2 | open | lexer imported instance methods 2026 10 06 | `src/compiler/10.frontend/core/lexer_struct.spl:1789` |
| mir_array_range_authority_header_2026_10_18 | P2 | open | copy-exact-fourteen-header-fields-without-unsupported-array-range | `src/compiler/80.driver/cache/runtime_std_authority_receipt.spl:179` |
| mir_lower_child_tasks_append_access_violation_2026-10-19 | P1 | open | native MIR lowering access-violates on the loop-tail `if a.f != '' and b.f == a.f: ... else: ...` form; statement-form if with a helper predicate is equivalent | `src/app/mcp/assistant/session_store_helpers.spl:61` |
| mir_optional_record_nil_join_2026_10_18 | P2 | open | retain-optional-provider-owner-without-a-call-plus-nil-merge | `src/lib/scv/compile_source_inventory.spl:57` |
| puresql_native_mir_failures_2026_10_25 | P2 | open | pure_sql native MIR failures worked around at 9 sites | `src/lib/nogc_sync_mut/database/pure_sql/_PureDatabase/pure_database.spl:73` |
| indcall_try_then_member_2026_10_25 | P2 | open | f(x)?.m() lexes as safe-navigation; try parenthesized | `src/compiler/70.backend/linker/elf/archive_file.spl:75` |
| convnodes_retained_file_result_tuple_u64_2026_10_25 | P2 | open | retained_file result tuple u64 lowering | `src/lib/nogc_sync_mut/io/retained_file.spl:151` |
| native_u8_array_ne_compares_reference_2026_10_25 | P2 | open | native [u8] != compares references; element-wise compare | `src/lib/nogc_sync_mut/io/retained_file.spl:288` |
| native_raw_integer_optional_presence_2026_10_26 | P2 | open | native to_i64 returns raw i64 under ?? presence test | `src/lib/scv/compile_source_inventory.spl:420` |
| mir_bare_ok_imported_trait_method_return_2026_10_27 | P2 | open | bare Ok/Err on imported trait method result ambiguous in stage2 (fixed by #4998) | `src/compiler/70.backend/backend/backend_api.spl:161` |
| mir_provider_optional_type_wrapper_segv_2026-10-14 | P1 | open | old-A174-provider-ArrayLit-optional-ABI | `src/compiler/40.mono/monomorphize_integration.spl:216` |
| mir_tco_parameter_local_identity_2026_10_16 | P2 | open | retain indexed instruction declaration before enum dispatch | `src/compiler/60.mir_opt/mir_opt/tco.spl:125` |
| mir_unannotated_collection_element_type_lost_2026_10_20 | P2 | open | MIR keeps no element type for an unannotated array literal, so pop() is unresolved | `src/compiler/80.driver/action_graph/coordinator.spl:67` |
| native-result-ok-record-inference-20261018 | P2 | open | retain-declared-result-ok-record | `src/app/bootstrap_builder/native_group_provisional_runtime.spl:110` |
| native_array_concat_dispatch_bootstrap_2026_10_16 | P2 | open | baked bootstrap producer cannot dispatch array concat | `src/app/startup/launch_metadata.spl:708` |
| native_array_concat_method_missing_2026_10_16 | P2 | open | use-supported-array-add-merge-path | `src/compiler/80.driver/cache/package_archive_cache.spl:417` |
| native_comprehension_packed_u8_array_mir_2026_10_20 | P2 | open | self_hosted_mir_rejects_comprehension_over_packed_u8_array | `src/compiler/10.frontend/frontend_advisory_preprocess_port_v1.spl:90` |
| native_future_receiver_typeparam_2026_10_18 | P2 | open | Explicit real Future construction retains the concrete Poll and Result payload owners after static-call receiver specialization fails | `src/lib/common/io/read_only_file_view.spl:183` |
| native_optional_fn_payload_binding_arity_mir_2026_10_20 | P2 | open | declared_fn_parameter_gives_the_indirect_call_its_proven_signature | `src/compiler/80.driver/driver_build/parallel.spl:379` |
| native_result_enum_unwrap_err_2026_10_18 | P2 | open | preserve-enum-error-through-pattern-binding | `src/compiler/20.hir/archive/interface_action_archive.spl:206` |
| native_text_scalar_validation_failure_2026_10_18 | P2 | open | use-existing-pure-utf8-owners-for-scalar-validation | `test/fixtures/repro/compiler/char_wire_scalar_cast/main.spl:8` |
| outline_block_native_prerequisites_2026_10_16 | P2 | open | baked native producer omits trait default slots | `src/compiler/15.blocks/blocks/builtin_blocks_data.spl:200` |
| p4p2_cross_module_generic_free_fn_not_instantiated_2026-10-20 | P2 | open | phase-2 producer emits no object symbol for generic free fns and leaves cross-module calls on the unspecialized name (lld-link: undefined symbol lib.nogc_sync_mut.concurrent.mutex.mutex_new/mutex_unlock); i64 gates mirror mutex_lock_gate | `src/lib/nogc_sync_mut/concurrent/mutex.spl:175` |
| pass_scope_enum_owner_projection_2026_10_19 | P2 | open | retain declared record and enum subject before qualified match | `src/compiler/60.mir_opt/mir_opt/mod.spl:870` |
| positional_brace_dict_payload_parsed_as_struct_field_2026_10_20 | P2 | open | positional `V({text: i64})` payload is read as a named field `text: i64`; spelled Dict<K, V> | `src/compiler/20.hir/hir_lowering/phase_memo_ownership.spl:4` |
| pure_simple_native_array_suffix_range_2026_10_12 | P2 | open | collect_guarded_array_suffix_until_native_range_index_lowering_exists | `src/compiler/00.common/dependency/member_visibility.spl:46` |
| query-native-array-tail-range-20261016 | P2 | open | native-range-lowering | `src/app/cli/_QueryVisibility/query_commands.spl:662` |
| query-native-trim-end-dot-20261016 | P2 | open | native-method-resolution | `src/app/cli/_QueryVisibility/symbol_resolution.spl:25` |
| seed_list_comprehension_join_and_empty_native_2026_10_21 | P2 | open | bootstrap comprehensions lower to nil and erase join receiver | `test/fixtures/native/json_comprehension_join/explicit/main.spl:10` |
| seed_windows_path_identity_errno_discovery_2026_10_06 | P2 | open | keep_nonwindows_errno_directives_out_of_windows_seed_discovery | `src/lib/nogc_sync_mut/io/path_identity_abi.spl:19` |
| source_change_inferred_return_field_layout_2026_10_11 | P2 | open | explicit return-type import/control keeps the producer ABI failure visible. | `test/fixtures/compiler/source_change_contract_native.spl:1` |
| ui_c1_unit_nil_type_aliases_native_2026_10_16 | P2 | open | 0CD6 recognizes canonical lowercase unit; capital nominal alias is unresolved | `src/app/ui.web/bounded_channel.spl:36` |
| value_optional_payload_type_context_native_2026_10_16 | P2 | open | retain declared Value optional payload context across nested Some construction | `src/compiler/70.backend/backend_types.spl:233` |
| websocket_timestamp_owner_and_entropy_2026_10_16 | P2 | open | undefined Platform timestamp owner; historical timestamp units unknown | `src/lib/nogc_sync_mut/websocket/frame.spl:30` |
| codegen_isa_sffi_text_abi_misexpansion_2026_10_22 | P1 | open | Cranelift ISA/config SFFI wrappers hand-expand text with rt_string_data/rt_string_len; seed-built binaries re-expand the extracted pointer so isa-feature readback returns garbage (same defect class as io_file_open) | `src/lib/nogc_sync_mut/sffi/codegen.spl:38` |
| generic_enum_pattern_self_subject_hir_2026_10_22 | P2 | open | selfhosted_hir_rejects_generic_enum_patterns_on_self_field_subjects_but_accepts_parameter_subjects | `src/lib/nogc_async_mut/async/poll.spl:14` |
| gzip_optional_collection_payload_provenance_2026_10_21 | P2 | open | gzip optional collection payload provenance 2026 10 21 | `src/lib/nogc_sync_mut/compression/gzip/compress.spl:110` |
| gzip_untyped_reader_byte_array_text_dispatch_2026_10_21 | P2 | open | gzip untyped reader byte array text dispatch 2026 10 21 | `src/lib/nogc_sync_mut/compression/gzip/header.spl:70` |
| native_array_take_method_missing_2026_10_21 | P2 | open | Use the existing ordered fresh-prefix contract until native array.take is admitted | `src/lib/nogc_async_mut/database/query.spl:154` |
| native_byte_to_i64_text_dispatch_2026_10_21 | P2 | open | old645 dispatches numeric byte methods as text; remove after rebuilt producer passes byte and SDN regressions | `src/lib/common/sdn/parser.spl:204` |
| native_method_result_overwrites_receiver_slot_2026_10_21 | P2 | open | old_producer_field_writeback_uses_bool_result | `src/compiler/10.frontend/generated/ast_semantic_value.spl:26` |
| native_numeric_alias_routed_as_text_2026_10_21 | P2 | open | old_producer_to_i64_parses_integer_as_text | `src/lib/common/crypto/sha256.spl:519` |
| native_optional_array_pattern_binder_i64_2026_10_21 | P2 | open | preserve_declared_sdn_array_element_type_until_pattern_binder_lowering_is_rebuilt | `src/compiler/80.driver/driver_build/incremental.spl:1034` |
| nll_live_aliases_method_arg_corruption_2026_10_22 | P1 | open | self_receiver_plus_array_arg_method_call_miscompiles_in_native_candidate | `src/compiler/55.borrow/borrow_check/nll.spl:337` |
| optional_array_payload_narrowing_native_2026_10_21 | P2 | open | old_producer_does_not_narrow_optional_array_after_nil_guard | `src/app/compiler_schema/fold_gen.spl:324` |
| optional_try_nominal_owner_missing_2026_10_21 | P2 | open | Keep the declared table owner until rebuilt Try metadata recovery is qualified | `src/lib/nogc_async_mut/database/bug.spl:389` |

## Closed Bugs

| ID | Severity | Status | Title | Updated |
|----|----------|--------|-------|---------|
| bitbucket_5xx_error_drops_http_status_2026-10-31 | P2 | fixed | Bitbucket 5xx errors omitted the HTTP status | 2026-10-31 |
| confluence_list_ignores_links_next_2026-10-31 | P1 | fixed | Confluence list and search ignored the next link | 2026-10-31 |
| devhub_minio_truncated_body_reported_as_success_2026-10-31 | P1 | fixed | A truncated MinIO GET reported success | 2026-10-31 |
| outlook_email_adapter_get_sent_without_auth_2026-10-31 | P1 | fixed | The Outlook Graph adapter sent GETs without auth | 2026-10-31 |
| seed_interpreter_opened_view_read_tuple_index_2026_10_31 | P2 | fixed | Tuple index failure after an encrypted open came from a shadowed binding | 2026-10-31 |
| os_crypto_partial_helper_rename_2026_10_31 | P1 | fixed | OS crypto modules call helpers under names they no longer define | 2026-10-31 |
| workaround_annotation_malformed_refresh_fails_2026_10_27 | P1 | fixed | Workaround annotation malformed: refresh fails on every native-build | 2026-10-27 |
| parse_fibers_every_file_errors_2026_10_27 | P1 | fixed | parse-fibers child reports every file as error (tldr/error arrays aliased) | 2026-10-27 |
| hir_shard_claim_failure_blocks_ledger_2026_10_27 | P0 | fixed | HIR shard ledger claim race / worker-crash global block | 2026-10-27 |
| mono_generic_field_access_arg_unspecialized_2026-10-23 | P2 | fixed | mono generic field access arg unspecialized (workaround registered) | 2026-10-27 |
| stage2_core_c_literal_relocations_resolve_to_minus_one_2026_10_19 | P0 | fixed | Stage 2 binary relocates runtime_native.c string literals to -1; rt_secure_temp_dir_make SEGVs in the Stage 2 sanity build | 2026-10-20 |
| stage3_hir_shard_workers_collide_on_mem_snapshot_file_2026_10_19 | P1 | fixed | Stage 3 sharded route: every HIR shard worker inherits one SIMPLE_MEM_SNAPSHOT_FILE and fails O_EXCL open (retained lowering path lacked the shard-mode guard) | 2026-10-19 |
| bdd_assert_outside_it_silent_false_green_2026_10_19 | P2 | fixed | Spec assertion failure outside an `it` block is silently dropped (assert_*, expect matchers and pure-Simple fail_assertion now fatal) | 2026-10-19 |
| runtime_array_join_counted_bytes_2026_10_12 | P1 | fixed | Runtime array join discards counted NUL bytes | 2026-10-12 |
| phase1_bootstrap_builder_invalid_branch_layout_2026_10_06 | P1 | fixed | Invalid bootstrap builder conditional branch layout blocks Phase1 specs | 2026-10-06 |
| bootstrap_progress_monitor_reports_live_run_as_dead_2026-09-03 | P1 | fixed | Bootstrap progress monitor reports a live macOS compiler tree as zero processes and zero RSS | 2026-09-21 |
| gpu_backend_layer_result_reason_clobber_2026_08_03 | P2 | fixed | GPU backend layer_result clobbers producer unavailability reason | 2026-08-03 |
| 2026-08-05_wm_content_frame_web_provenance_unreachable_via_widget_panel | P2 | fixed | wm_content_frame_web_provenance_valid unreachable for widget-panel WM content | 2026-08-17 |
| 2026-08-05_wm_false_success_family_guard_blocked_by_out_of_scope_gaps | P2 | fixed | wm_false_success_family_spec cannot reach clean verdict; service.spl counters unbaselined | 2026-08-17 |
| a2_target_ir_blocked_on_untracked_target_graph_2026-08-10 | P2 | fixed | A2 target IR complete but never landed; target_graph.spl vanished | 2026-09-13 |
| aarch64_real_firmware_boot_gap_and_seed_defects_2026-07-14 | P2 | fixed | aarch64 real-firmware boot gap plus arm64 virtio-blk single-sector defect | 2026-08-17 |
| add_remove_log_modes_timeout_resource_limit_2026-07-17 | P3 | closed | add_remove_log_modes_spec times out from SIMPLE_LIB=src 600+ file interpreter load | 2026-08-17 |
| aes128_ccm_rfc3610_kat_mismatch_2026-07-20 | P1 | closed | AES-128-CCM RFC3610 KAT mismatch: wrong ciphertext and auth tag | 2026-08-17 |
| aes256_ctr_keystream_wrong_after_first_block_2026-07-20 | P1 | fixed | AES-256-CTR keystream diverges from NIST SP800-38A after first block | 2026-08-17 |
| aes_utilities_unseeded_key_iv_nonce_generators_are_lcg_constants_2026-08-08 | P2 | fixed | generate_aes_key/generate_iv/generate_nonce are constant-seeded LCGs | 2026-08-17 |
| aliased_array_mut_param_mutation_lost_interpreter_2026-08-06 | P1 | closed | Array passed as both mut and non-mut param silently discards the mutation | 2026-08-17 |
| angle_bracket_index_lint_parse_mismatch_2026-06-06 | P2 | fixed | Angle-bracket index lint suggests a form the parser rejects | 2026-08-17 |
| animation_subsystems_fully_unwired_2026-07-05 | P2 | closed | Animation subsystems fully built and tested but unreachable in any live GUI lane | 2026-08-17 |
| any_receiver_element_read_shift_and_tag_2026-08-06 | P1 | fixed | Element read off an `any` receiver: three forms, three different results | 2026-09-13 |
| any_typed_closure_param_destroys_value_2026-07-28 | P1 | closed | Any-typed closure parameters silently destroy the value | 2026-08-17 |
| aop_hart_hooks_weaving_gaps_2026-07-22 | P2 | closed | AOP hart hooks: no in-tree path executes woven advice for lib-module hardware code | 2026-08-17 |
| arm64_qemu_ivshmem_preboot_2026-07-12 | P2 | closed | ARM64 QEMU ivshmem BAR2 mapping: PCI enumeration returns -2 despite 1af4:1110 | 2026-08-17 |
| asm_template_placeholders_never_bind_2026-08-07 | P1 | fixed | asm ... template placeholders never bind; @cfg(target_arch) is inert | 2026-09-18 |
| assign_rhs_newline_continuation_parse_2026-07-25 | P3 | fixed | `name =` with the RHS on the next line does not parse | 2026-09-13 |
| ast_env_mirror_bypasses_stale_index_guard_2026-08-01 | P1 | fixed | AST env mirror serves stale nodes and bypasses the stale-index guard | 2026-08-17 |
| ast_env_var_quadratic_parse_2026-06-13 | P1 | closed | AST env-var backing store causes O(N^2) parse time | 2026-08-17 |
| asym_typed_keypair_tuple_corruption_2026-06-15 | P3 | closed | asym_typed_keypair tuple-element corruption on cross-module return | 2026-08-17 |
| async_mutex_blocks_carrier_thread_no_suspend_2026-07-28 | P2 | closed | Async-tier mutex/rwlock block the carrier OS thread instead of suspending | 2026-08-17 |
| async_runtime_detached_completed_results_unbounded_2026-08-13 | P2 | fixed | Detached completed task results are retained unboundedly | 2026-09-13 |
| atomic_write_providers_were_non_atomic_2026-07-19 | P3 | closed | Atomic-write providers were non-atomic; Stage 4 integration still pending | 2026-08-17 |
| backend_linker_check_arm_body_const_assign_2026-07-02 | P3 | fixed | `simple check` on backend/linker files hits unrelated 'cannot assign to const arm_body' | 2026-08-17 |
| backend_optimization_facts_gating_not_enforced_2026-07-20 | P3 | fixed | Backend optimization skip reasons retain optional fact wrappers | 2026-09-13 |
| backend_session_kind_cpu_simd_api_drift_2026-06-01 | P3 | fixed | BackendSessionKind CPU SIMD API drift across the two engine2d tiers | 2026-08-17 |
| backend_trait_undefined_impls_unchecked_2026-07-24 | P2 | closed | Compiler `Backend` trait is declared nowhere; five impls silently unchecked | 2026-08-17 |
| bare_hardware_namespace_import_unresolved_2026-07-20 | P2 | closed | Bare `use hardware.*` imports do not resolve; std. prefix required | 2026-08-17 |
| baremetal_option_field_unwrap_faults_class_2026-07-18 | P1 | closed | Option-unwrap / if-val field access faults on baremetal native codegen | 2026-08-17 |
| bare_trailing_identifier_named_context_fails_to_parse_2026-08-09 | P3 | fixed | Bare trailing expression named `context` parses as an identifier when no context DSL header follows; pure-Simple grammar was already correct and pinned (2/2) | 2026-09-23 |
| base58_decode_reversed_polarity_rootcause_2026-07-29 | P1 | closed | Two default-engine miscompiles reverse base58_decode polarity (silent wrong data) | 2026-08-17 |
| blink_paint_tree_walker_module_missing_2026-07-20 | P2 | closed | blink paint_tree_walker module still missing; spec targets unimplemented module | 2026-08-17 |
| blink_parse_declarations_cross_module_collision_2026-08-11 | P2 | fixed | Blink cascade calls the wrong same-named parse_declarations across modules | 2026-09-18 |
| blink_specs_import_unimplemented_modules_2026-08-10 | P2 | fixed | Four blink specs RED: they import blink modules that do not exist | 2026-09-13 |
| bootstrap_admission_v2_fail_closed_blocks_all_bootstraps_2026-08-17 | P1 | fixed | Bootstrap admission v2 unconditionally fail-closed; no bootstrap can start | 2026-08-17 |
| bootstrap_default_len_is_empty_not_materialized_2026-07-13 | P3 | closed | Bootstrap default Len.is_empty is not materialized | 2026-08-17 |
| bootstrap_diagnostic_missing_child_preflight_2026-08-02 | P3 | fixed | Bootstrap diagnostic sweep missing-child preflight | 2026-09-13 |
| bootstrap_erased_text_rfind_optional_abi_2026-07-13 | P2 | closed | Bootstrap erased-text rfind loses Optional not-found semantics | 2026-08-17 |
| bootstrap_lint_json_validation_false_green_2026-07-23 | P2 | fixed | Bootstrap lint JSON validation accepted malformed output (false green) | 2026-09-13 |
| bootstrap_logging_diagnostics_2026-07-07 | P3 | closed | Bootstrap logging diagnostics incomplete (open-ended remaining items) | 2026-09-13 |
| bootstrap_low_memory_positional_bridge_circularity_2026-07-26 | P2 | closed | Low-memory positional bridge blocked by split pure-binary capabilities | 2026-08-17 |
| bootstrap_main_entry_closure_no_object_progress_2026-07-23 | P2 | fixed | bootstrap_main native build makes no object progress | 2026-09-13 |
| bootstrap_named_tuple_return_parse_2026-07-17 | P2 | fixed | Bootstrap parser rejects labeled tuple return types | 2026-09-13 |
| bootstrap_parser_address_of_cast_2026-07-27 | P2 | closed | Bootstrap parser rejects address-of cast arguments | 2026-08-17 |
| bootstrap_parser_quadratic_source_refetch_2026-07-12 | P2 | closed | Bootstrap parser quadratic source refetch; full bootstrap acceptance open | 2026-08-17 |
| bootstrap_planner_v1_unbound_authorization_2026-08-14 | P1 | closed | Bootstrap planner v1 authorization gap is superseded by the execution-bound v2 producer | 2026-09-14 |
| bootstrap_prefix_address_of_parser_gap_2026-07-27 | P2 | closed | Bootstrap parser rejects prefix address-of expressions | 2026-08-17 |
| bootstrap_progress_watcher_root_only_rss_2026-08-02 | P3 | fixed | Bootstrap progress watcher reports only wrapper RSS, not the child tree | 2026-09-13 |
| bootstrap_pure_simple_stage2_stall_yoon_note_2026-07-02 | P2 | closed | --pure-simple stage2 stalls on yoon-note (7200s timeout, no binary) | 2026-08-17 |
| bootstrap_seed_jit_host_evidence_chain_false_negative_2026-07-27 | P3 | closed | Bootstrap-seed JIT host-evidence chain false negative | 2026-08-17 |
| bootstrap_stage1_native_build_llvm_icmp_segfault_2026-07-09 | P1 | fixed | Stage 1 SIGSEGV in LLVM ConstantFolder::FoldCmp via interpreted LLVMBuildICmp | 2026-09-22 |
| bootstrap_stage2_capability_log_phantom_2026-08-17 | P3 | fixed | Warning references stage2-capability.log that is never written when stage2 fails | 2026-09-13 |
| bootstrap_stage2_empty_mir_bodies_2026-07-05 | P1 | closed | Stage-2 bootstrap: function bodies lower to empty ret-0 stubs | 2026-08-17 |
| bootstrap_stage2_silent_exit1_empty_log_2026-08-17 | P2 | fixed | Stage2 silent exit-1 with 0-byte stage2-native-build.log | 2026-08-17 |
| bootstrap_stage3_module_surface_placeholder_nil_2026-08-01 | P1 | fixed | Stage 3 module-surface placeholder nil trap | 2026-09-22 |
| bootstrap_stage3_selfhost_seed_wrapper_fallback_2026-06-17 | P1 | closed | Stage3 self-host: stage2 binary emits only a seed-wrapper not native code | 2026-09-13 |
| bootstrap_stage4_ast_hir_overlap_memory_2026-07-27 | P1 | closed | Stage 4 AST/HIR overlap exhausts the no-GC heap registry | 2026-08-17 |
| bootstrap_stage4_get_args_infinite_recursion_coredump_2026-06-21 | P1 | fixed | Stage4 binary SIGSEGVs at startup via io.cli_ops.get_args recursion | 2026-09-13 |
| bootstrap_stage4_graph_load_timeout_2026-07-05 | P2 | closed | Stage-4 native-build module-graph loading exceeds the 7200s timeout | 2026-08-17 |
| bootstrap_stage4_hir_import_crash_2026-07-27 | P2 | closed | Stage 4 HIR import crash on unresolved import symbols | 2026-08-17 |
| bootstrap_stage4_optional_arg_and_mixed_tail_miscompile_2026-07-23 | P1 | closed | Seed stage4: optional-in-arg and mixed-tail return miscompiles | 2026-08-17 |
| bootstrap_stage4_seed_compiled_full_cli_run_test_crash_2026-07-20 | P2 | closed | Stage-4 seed-compiled full CLI: 2 startup symptoms still open after SIGSEGV fix | 2026-09-13 |
| browser_animation_jsvalue_symbol_compiler_blocker_2026-07-28 | P2 | closed | Browser animation target blocked by JsValue.Symbol lowering | 2026-08-17 |
| browser_demo_frozen_loading_placeholder_2026-07-12 | P2 | closed | browser_demo app is a frozen Loading placeholder not a browser | 2026-08-17 |
| browser_dom_bridge_css_runtime_blocker_2026-06-14 | P3 | closed | Browser DOM bridge CSS runtime blocker (checks but no runtime evidence) | 2026-08-17 |
| browser_engine_css_float_layout_unimplemented_2026-07-20 | P2 | closed | CSS float/clear layout produces no visible geometry | 2026-08-17 |
| browser_engine_css_size_quadratic_pixel_render_2026-07-04 | P1 | closed | Pixel render scales quadratically with CSS size; spec greenwashed by hard-coded ids | 2026-08-17 |
| browser_engine_free_fn_arg_mutation_lost_2026-06-30 | P1 | closed | Class-instance args to free functions lose mutations in compiled library modules | 2026-09-13 |
| browser_layout_large_simd_fill_facade_unsafe_2026-07-09 | P2 | closed | Large SIMD fill facade is unsafe/unverified beyond count=64 | 2026-08-17 |
| browser_net_real_site_gaps_2026-07-11 | P2 | closed | Browser net stack real-site gaps; pure-Simple TLS transport is a stub | 2026-08-17 |
| browser_network_policy_check_blocker_2026-07-26 | P3 | closed | Browser network policy check blocker (cors.spl cannot be checked) | 2026-08-17 |
| browser_session_animation_target_build_blockers_2026-07-26 | P2 | closed | BrowserSession animation target build blockers (parser rejects compact forms) | 2026-08-17 |
| browser_static_shell_cache_spec_timeout_2026-06-14 | P3 | closed | browser_static_shell_cache_spec times out as a whole even at --timeout 300 | 2026-08-17 |
| browser_text_node_blanks_frame_2026-08-05 | P1 | fixed | Any text node blanks the whole frame; text_painter still unreferenced by browser_renderer | 2026-09-13 |
| browser_webgpu_queue_wasm_memory_sspec_promise_2026-06-14 | P3 | closed | SSpec promise harness cannot express the WebGPU queue WASM-memory scenario | 2026-08-17 |
| bug_sspec_daemon_optional_lookup_equality_divergence_2026-07-20 | P1 | closed | simple test daemon evaluator diverges from simple run on text? lookup + equality | 2026-08-17 |
| build_lint_routes_to_rust_clippy_not_cli_run_lint_2026-07-06 | P2 | closed | `bin/simple build lint` routes to Rust clippy so pure-Simple cli_run_lint never executes | 2026-08-17 |
| build_lint_subcommand_triggers_full_driver_rebuild_2026-06-15 | P3 | closed | `bin/simple build lint <file>` triggers a full cargo/clippy driver rebuild instead of lint | 2026-08-17 |
| bytebuffer_push_byte_freeze_wrong_interp_2026-06-15 | P1 | closed | ByteBuffer.push_byte(v)+freeze() yields wrong byte values in the interpreter (silent data | 2026-08-17 |
| bytespan_equals_boxed_int_pointer_slot_93_guest_faults_2026-07-28 | P1 | closed | ByteSpan.equals faults 93x on a boxed integer in a pointer slot in the SimpleOS WM guest | 2026-08-17 |
| calc_cursor_hidden_row_awareness_divergence_2026-08-11 | P2 | fixed | Calc cursor movement honours hidden rows only in the GUI session, not terminal or interact | 2026-08-17 |
| calculator_canned_content_missing_marker_2026-07-14 | P3 | closed | Calculator canned WM content is emitted without the [canned] provenance marker | 2026-08-17 |
| cancellation_token_two_level_propagation_stale_after_third_alloc_2026-07-29 | P2 | closed | CancellationToken depth-2 cancel propagation reads a stale registry after a third allocati | 2026-08-17 |
| case_bare_ident_is_irrefutable_binding_2026-08-01 | P1 | fixed | A bare identifier in `case` position silently becomes an irrefutable binding, matching eve | 2026-08-17 |
| cert_chain_signature_verification_missing_2026-07-17 | P1 | closed | TLS chain-of-trust verify_signature has no implementation, so cert chains are never crypto | 2026-08-17 |
| chacha20_poly1305_seal_open_api_mismatch_2026-07-20 | P2 | closed | chacha20_poly1305_seal/_open raw-[u8] API the specs call does not exist; two incompatible | 2026-08-17 |
| chained_static_ctor_receiver_drops_mutation_2026-08-01 | P1 | closed | A mutating method chained directly off a static constructor call is a silent no-op | 2026-09-13 |
| check_directory_target_false_green_2026-07-24 | P2 | closed | `simple check` on a directory target reports green without checking the directory contents | 2026-08-17 |
| check_unknown_option_false_green_2026-07-23 | P2 | fixed | `simple check` accepts an unknown option and exits green instead of erroring | 2026-09-13 |
| chore_commit_941605d43d9_hidden_semantic_changes_2026-08-01 | P2 | closed | Glob-imported `main` no longer enters functions/env/MODULE_GLOBALS so bare-name calls now | 2026-09-13 |
| ci_gate_enforcement_surface_2026-07-07 | P3 | closed | check-repo-hygiene.shs is RED on content debt and its CI job never goes green | 2026-08-17 |
| class_field_reference_semantics_diverge_2026-08-06 | P1 | closed | Interpreter value-copies class fields while the JIT crashes on an optional class field | 2026-08-17 |
| class_named_arg_out_of_order_drops_field_2026-06-30 | P2 | fixed | Class constructor drops fields when named args are given out of declaration order | 2026-08-17 |
| cli_driver_binary_repo_seed_infinite_delegation_loop_2026-07-25 | P1 | closed | `bin/simple run` enters an infinite seed-delegation loop that blocks all execution | 2026-08-17 |
| cli_driver_binary_symlink_argv0_2026-07-11 | P2 | closed | _cli_driver_binary() seed-sibling lookup fails when argv0 is a symlink | 2026-08-17 |
| cli_global_flags_check_timeout_2026-07-05 | P2 | closed | `simple check` times out parsing the CLI global-flag parser file | 2026-08-17 |
| cli_help_dispatch_alignment_gate_red_2026-08-09 | P2 | fixed | cli_help_alignment_spec is RED: `simple --help` and dispatch have drifted by 18 commands | 2026-09-13 |
| closure_param_cross_module_result_mistag_2026-07-28 | P2 | closed | Cross-module closure-param invocation mis-tags its result value in the seed run lane | 2026-08-17 |
| closure_selective_capture_skips_non_expression_statements_2026-07-27 | P2 | fixed | The JIT still substitutes 0 for a closure's lost direct read even after the capture walker | 2026-08-17 |
| codegen_bare_method_receiver_type_blind_candidate_selection_2026-07-28 | P1 | closed | Bare-method codegen binds a candidate by name-suffix with no receiver-type check (silent w | 2026-08-17 |
| codegen_large_match_dispatch_body_2026-07-27 | P2 | closed | Codegen fails on _dispatch_function, a 236-arm match with a 2497-line body | 2026-08-17 |
| collection_desugar_scalar_merge_rewrite_2026-07-29 | P2 | closed | collection desugar still rewrites x = x + ident to x.merge(ident) on scalars | 2026-08-17 |
| common_encoding_yaml_broken_cross_submodule_import_2026-07-20 | P2 | fixed | encoding/yaml.spl imports std.common.yaml.* which has no __init__.spl barrel | 2026-08-17 |
| commonjs_granted_module_execution_limitations_2026-06-01 | P3 | closed | CommonJS require/__filename limitations in granted module execution | 2026-08-17 |
| compiled_checker_asm_volatile_indent_gap_2026-08-03 | P2 | closed | Compiled checker rejects asm-volatile indented block in riscv cmo.spl | 2026-09-13 |
| compiled_checker_pure_parser_parity_gaps_2026-08-02 | P2 | fixed | Compiled checker rejects 247 reproduced repository sources (parser parity) | 2026-08-17 |
| compile_format_smf_nil_receiver_crash_2026-07-31 | P2 | fixed | simple compile --format=smf crashes on nil receiver | 2026-09-13 |
| compile_lane_false_fails_globals_in_mainless_modules_2026-07-29 | P2 | closed | bin/simple compile false-fails main-less modules with a module-level global | 2026-08-17 |
| compiler_cross_module_private_symbol_collision_2026-06-16 | P1 | closed | Private _-prefixed functions collide across modules; wrong fn called | 2026-08-17 |
| compositor_render_all_color_name_collapse_2026-08-06 | P2 | closed | Compositor.render_all unrunnable: two Color declarations collapse by name | 2026-09-13 |
| compress_lz4_empty_payload_roundtrip_corruptstream_2026-07-20 | P2 | fixed | LZ4 auto-frame round-trip rejects its own empty-payload output as corrupt | 2026-08-17 |
| context_block_outer_var_write_lost_under_test_2026-07-20 | P2 | fixed | context <obj>: block body writes to an outer var are lost under test | 2026-08-17 |
| contract_expr_forall_ge_call_member_not_found_2026-07-20 | P2 | fixed | ContractExprKind.Forall and ContractExpr.ge/.call report not-found cross-module | 2026-08-17 |
| core_c_capsule_gate_wrongly_opted_out_of_guard_wiring_2026-08-06 | P3 | fixed | core-C capsule gate still opted out of guard wiring on a false rationale | 2026-08-17 |
| core_c_runtime_archive_rename_enoent_flaky_2026-07-26 | P3 | fixed | Residual archive-build rename race (silent-degradation half fixed) | 2026-09-13 |
| core_c_string_len_registry_2026-06-02 | P2 | fixed | core-c .len() garbage: rt_string_len registry check rejects compiler literals | 2026-09-13 |
| coverage_entry_misfiling_is_not_bounded_at_two_lines_2026-08-04 | P2 | fixed | Coverage <entry> misfiling swallows method bodies, up to 21 points per module | 2026-08-17 |
| cpu_simd_direct_fill_full_bootstrap_stage4_spin_2026-07-08 | P2 | closed | Full-bootstrap Stage 4 spins on the CPU-SIMD direct-fill lane | 2026-08-17 |
| cpu_simd_engine2d_rvv_native_rows_missing_2026-07-08 | P3 | closed | RVV proof recorded, but .spl detection-branch legs still blocked | 2026-08-17 |
| cpu_simd_external_cairo_8k_perf_gap_2026-07-09 | P2 | closed | CPU-SIMD external Cairo 8K perf gap | 2026-08-17 |
| cpu_simd_mutable_array_extern_wiring_2026-05-31 | P2 | closed | CPU SIMD mutable-array extern wiring absent; cpu_simd backend aliases CpuBackend | 2026-08-17 |
| cranelift_direct_string_constant_null_pointer_2026-07-12 | P1 | closed | native-build --backend cranelift: string constants compile to a null pointer | 2026-08-17 |
| cranelift_native_aggregate_return_nil_receiver_hosted_wm_2026-07-26 | P1 | closed | Cranelift native lane decodes aggregate/Option returns as nil receivers | 2026-08-17 |
| cranelift_noparen_method_access_miscompiles_2026-07-06 | P1 | closed | Cranelift miscompiles zero-arg method access without parens on structs | 2026-08-17 |
| cranelift_runtime_initialized_float_global_2026-07-19 | P2 | fixed | Cranelift rejected runtime-initialized float globals | 2026-08-17 |
| cranelift_seed_missing_sffi_externs_2026-07-16 | P2 | closed | Deployed seed lacks 9 rt_cranelift_* SFFI externs; strict-cranelift build cannot run | 2026-08-17 |
| cranelift_u8_array_literal_data_pointer_garbage_2026-07-06 | P1 | closed | Cranelift emits garbage data pointer for [u8] array literals in freestanding build | 2026-08-17 |
| cranelift_unannotated_module_bool_global_tagbox_truthy_2026-07-27 | P1 | closed | Module-level val x = false stored tag-boxed (19) and reads TRUTHY | 2026-08-17 |
| crash_signal_bundle_extern_gap_2026-07-29 | P3 | closed | No Simple-reachable hook from SIGSEGV/SIGABRT into CrashBundleV1 | 2026-08-17 |
| credential_kdf_multi_derivation_spec_aborts_runner_2026-08-08 | P2 | fixed | Multi-derivation bcrypt KDF spec aborts test child rc=255 with no verdict | 2026-08-17 |
| credential_key_file_write_has_no_mode_argument_2026-08-08 | P2 | fixed | Secret files created world/group-readable then narrowed; no write-with-mode primitive | 2026-09-13 |
| credential_store_module_level_val_reads_wrong_2026-08-08 | P2 | fixed | credential_kdf_cost returns wrong value; module-level val reads wrong constant | 2026-09-13 |
| cross_clang_codegen_broken_2026-07-06 | P2 | closed | Cross clang-20 SIGABRTs on all codegen at -O1 and above | 2026-08-17 |
| cross_import_const_no_hir_linkage_2026-07-25 | P2 | closed | Imported module-level const has no cross-module HIR linkage | 2026-08-17 |
| cross_module_imported_fn_mutation_not_propagating_2026-07-12 | P1 | closed | Imported function mutation not propagating to caller's instance (wrong dispatch) | 2026-08-17 |
| crypto_digest_generic_struct_2026-06-15 | P2 | closed | Generic struct type parameter not resolved in impl block | 2026-08-17 |
| crypto_interp_watchdog_timeout_heavy_pqc_specs_2026-07-20 | P3 | closed | Interpreter-mode watchdog timeout on 7 heavy crypto/PQC KAT specs | 2026-08-17 |
| crypto_reference_signature_key_ops_unresolvable_2026-07-20 | P2 | fixed | std.signature.key_ops has no .spl source; whole spec cannot load | 2026-09-13 |
| crypto_sffi_random_hex_degrades_to_empty_string_on_entropy_failure_2026-08-08 | P2 | fixed | random_hex degrades to empty string on CSPRNG failure; random_salt inherits it | 2026-09-13 |
| cuda_backend_gpu_warp_ballot_arity_mismatch_2026-07-20 | P2 | closed | CUDA backend requires 2 args for gpu_warp_ballot but intrinsic takes 1 | 2026-08-17 |
| cuda_ffi_is_available_and_device_count_wrong_2026-08-09 | P2 | fixed | CudaFfi.is_available() false and device_count() 0 on host with two GPUs | 2026-09-13 |
| cuda_font_companion_package_trust_anchor_2026-07-15 | P3 | closed | CUDA font companion lacks a production package trust anchor | 2026-08-17 |
| cuda_lane_session_create_unresolved_across_module_boundary_2026-08-07 | P2 | closed | CudaLaneSession.create() unresolved across module boundary | 2026-09-13 |
| cuda_resident_session_missing_mapped_memory_and_watchdog_sffi_2026-08-07 | P2 | fixed | CUDA resident session needs cuMemHostAlloc/cuMemHostGetDevicePointer/cuDeviceGetAttribu... | 2026-08-17 |
| cuda_resident_session_run_program_discards_arena_data_region_state_2026-08-08 | P2 | closed | run_source/run_program discard arena DATA-region state every call | 2026-09-13 |
| dangling_reference_checker_symlink_and_untracked_blind_spots_2026-07-28 | P3 | closed | check-dangling-references false positives on symlinked trees and untracked providers | 2026-08-17 |
| dap_spec_stubs_reported_green_without_asserting_2026-08-08 | P3 | fixed | DAP spec examples reported GREEN while asserting nothing | 2026-09-13 |
| declared_return_type_not_enforced_2026-08-09 | P1 | fixed | HIR lowering enforces declared function return types for explicit and implicit return expressions | 2026-09-14 |
| decorator_aop_interpreter_fallback_noop_2026-07-20 | P2 | fixed | @decorator wrapping and AOP pc{} weaving are no-ops under the tree-walking interpreter | 2026-08-17 |
| deep_recheck_2026-07-05 | P2 | closed | Deep-recheck bug inventory 2026-07-05 (umbrella, mixed status) | 2026-08-17 |
| deployed_binary_interp_extern_and_module_table_constraints_2026-07-07 | P3 | closed | Deployed binary: interpret-mode extern registration + baked module table constraints | 2026-08-17 |
| deployed_bin_simple_bootstrap_only_2026-07-31 | P2 | fixed | Deployed bin/simple is bootstrap-only: no test/run/lint, cannot parse @extern | 2026-08-17 |
| deployed_bin_simple_still_seed_2026-08-05 | P2 | fixed | Deployed bin/simple is still the Rust seed, not the self-hosted binary | 2026-08-17 |
| deployed_seed_test_runner_init_hang_2026-07-17 | P3 | closed | Deployed release binary: single-file simple test hangs on ALL specs (stale seed) | 2026-08-17 |
| deployed_selfhost_env_set_miscompile_segv_2026-07-14 | P1 | closed | Tracked release/ pure-Simple CLI SIGSEGVs in setenv: rt_env_set gets a boxed int as char* | 2026-08-17 |
| diag_stage_facet_cross_module_collision_under_test_2026-07-06 | P2 | fixed | Bare-name function registry lets dbg_stage collide cross-module, aborting specs with type | 2026-08-17 |
| dict_array_contains_raw_untagged_key_2026-08-02 | P1 | fixed | rt_contains gets an untagged key so dict .has()/in returns false for a key that is present | 2026-08-17 |
| dict_class_field_contains_key_after_insert_2026-08-08 | P1 | closed | Bracket-read self.d[k] on a class-field {i64:[i64]} dict segfaults under native-build | 2026-08-17 |
| dict_struct_key_iteration_single_entry_2026-06-13 | P2 | closed | Dict with struct/composite keys iterates fewer entries than inserted in the interpreter | 2026-09-13 |
| digest_hex_double_import_corruption_2026-06-15 | P1 | closed | Digest.hex() returns struct-representation bytes when seam.spl and ctypes are both | 2026-08-17 |
| disk_image_fat32_builder_defects | P2 | fixed | FAT32 builder writes dirent names verbatim-with-dot instead of 8.3 and truncate silently | 2026-09-18 |
| doc_coverage_csv_exporter_missing_nl_docitem_ctors_2026-07-20 | P2 | fixed | DocItem has no create_class/create_enum static methods and NL is unresolved in | 2026-08-17 |
| doc_nav_spec_stale_doc_spec_path_and_dual_tree_ambiguity_2026-07-20 | P3 | closed | doc_nav_spec reads dead doc/spec/ paths so every assertion runs against empty strings | 2026-08-17 |
| docs_titled_commit_2313821fd77_reverted_five_landed_fixes_2026-08-10 | P1 | closed | No pre-push guard detects a stale-WC snapshot that deletes 7053 lines while keeping file | 2026-08-17 |
| doctest_parser_spec_api_mismatch_2026-07-20 | P3 | closed | parser_spec asserts DoctestItem.code/.setup/.teardown fields that the class does not | 2026-08-17 |
| dotq_existence_check_is_scalar_truthiness_on_jit_2026-07-27 | P1 | closed | .? lowers to a raw scalar truthiness test on JIT/native so 0.? is false and .? is true | 2026-08-17 |
| dot_question_truthy_op_returns_payload_as_call_arg_2026-07-20 | P2 | fixed | x.? passed directly as a bool-typed call argument evaluates to the payload, not true | 2026-09-13 |
| draw_ir_sdn_roundtrip_composition_field_assign_on_non_object_2026-08-15 | P2 | fixed | SDN-roundtripped Draw IR composition renders with cannot assign field on non-object | 2026-09-13 |
| draw_ir_window_shadow_clipped_2026-07-13 | P3 | closed | WM window shadow RECT is clipped by the embedded surface and overwritten by the body RECT | 2026-08-17 |
| ds_utils_t_optional_wrapping_inconsistency_2026-06-26 | P2 | fixed | Same -> T? method returns Option::Some(N) in one call site and bare N in another | 2026-08-17 |
| dual_backend_generic_typed_seam_2026-06-15 | P2 | closed | Generic fn with a trait bound fails with Unknown type: T in the interpreter | 2026-08-17 |
| duplicate_hirtype_enum_decls_drop_module_to_interpreter_2026-08-04 | P3 | fixed | 26 duplicate `enum HirType` declarations still shadow the canonical struct as a latent | 2026-08-17 |
| ecc_p384_p521_sign_verify_broken_2026-07-20 | P1 | closed | ECDSA P-384 sign returns a 0-byte signature and NIST CAVP verify fails on P-384 and P-521 | 2026-08-17 |
| ecdsa_p256_sign_verify_roundtrip_broken_2026-07-20 | P1 | closed | ECDSA P-256 verify rejects a 64-byte signature this repo's own sign just produced | 2026-08-17 |
| ed25519_live_baremetal_self_test_unproven_2026-06-06 | P2 | closed | Ed25519 baremetal self-test in the SSHD QEMU lane has never produced a passing transcript | 2026-08-17 |
| ed25519_rfc8032_t_sha_abc_pubkey_mismatch_2026-07-20 | P1 | closed | RFC8032 7.1 T_SHA_ABC vector: ed25519 derives the wrong public key and verify fails | 2026-08-17 |
| ed25519_scalar_mul_ct_regression_2026-07-20 | P1 | closed | ed_scalar_mul_basepoint delegates to _simple which branches on each secret scalar bit | 2026-08-17 |
| editor_ide_render_example_jit_static_self_2026-05-30 | P3 | fixed | IDE render example falls back off JIT on a static-method self diagnostic | 2026-08-17 |
| electron_keyboard_modifiers_dropped_2026-07-05 | P2 | closed | Electron backend drops all keyboard modifier state and most non-printable keys | 2026-08-17 |
| electron_mdi_unreachable_from_live_entrypoint_2026-07-05 | P2 | closed | Electron MDI windows exist in ui_shared_mdi but no live entrypoint reaches them | 2026-08-17 |
| electron_open_file_dialog_unbounded_stdin_wait_2026-07-05 | P2 | closed | Electron open_file_dialog blocks in `while true` on stdin with no timeout | 2026-08-17 |
| electron_renderdoc_vulkan_widget_capture_launch_diagnostics_2026-06-28 | P3 | closed | Electron RenderDoc widget capture gate reports gpu_process_exit_status=fail | 2026-08-17 |
| elf_parser_relocations_merged_without_target_section_2026-08-08 | P1 | fixed | linker/elf_parser.spl ElfObject.relocations merges every SHT_RELA without recording sh_... | 2026-08-17 |
| emit_smf_stub_drops_module_content_2026-06-12 | P1 | closed | --emit-smf writes a 219-byte stub regardless of module content | 2026-08-17 |
| engine2d_backend_probe_result_missing_hardening_methods_2026-07-20 | P3 | closed | Engine2D BackendProbeResult still lacks is_hardware() present on the 3D counterpart | 2026-08-17 |
| engine2d_completed_frame_snapshot_gap_2026-07-10 | P2 | closed | Engine2D exposes no completed-frame snapshot, so render evidence cannot be captured | 2026-08-17 |
| engine2d_cpu_offscreen_render_commands_first_frame_fault_2026-07-17 | P2 | closed | CPU-rasterizer offscreen/embedded batch faults on the first frame in render_commands | 2026-08-17 |
| engine2d_interpreted_mirror_dominates_render_2026-07-03 | P2 | closed | Per-op interpreted mirror runs before every backend op, making all backends equally slow | 2026-08-17 |
| engine2d_metal_draw_image_parity_coverage_gap_2026-07-07 | P3 | fixed | draw_image/kernel_blit_image has a Metal dispatch path but zero CPU-vs-Metal parity cov... | 2026-09-13 |
| engine2d_metal_gpu_only_clip_unimplemented_2026-07-06 | P3 | closed | Metal GPU-only-mode scissor clip is implemented but has no native execution evidence | 2026-08-17 |
| engine2d_read_pixels_provenance_gap_2026-06-14 | P2 | closed | read_pixels cannot prove whether returned pixels came from GPU readback or the CPU mirror | 2026-08-17 |
| engine2d_render_evidence_spec_missing_module_2026-08-08 | P2 | fixed | engine2d_render_evidence_spec.spl imports os.compositor/x86.render_capture_ack module t... | 2026-08-17 |
| engine2d_simd_gpu_layer_audit_2026-08-08 | P3 | fixed | SIMD/GPU-backend layer audit findings filed but most were not fixed | 2026-09-13 |
| engine2d_simd_span_kernels_slower_and_fill_colour_corrupt_2026-08-06 | P1 | closed | engine2d SIMD fill_span corrupts the fill colour via bad marshalling, so it cannot be a... | 2026-09-13 |
| engine2d_vulkan_software_showcase_frame_divergence_2026-07-02 | P2 | closed | Vulkan and Software backends differ on 1136/30000 px of the text-heavy showcase frame | 2026-08-17 |
| engine2d_vulkan_translation_vk_version_2026-07-10 | P3 | closed | VulkanBackend.create() mis-resolves because the translation requires a missing vk_versi... | 2026-08-17 |
| engine3d_vulkan_world_font_depth_write_disabled_2026-07-13 | P3 | fixed | Engine3D Vulkan world-font depth write is disabled; source fixed but never run natively | 2026-09-18 |
| engine_lib_api_surface_drift_vs_spec_2026-07-20 | P2 | closed | engine/skia lib API surface has drifted from what unit specs call | 2026-08-17 |
| enum_assoc_fn_residual_exposure_2026-07-28 | P1 | fixed | 1611 non-spec call sites of enum associated fns (incl. smf_cache Platform.from_u8) are... | 2026-09-13 |
| enum_associated_fn_never_called_on_jit_2026-07-28 | P1 | closed | EnumName.assoc_fn() is never invoked under the JIT - returns a bogus value with no error | 2026-08-17 |
| enum_associated_fn_vacuous_spec_sweep_2026-07-28 | P2 | closed | Unknown count of specs pass vacuously because the JIT enum-associated-fn hijack fakes r... | 2026-08-17 |
| enum_field_in_nested_call_arg_join_not_found_2026-08-17 | P2 | fixed | Struct literal with enum-typed field inside a call arg fails with method join not found | 2026-08-17 |
| enum_impl_static_fn_method_call_path_skips_impl_methods_2026-07-20 | P2 | closed | EnumName.static_method() reports unknown variant or method when declared in a separate impl block | 2026-08-17 |
| enum_impl_static_fn_scoping_2026-07-29 | P1 | closed | Declared enum associated fns yield silent wrong values on the JIT engine | 2026-08-17 |
| enum_pattern_match_optional_value_silent_fallthrough_2026-07-20 | P1 | closed | match on a T? enum silently falls through to _ for every field-binding variant arm | 2026-08-17 |
| enum_payload_dict_copied_on_function_return_2026-07-28 | P1 | closed | Dict payload inside an enum is copied at the function-return boundary so later writes are lost | 2026-08-17 |
| enum_variant_struct_name_collision_census_2026-07-30 | P2 | closed | Same-named structs shadow enum variants in bare match patterns beyond the fixed SymbolKind case | 2026-09-13 |
| env_get_nil_coalesce_dead_fallback_2026-07-25 | P1 | closed | env_get(...) ?? default never takes the fallback because env_get returns text  not text? | 2026-08-17 |
| excel_floor_ceiling_negative_significance_sign_2026-07-20 | P2 | closed | excel_floor/excel_ceiling return the wrong value for negative significance (must use abs) | 2026-08-17 |
| exec_cap_check_caller_identity_not_threaded_2026-08-07 | P2 | fixed | exec_cap_check's scalar-caller ABI cannot carry a CapabilitySet so non-kernel callers are always denied | 2026-08-17 |
| exp_cli_script_delegation_falls_back_to_usage_2026-07-20 | P2 | closed | exp CLI prints its usage banner instead of delegating to the experiment script | 2026-08-17 |
| expect_comparison_to_equal_footgun_2026-07-17 | P3 | closed | ~1,360 spec lines still route comparisons through expect(a==b).to_equal(false) | 2026-08-17 |
| extern_class_constructor_not_found_simpleerror_2026-08-02 | P2 | closed | Constructing extern class SimpleError fails with E1002 / cannot infer field type | 2026-09-13 |
| extern_return_type_mismatch_object_to_int_2026-07-21 | P1 | closed | A function returning an extern fn call result fails: cannot convert object to int | 2026-08-17 |
| f64_integral_to_text_drops_fraction_2026-07-25 | P2 | closed | Integral f64 interpolates as 1 instead of 1.0, losing float identity in text | 2026-08-17 |
| failed_to_load_imported_types_is_only_a_warning_2026-08-07 | P2 | fixed | Unresolvable module import is only a WARN, so type checking proceeds with zero imported types | 2026-09-13 |
| fat32_database_atomic_replace_recovery_missing_2026-08-14 | P1 | fixed | Fat32Filesystem.rename_at is not atomic and mount performs no journal recovery | 2026-09-18 |
| fault_detection_module_var_mutation_2026-06-26 | P1 | closed | Module-level var mutations made inside a called function are not visible to the caller | 2026-08-17 |
| feature_section_failures_2026-07-18 | P2 | closed | Residual open buckets from the 815-failure triage (animation module, rt_engine2d SFFI, unparseable summaries) | 2026-08-17 |
| fe_p256_field_module_missing_2026-08-04 | P2 | closed | std.common.math.field.fe_p256 does not exist so 2 specs and 43 examples cannot run | 2026-08-17 |
| fetch_wasm_chain_spec_runner_premature_child_termination_2026-06-30 | P2 | closed | Test runner reports file-level FAIL with truncated output while the spec passes 250/250 directly | 2026-08-17 |
| file_read_bytes_has_six_definitions_with_three_return_types_2026-08-09 | P2 | fixed | file_read_bytes still has four definitions split between [u8] and [i64] return types | 2026-09-13 |
| flat_ast_export_from_and_type_alias_loss_2026-07-27 | P2 | closed | Flat AST drops the provider module of `export X from M` and never dispatches `type Name = Target` | 2026-08-17 |
| font_render_batch_transform_identity_default_not_applied_2026-07-19 | P2 | closed | FontRenderBatch.transform_identity class default reads back empty on freestanding, | 2026-08-17 |
| font_renderer_cache_nested_aggregate_loss_2026-07-27 | P2 | closed | WM font metric resolve returns has_ttf=0 on 117/118 lookups; nested array-bearing | 2026-08-17 |
| for_in_custom_struct_no_iterator_protocol_2026-06-15 | P2 | closed | for x in <custom struct> iterates zero times with no error or diagnostic | 2026-08-17 |
| freestanding_entry_module_constants_zero_stubs_2026-07-11 | P1 | closed | Stage3 cranelift freestanding emits entry-module scalar vals as weak fns returning zero | 2026-08-17 |
| freestanding_module_val_initialization_before_io_2026-07-11 | P2 | closed | freestanding module-level val hardware port constants read as zero before module init in | 2026-08-17 |
| freestanding_wrapper_profile_i32_global_var_shifted_2026-07-02 | P2 | closed | cranelift freestanding wrapper profile reads module-level i32 var back shifted right by 3 | 2026-08-17 |
| game2d_breakout_interpreter_60s_session_slow_2026-07-02 | P3 | fixed | 3600-frame rendered Breakout session costs ~14s/frame in the interpreter so it cannot | 2026-08-17 |
| game2d_engine2d_compute_adapter_capsule_boundary_2026-05-31 | P3 | closed | game2d cannot use the shared compute-session path: either adapter placement trips a | 2026-08-17 |
| gap_tls_13_key_schedule_missing_2026-06-15 | P2 | closed | Pure-Simple TLS server has no 1.3 handshake secret derivation, Finished verify, or record | 2026-08-17 |
| gap_tls_server_alpn_missing_2026-06-15 | P2 | closed | server-side ALPN selection is never fed a live ClientHello, so no accepted connection | 2026-08-17 |
| gap_tls_stream_wrapper_missing_2026-06-15 | P2 | closed | accepted TcpStream has no encrypted overlay that frames, authenticates and decrypts TLS | 2026-08-17 |
| gc_analysis_desugar_dropped_method_bodies_2026-08-02 | P1 | closed | gc_analysis mod.spl method bodies were dropped by desugaring, so GC safety analysis | 2026-08-17 |
| gc_async_mut_gpu_ffi_facades_are_dangling_2026-08-09 | P2 | fixed | all four gc_async_mut engine2d ffi_* facades export-use modules that do not exist on disk | 2026-09-13 |
| gc_config_with_heap_size_cross_module_collision_2026-07-20 | P2 | closed | GcConfig.with_heap_size reports unknown static method though declared, while default() on | 2026-08-17 |
| gc_module_loader_spec_asserts_gc_sync_mut_absent_2026-08-17 | P2 | fixed | gc_module_loader_spec asserts src/lib/gc_sync_mut is absent; it holds 867 .spl files | 2026-09-13 |
| gc_nogc_memory_audit_findings_2026-06-11 | P2 | closed | gc mode is allocate-and-leak: codegen never emits free/collect and gc/nogc binaries are | 2026-08-17 |
| generated_gui_full_web_css_evidence_timeout_2026-06-02 | P3 | closed | full production Web UI CSS (38KB) exceeds the 60s parity-evidence watchdog under | 2026-08-17 |
| generate_rv64_test_program_package_missing_impl_2026-07-20 | P2 | closed | src/hardware/fpga_linux/generate_rv64_test_program_package.spl does not exist so its only | 2026-08-17 |
| generator_take_returns_empty_after_name_collision_fix_2026-08-17 | P1 | fixed | std.generator take(generate_range(0,3), 2) returns an empty array instead of [0, 1], exit | 2026-09-13 |
| generic_static_method_type_param_unresolved_2026-07-25 | P2 | closed | static fn whose signature mentions the class type param T is unresolvable | 2026-08-17 |
| gen_lean_cli_infinite_recursion_2026-06-30 | P2 | closed | bin/simple gen-lean recurses without bound because the wrapper re-invokes bin/simple | 2026-08-17 |
| glyph_raster_cache_text_array_index_corrupt_zero_hit_rate_2026-08-06 | P2 | closed | module-level [text] glyph-raster cache index read is corrupt under native/JIT so lookup | 2026-09-13 |
| gpu_perf_measurement_harness_runtime_blocked_2026-07-10 | P2 | closed | gpu_perf_compare.spl exits 139 on entering the CUDA dlopen SFFI path; no deployed GPU | 2026-09-13 |
| graphics_2d_showcase_nil_receiver_2026-07-11 | P2 | closed | Engine2D.create_offscreen boxed backend traps 'field access on nil receiver' exit=132 | 2026-08-17 |
| gui_showcase_4k_bin_simple_native_assignment_target_2026-06-27 | P2 | fixed | check-widget-showcase-4k-200fps.shs fails 'semantic: invalid assignment: unsupported | 2026-08-17 |
| gui_smf_dynlib_hot_call_runtime_missing_2026-06-01 | P3 | closed | macOS arm64 .dylib SMF hot-call evidence still missing; only Linux host evidence passes | 2026-09-13 |
| gui_web_2d_completion_static_cache_isolation_timeout_2026-06-28 | P3 | closed | gui_web_2d_goal_completion_criteria_spec needs a shared static cache dir, a concurrency | 2026-08-17 |
| hda_pure_simple_pci_scan_phase3_sigsegv_2026-07-29 | P2 | closed | Pure-Simple x86 PCI config-port scan via rt_port_inl/outl segfaults (exit 139) after | 2026-09-13 |
| hir_lowering_bool_field_infer_imported_struct_2026-07-03 | P2 | closed | HIR lowering cannot infer a bool field type on a cross-module struct, dropping the run to | 2026-08-17 |
| hir_lowering_quadratic_symbol_define_2026-07-28 | P1 | fixed | Per-module HIR lowering time regressed 262x (tokens module 1960ms to 512761ms), blocking | 2026-09-13 |
| hir_stmt_expr_payload_extraction_nil_2026-07-17 | P1 | fixed | StmtKind.Expr single-arm payload extraction returns nil intermittently, independent of | 2026-09-13 |
| hosted_string_trim_case_raw_receiver_degrades_2026-08-11 | P1 | fixed | rt_string_trim still returns the raw pointer untrimmed and rt_string_ascii_case still | 2026-08-17 |
| hosted_wm_capture_put_pixel_lowering_2026-07-19 | P2 | closed | Self-hosted lowering reports 'Unknown variable: width' in | 2026-08-17 |
| hpack_huffman_single_symbol_decode_empty_2026-06-30 | P2 | closed | hpack_huffman_decode([0x1F],0,1) returns Ok([]) dropping symbol 97, and concat-built [u8] | 2026-08-17 |
| hwir_foundation_spec_residual_failures_2026-08-16 | P2 | fixed | hwir_foundation_spec.spl has 21 substantive failures (17x expected false to equal true) | 2026-08-17 |
| i8_array_literal_reads_back_wrong_value_2026-08-17 | P1 | fixed | [5i8, 6i8] reads element 0 back as 43 under the cranelift JIT with no diagnostic | 2026-08-17 |
| ide_feature_check_jit_fallback_static_self_2026-06-01 | P2 | closed | IDE --feature-check falls back to interpreter with 'cannot use self in static method' HIR | 2026-09-13 |
| ide_feature_check_tui_mode_falsy_call_result_2026-07-20 | P2 | closed | ide --feature-check --tui: truthy call result evaluates to 0, TUI branch never taken | 2026-08-17 |
| if_expression_dead_branch_binds_empty_list_2026-08-06 | P1 | closed | if-expr with constant-false condition binds the DEAD branch's [] not the live value | 2026-08-17 |
| interp_aot_source_pipeline_stubbed_non_functional_2026-06-25 | P2 | closed | AOT source-compile pipeline returns empty HirModule(functions:{}) under seed interpreter | 2026-08-17 |
| interp_crossmod_local_slot_aliasing_2026-06-15 | P1 | closed | Cross-module fn receiving a local object arg aliases the caller's local slot | 2026-08-17 |
| interp_dict_class_value_copy_on_get_mutation_loss_2026-07-06 | P1 | closed | Dict<K,ClassInstance>.get()/.set() copies the value so mutations are silently lost | 2026-08-17 |
| interp_enum_match_class_name_collision_2026-07-06 | P2 | closed | Enum-variant match returns nil when a class shares the variant name (closure-dependent) | 2026-08-17 |
| interp_expect_inline_equality_arg_misevaluates_2026-07-07 | P1 | fixed | expect(a == b).to_equal(false) mis-evaluates the inline == argument | 2026-08-17 |
| interp_expect_to_equal_swallows_failures_multi_describe_2026-06-15 | P1 | closed | expect().to_equal() swallows failures in specs with multiple describe blocks | 2026-08-17 |
| interp_f64_nested_struct_payload_zero_2026-06-14 | P1 | closed | f64 payloads zero out flowing through deeply nested struct/enum returns in stage4 interp | 2026-09-13 |
| interp_if_val_some_expression_form_field_access_2026-07-31 | P2 | fixed | if val Some(x) = opt: EXPR else: EXPR2 loses field access on x in value position | 2026-09-13 |
| interp_imported_enum_inline_methods_variants_dropped_2026-06-30 | P2 | closed | std.sdn.* resolves to a stale bundled stdlib copy with a divergent SdnValue API | 2026-08-17 |
| interp_io_runtime_env_get_option_text_corruption_2026-06-19 | P2 | closed | std.io_runtime.env_get returns corrupted text under bin/simple run | 2026-09-13 |
| interp_logical_short_circuit_2026-07-15 | P1 | fixed | Interpreter and/or eagerly evaluate the right operand instead of short-circuiting | 2026-08-17 |
| interp_match_expr_binding_scope_leak_2026-07-15 | P2 | fixed | Interpreter match-expression bindings leak out into the caller's scope | 2026-08-17 |
| interp_mixed_numeric_arithmetic_2026-07-15 | P2 | fixed | Interpreter mixed integer/float arithmetic returns wrong values or is rejected | 2026-08-17 |
| interp_option_struct_semantics_macos_parity_2026-07-25 | P2 | closed | Option/struct interpreted-lane semantics differ on macOS in deployed and stage4 binaries | 2026-08-17 |
| interp_parse_module_arena_visibility_crash_2026-06-16 | P2 | fixed | Interpreted parse_module + arena decl access crashes in convert_decl_visibility | 2026-09-13 |
| interp_parse_superlinear_2026-06-12 | P2 | closed | Lean-parser parse_module is superlinear and degrades per call under the interpreter | 2026-09-13 |
| interpreted_engine2d_full_res_render_slow_2026-07-02 | P3 | closed | Interpreted Engine2D cpu backend renders one 640x480 frame in ~9.3s, pushing capture specs to ~101s | 2026-09-13 |
| interpreter_bare_arg_not_some_wrapped_at_optional_param_2026-08-04 | P1 | fixed | Bare arg at a T? param is not Some-wrapped so case Some(x) matches no arm (silent fall-through) | 2026-08-17 |
| interpreter_cross_module_enum_discriminant_3_compares_false_2026-08-04 | P1 | closed | Cross-module enum variant with discriminant 3 compares FALSE in the interpreter (silent wrong result) | 2026-08-17 |
| interpreter_first_class_fn_dispatch_drops_nested_array_writeback_2026-08-09 | P1 | fixed | Two mutating me calls in one first-class-fn-dispatched invocation drop the first nested array write | 2026-09-13 |
| interpreter_if_val_nil_mismatch_option_2026-07-03 | P2 | fixed | if val x = <nil Option> wrongly takes the match branch in the interpreter | 2026-09-13 |
| interpreter_ifval_optioncheck_return_divergence_2026-07-17 | P2 | fixed | Seed interpreter diverges from native on if val v = x.? and on return inside a value-match arm | 2026-09-13 |
| interpreter_list_generic_nil_2026-06-12 | P2 | fixed | Seed interpreter List<T>() constructor yields a nil receiver | 2026-09-13 |
| interpreter_match_on_option_of_enum_fires_no_arm_2026-08-06 | P2 | fixed | match on an Option<Enum> value directly fires no arm (silent, no error) | 2026-09-18 |
| interpreter_sffi_missing_piped_process_externs_2026-07-29 | P2 | fixed | rt_process_spawn_piped family is not registered in the interpreter extern dispatch table | 2026-09-13 |
| interp_return_in_match_expr_swallowed_2026-06-30 | P1 | fixed | return inside a match/if EXPRESSION is swallowed and becomes the expression value | 2026-09-13 |
| interp_run_cross_module_db_option_mutation_2026-06-13 | P1 | fixed | bin/simple run interpreter loses cross-module DB Option/struct returns and field mutations | 2026-08-17 |
| interp_run_enum_single_field_payload_corrupt_2026-06-15 | P1 | closed | bin/simple run silently corrupts single-field enum payload values | 2026-08-17 |
| interp_simpleos_lane_contract_crash_2026-06-13 | P1 | closed | Interpreter crashes on lane-contract field access, blocking all catalog-lane QEMU scenarios | 2026-09-13 |
| interp_state_corruption_parse_module_2026-06-12 | P2 | closed | Interpreted parse_module corrupts state around hex-literal conversion | 2026-09-13 |
| interp_static_fn_new_hijacks_named_ctor_2026-07-02 | P1 | fixed | static fn new hijacks named-argument class construction, silently building wrong-field instances | 2026-09-13 |
| interp_struct_local_copy_aliasing_2026-07-22 | P1 | closed | Interpreter struct locals alias instead of copying on assignment (silent state corruption) | 2026-08-17 |
| interp_style_block_color_shorthand_lowering_2026-07-11 | P2 | closed | HIR lowering flakes on <style>-block background/color shorthand during software paint | 2026-08-17 |
| interp_testdatabase_class_collision_kills_aggregate_test_runs_2026-07-17 | P1 | fixed | TestDatabase class-name collision in the interpreter kills every aggregate simple test run | 2026-09-13 |
| interp_text_find_byte_offset_vs_slice_char_offset_2026-06-30 | P2 | fixed | text.find returns a BYTE offset while text.slice/text.len use CHAR offsets, silently corrupting data | 2026-08-17 |
| interp_to_int_split_result_nil_coalesce_garbage_2026-07-17 | P2 | fixed | .to_int() on split-derived text and the ?? fallback both return garbage under the Rust seed interpreter | 2026-09-13 |
| interp_u64_high_bit_option_unwrap_corruption_2026-07-11 | P1 | closed | u64 struct field >= 2^63 corrupts if val Option unwrap after a JIT shared-pointer bail | 2026-08-17 |
| interp_while_body_scope_leak_2026-07-15 | P2 | fixed | Interpreter while-body locals leak into the enclosing scope (silent caller-state mutation) | 2026-08-17 |
| int_to_u8_to_char_chained_call_nested_dispatch_2026-08-07 | P2 | fixed | (i64).to_u8().to_char() chained call fails when it appears in a nested-call dispatch context | 2026-09-13 |
| iso_use_after_move_invisible_as_call_argument_2026-08-07 | P2 | fixed | iso use-after-move is invisible to the borrow checker when the second use is a call argument | 2026-09-18 |
| itf_minio_sigv4_not_runnable_interp_or_native_2026-06-16 | P2 | closed | itf minio SigV4 round-trip still not runnable: JIT bridge and module/native gaps remain after rt_http_request | 2026-09-13 |
| jit_array_oob_read_leaks_raw_rt_nil_sentinel_2026-08-07 | P1 | fixed | JIT array out-of-bounds read leaks the raw RT_NIL sentinel 3 instead of nil or a panic | 2026-08-17 |
| jit_cannot_resolve_native_socket_externs_2026-08-09 | P2 | fixed | JIT cannot resolve native_tcp_bind so every JIT-mode networking run silently falls back to the interpreter | 2026-08-17 |
| jit_cross_module_tuple_field_read_returns_nil_2026-08-01 | P1 | closed | JIT cross-module tuple .0 field read returns nil instead of the field value | 2026-08-17 |
| jit_fallback_drops_second_static_method_registration_2026-07-20 | P2 | closed | Interpreter fallback loses a struct's 2nd+ static method registration, giving unknown-static-method at runtime | 2026-08-17 |
| jit_game2d_backend_method_dispatch_sigsegv_2026-07-02 | P1 | closed | SIGSEGV calling GameBackend trait methods via LoopDriver.step under JIT | 2026-08-17 |
| jit_hex_to_u8_array_byte_corruption_2026-06-30 | P1 | closed | JIT corrupts [u8] built via ((hi<<4)|lo).to_u8() loop; interpreter is correct | 2026-08-17 |
| jit_hir_struct_field_type_infer_2026-07-18 | P3 | fixed | JIT HIR lowering cannot infer struct-typed field type, silently falls back to interpreter | 2026-09-13 |
| jit_hir_unknown_variable_valid_cross_module_import_2026-07-22 | P3 | fixed | JIT HIR lowering reports Unknown variable for validly-exported cross-module import lsu64_load | 2026-09-13 |
| jit_i64_boundary_constant_wraps_to_negative_2026-08-09 | P1 | fixed | JIT wraps large i64 boundary constants (p60/p62/i64::MAX) to negative or zero | 2026-09-13 |
| jit_if_nil_takes_true_branch_2026-08-04 | P1 | closed | JIT treats a nil if-condition as truthy; interpreter treats it as falsy | 2026-08-17 |
| jit_interp_bridge_typed_extern_returns_2026-06-12 | P3 | closed | JIT InterpCall bridge cannot represent f64 or text extern return values | 2026-08-17 |
| jit_method_dispatch_audit_2026-07-29 | P3 | fixed | Cranelift JIT builtin-method dispatch audit: enum guards only fire for statically-resolved types, Some(x)/Ok(x) are ANY | 2026-08-17 |
| jit_method_lower_not_found_on_nil_backend_autoresolve_2026-08-02 | P2 | fixed | engine2d backend auto-resolution fails with method lower not found on nil under JIT | 2026-09-13 |
| jit_module_drop_primitive_api_ty_field_2026-08-08 | P2 | closed | JIT drops primitive_api.spl module: field 'ty' accessed on struct String which has no such field | 2026-09-13 |
| jit_packed_bitfield_field_read_returns_nil_2026-08-10 | P1 | fixed | @packed bitfield field reads return nil when built via the positional raw constructor | 2026-09-13 |
| jit_run_file_pipeline_gaps_2026-07-30 | P3 | fixed | run_file_jit and the whole-program native-build pipeline diverge; shb_writer/exec_core paths differ | 2026-09-13 |
| jit_substring_chained_to_int_returns_pointer_2026-08-04 | P1 | closed | text.substring(n).to_int() chained returns the raw text pointer instead of the parsed integer | 2026-08-17 |
| jit_unresolved_static_ctor_symbol_xlenconfig_2026-07-27 | P3 | fixed | Unresolved static-ctor symbol XlenConfig_dot_rv32 demotes the whole module to the interpreter | 2026-09-13 |
| js_engine_ternary_and_statement_split_2026-07-11 | P2 | fixed | JS subset parser drops the ternary operator and never evaluates statements after a closing brace | 2026-09-13 |
| json_logic_spec_blocked_stub_modules_2026-06-26 | P2 | closed | json_logic_spec blocked by stub-only json sub-modules | 2026-09-13 |
| jupyter_labextension_missing_federated_build_packaging_2026-08-07 | P3 | fixed | JupyterLab labextension has no installable federated-extension build pipeline | 2026-08-17 |
| kernel_table_mut_writeback_lost_through_nested_free_fn_2026-08-07 | P2 | fixed | CpuKernelTable mut write-back is lost through a nested free fn / self.field in the interpreter | 2026-09-13 |
| kv260_naxriscv_bitstream_no_jtag_observability | P2 | closed | KV260 NaxRiscv bitstream exposes no JTAG/PS debug path to the softcore, blocking physical RISC-V bring-up | 2026-09-13 |
| kv260_tiny_bram_double_run_per_reset_2026-07-26 | P3 | closed | KV260 tiny-BRAM SoC firmware executes twice per hardware reset while GHDL runs once | 2026-08-17 |
| latex_range_renderer_root_cause_unfixed_2026-08-08 | P2 | fixed | LaTeX sum-range renderer upper bound patched at 2 call sites, shared root helper still wrong | 2026-08-17 |
| lean_regen_memory_capabilities_missing_conversion_theorem_2026-07-20 | P2 | fixed | regenerate_memory_capabilities emits no conversion_is_safe theorem, only reflexivity special cases | 2026-09-13 |
| length_field_access_drops_module_from_jit_2026-08-08 | P2 | fixed | Unlowered field access .length forces the whole module out of JIT (100-1000x slowdown) | 2026-09-13 |
| lib_alias_import_of_web_budget_clock_module_not_found_2026-08-08 | P2 | fixed | use lib.gc_async_mut... alias fails to resolve _web_budget_clock module var while std. alias works | 2026-09-13 |
| link_native_cc_freebsd_obj0_only_2026-07-05 | P2 | fixed | FreeBSD native link branch passes only object_files[0], dropping runtime objects | 2026-09-13 |
| lint_cli_single_file_gated_by_workspace_root_guard_2026-07-08 | P3 | fixed | Single-file simple lint exit code is overridden by workspace-root guard; unknown subcommand exits 0 | 2026-09-13 |
| lint_code_impl_indent_parse_error_2026-07-05 | P3 | fixed | Lint fix-rule module lint_code.spl fails to parse due to Indent token handling in impl blocks | 2026-09-13 |
| lint_module_graph_spec_pollution_dict_int_2026-07-31 | P2 | closed | Specs importing compiler.tools.lint.main get file-level cannot convert dict to int failure | 2026-09-13 |
| lint_profile_optional_assertion_runner_failure_2026-07-19 | P3 | closed | Lint profile optional-assertion runner fails; doc is a 571B stub with no root cause | 2026-09-13 |
| lint_reports_clean_on_module_that_fails_to_parse_2026-08-09 | P2 | fixed | bin/simple lint reports all files clean on a module that does not parse (fail-open) | 2026-09-13 |
| lint_req_comment_stmt_arena_oob_decorators_2026-08-07 | P2 | closed | bin/simple lint crashes with stmt-arena OOB on src/lib/nogc_sync_mut/spec/decorators.spl | 2026-08-17 |
| lint_stub001_false_positive_on_string_interpolation_param_2026-07-29 | P3 | fixed | lint STUB001 false-positives on a param used only inside a string interpolation | 2026-08-17 |
| live_lane_inline_text_measure_counts_utf8_bytes_2026-08-11 | P2 | fixed | Live browser lane measures inline text advance by UTF-8 bytes not codepoints (aeb -> 4 not 3) | 2026-09-13 |
| lld_defsym_symbol_argv_quoting_2026-07-12 | P3 | closed | LLD parses unquoted --defsym=spl_start=<symbol> RHS as subtraction when path contains hyphens | 2026-08-17 |
| llm_caret_messaging_composition_spec_compile_timeout_2026-08-02 | P3 | fixed | llm_caret messaging composition_spec.spl does not finish compiling within the test budget | 2026-09-13 |
| llvm_imported_array_len_index_runtime_handle_2026-07-10 | P2 | closed | Imported array .len()/index under LLVM returns a runtime handle instead of the element/length | 2026-08-17 |
| llvm_index_of_array_receiver_backend_divergence_2026-07-28 | P2 | fixed | index_of on an array receiver routes to a different runtime symbol under LLVM than under Cranelift | 2026-09-13 |
| llvm_ir_builder_emit_module_header_ignores_constructor_triple_2026-08-09 | P2 | fixed | emit_module_header() rebuilds the triple from env and ignores the LlvmTargetTriple passed to create() | 2026-09-13 |
| lsp_emitter_never_implemented_cli_query_2026-07-28 | P1 | closed | LspEmitter is imported from std.report.emitter.lsp which does not exist; query_check dies at runtime | 2026-08-17 |
| lsp_mcp_integer_position_args_corrupted_2026-06-14 | P1 | closed | Deployed native LSP MCP server corrupts integer line/character args in tools/call | 2026-09-13 |
| macos_stage4_full_cli_low_memory_runaway_2026-07-17 | P2 | closed | macOS Stage 4 full-CLI compile exceeds the bounded memory envelope | 2026-08-17 |
| macos_bootstrap_copy_mem_provider_gap_2026-07-17 | P2 | closed | macOS hosted bootstrap archive lacked the copy_mem provider | 2026-09-21 |
| macos_vulkan_host_wm_live_evidence_cpu_mirror_and_input_gap_2026-07-26 | P3 | closed | Host-WM fullscreen evidence uses a CPU presentation mirror and synthetic input, not real GPU/WM | 2026-08-17 |
| macos_vulkan_native_entry_blockers_2026-07-24 | P2 | closed | macOS Vulkan native entry blocked by active MIR lane and stage3 module collision | 2026-08-17 |
| macos_vulkan_provider_availability_live_2026-07-26 | P2 | closed | Vulkan provider probe fails because DynLib.call0 exposes only an i64 ABI | 2026-08-17 |
| match_bare_ident_const_irrefutable_2026-07-20 | P1 | closed | A match arm naming a val constant lowers as an irrefutable capture, swallowing all later arms | 2026-08-17 |
| math3d_cos_taylor_precision_2026-07-20 | P3 | closed | math3d _sin uses a 3-term Taylor series, losing precision away from zero (error ~1e-3 near pi) | 2026-08-17 |
| math_block_implicit_mul_chain_and_matmul_2026-07-20 | P2 | fixed | m{} math-DSL mis-chains implicit multiplication over 3+ groups and rejects 1D-vector matmul | 2026-09-13 |
| mcp_bootstrap_protocol_dead_main_optimized_subject_2026-07-20 | P3 | closed | bootstrap_protocol_test.spl shells out to src/app/mcp/bootstrap/main_optimized.spl which does not exist | 2026-08-17 |
| mcp_bugdb_aliased_import_function_not_found_2026-07-20 | P2 | closed | Aliased free-function import (file_exists as file_exists_backend) is unresolved at runtime | 2026-08-17 |
| mcp_debug_log_tree_stdio_no_tree_output_2026-07-20 | P2 | closed | MCP debug_log_tree returns no matching response in either JSON or LLM-text mode | 2026-08-17 |
| mcpgdb_ping_method_not_found_2026-07-20 | P3 | closed | mcpgdb MCP server returns JSON-RPC Method not found for ping | 2026-08-17 |
| mcp_redeploy_smoke_failures_2026-06-01 | P2 | closed | MCP native build generates 33 unresolved-symbol stubs and the LSP MCP build 485 | 2026-09-13 |
| mcp_smf_script_artifact_missing_rt_dir_exists_2026-07-01 | P2 | closed | SMF script artifact does not export rt_dir_exists so the MCP script-mode deploy fails to load | 2026-08-17 |
| mcp_stdio_smoke_seed_flat_registry_len_i64_2026-07-17 | P2 | closed | Seed whole-program flat registry corrupts extract_id() when main_lazy_protocol.spl joins the import closure | 2026-09-13 |
| membership_query_untagged_key_llvm_backend_2026-08-02 | P3 | fixed | Seed LLVM backend fails closed on .contains/.has/in with an untagged needle | 2026-08-17 |
| metal_gpu_only_native_readback_collapses_to_one_pixel_2026-07-17 | P2 | closed | Metal GPU-only native readback returns a single pixel instead of the full framebuffer | 2026-08-17 |
| metal_session_variant_unqualified_import_resolves_wrong_2026-07-08 | P3 | closed | Unqualified std.gpu.engine2d.metal_session import can bind the nogc_sync_mut variant instead of gc_async_mut | 2026-08-17 |
| mir_lowering_codegen_error_first_call_zero_core_dump_2026-08-06 | P1 | fixed | CompileResult.CodegenError construction calls unresolved Array.first(), lowering to call 0 and crashing every fatal MIR-lowering error path | 2026-08-17 |
| mir_lowering_missing_hirtypekind_arms_wildcard_fatal_2026-08-05 | P2 | fixed | MIR function lowering has no arm for 9 of 26 HirTypeKind variants and hits a fatal wildcard on the redeploy-gate smoke fixture | 2026-09-13 |
| mir_unresolved_method_const0_fails_open_2026-07-28 | P1 | fixed | Unresolved method call fails OPEN as emit_const(temp, Int(0)) while sibling sites fail CLOSED via rt_panic, producing a silently wrong binary | 2026-09-13 |
| mislabeled_commit_c8dbb4df4f_mass_deletion_audit_2026-07-07 | P3 | fixed | 74 of 244 files deleted by mislabeled commit c8dbb4df4f are still absent from the tree | 2026-09-13 |
| mock_specs_shadow_callrecorder_callverifier_full_reimpl_2026-08-10 | P3 | fixed | mock_spec twins define a 593-line alternate mock framework, so the real CallRecorder/CallVerifier in std/spec/mock.spl is untested | 2026-09-13 |
| module_global_write_lost_on_frame_pop_2026-07-28 | P1 | fixed | Module-level var write is silently reverted on frame pop in the interpreted lane, inverting safety flags | 2026-09-13 |
| module_import_spec_jit_iter_parse_error_2026-06-26 | P3 | closed | JIT compile of std/src/core/iter.spl fails to parse, so 2 module_import_spec examples assert wrong values | 2026-09-13 |
| move_identifier_rejected_as_expression_2026-08-15 | P2 | fixed | Parser rejects the identifier `move` in expression position: expected expression, found Plus | 2026-09-13 |
| naked_struct_pattern_vs_option_always_wildcard_2026-07-29 | P2 | fixed | case StructName(field): matched against an Option<StructName> value always falls to the wildcard arm | 2026-09-18 |
| native_aot_missing_program_body_exit3_2026-07-19 | P2 | closed | compile --native binary omits the program body and exits 3 on a NIL sentinel | 2026-08-17 |
| native_build_cache_never_written_on_timeout_2026-07-26 | P2 | fixed | native-build cache is all-or-nothing: a timeout writes no entries so every rerun is fully cold | 2026-09-13 |
| native_build_const_eval_int_letter_2026-06-28 | P3 | closed | native-build const-eval cannot fold typed and module-level constant values (hex-letter parse half is fixed) | 2026-09-13 |
| native_build_corrupted_char_len_receiver_2026-07-31 | P2 | fixed | native-build phase2 parse: .len() on identifier c receives a corrupted str rendering as U+FFFD | 2026-09-13 |
| native_build_direct_seed_jit_hang_2026-07-30 | P2 | closed | native-build against the seed hangs under JIT; SIMPLE_EXECUTION_MODE=interpret terminates | 2026-09-13 |
| native_build_entry_closure_skips_failed_modules_2026-07-13 | P2 | closed | native-build entry closure continues past modules that fail parse/semantic, emitting unresolved stubs | 2026-08-17 |
| native_build_filehandle_instance_method_unresolved_2026-08-09 | P2 | closed | MIR lowering cannot resolve FileHandle instance methods (write_all/merge) in rt_io_file_roundtrip | 2026-09-13 |
| native_build_fixed_cost_floor_hides_incrementality_2026-08-08 | P3 | fixed | native-build pays ~209s fixed cost per invocation regardless of input size and emits no reuse receipt | 2026-08-17 |
| native_build_instance_method_dispatch_unresolved_after_match_bind_2026-08-09 | P2 | fixed | MIR lowering leaves instance methods unresolved on a match-bound class local | 2026-09-13 |
| native_build_llvm_lane_4layer_stack_2026-07-26 | P2 | closed | native-build LLVM lane: layers 1 and 4 of the mapped 4-layer defect stack remain unfixed | 2026-09-13 |
| native_build_missing_output_dir_silent_fail_2026-07-23 | P3 | closed | native-build worker exits 1 with no message when the --output directory does not exist | 2026-08-17 |
| native_build_nil_receiver_crash_2026-07-25 | P2 | closed | native-build crashes at startup with field access on nil receiver (SIGILL, zero output) | 2026-09-13 |
| native_build_no_keep_going_flag_2026-08-17 | P3 | closed | native-build has no --keep-going/--error-limit flag so only the first error class is visible per pass | 2026-09-13 |
| native_build_parser_100cps_regression_2026-07-26 | P2 | fixed | native-build lane parses at ~100 chars/sec so a kernel closure cannot finish any budget | 2026-09-13 |
| native_build_removed_runtime_bundle_false_green_2026-07-24 | P2 | fixed | native-build reports success after the runtime bundle was removed (false green link) | 2026-08-17 |
| native_build_scoping_and_bootstrap_readthrough_2026-07-30 | P2 | fixed | native-build scope resolution returns empty string instead of falling through to src, silently fail-open | 2026-09-13 |
| native_build_stage4_pre_object_spin_2026-07-13 | P2 | closed | native-build Stage 4 spins before object emit; dispatch and strict-link blockers keep composition blocked | 2026-08-17 |
| native_build_unknown_option_false_green_2026-07-23 | P3 | fixed | native-build silently ignores unknown CLI options instead of erroring | 2026-08-17 |
| native_build_worker_timeout_misaccounted_2026-08-09 | P2 | fixed | native-build worker timeout fires far earlier than the configured budget, killing large-closure builds | 2026-08-17 |
| native_class_static_ctor_missing_2026-07-23 | P1 | closed | Entry-closure native lowers class static-method calls to 0 and never emits class constructors | 2026-08-17 |
| native_concurrent_backend_spawn_not_backend_aware_join_is_2026-08-04 | P1 | fixed | With a non-PureStd concurrent backend spawn skips the provider registry while join reads it, so every join returns nil | 2026-09-13 |
| native_crossmodule_arithmetic_exit_5_2026-07-23 | P2 | closed | Native cross-module arithmetic probe exits 5 instead of the expected status | 2026-08-17 |
| native_dict_get_miss_returns_zero_not_nil_2026-07-28 | P1 | fixed | Dict<K,text>.get() on a MISS returns a zero value rather than nil, silently taking the found branch | 2026-08-17 |
| native_dynload_module_var_static_init_dropped_2026-07-11 | P2 | closed | Native dynload build drops static initializers on module-level var globals, leaving them zeroed | 2026-08-17 |
| native_engine2d_readback_aggregate_abi_2026-07-26 | P3 | closed | Engine2D readback aggregate return does not follow the native aggregate ABI | 2026-08-17 |
| native_enum_runtime_type_identity_2026-07-19 | P2 | fixed | Two distinct enums with same ordinal+payload compare equal behind Any (runtime enum ID 0) | 2026-09-18 |
| native_enum_text_payload_decimalized_2026-07-12 | P2 | closed | UIEvent.Action(name) text enum payload serializes as a decimal pointer under native | 2026-08-17 |
| native_font_acceptance_pre_summary_sigill_2026-07-19 | P2 | closed | Native font acceptance run exits 132 (SIGILL) before printing its first summary line | 2026-08-17 |
| native_get_args_coalesce_empty_2026-07-23 | P1 | closed | get_args() returns [] in entry-closure native: ?? [] emits rt_is_some on a raw SplArray* | 2026-08-17 |
| native_if_print_only_arms_alloca_void_2026-07-11 | P2 | closed | Statement-form if with print-only arms emits 'alloca void', invalid IR rejected by llc | 2026-08-17 |
| native_lambda_capture_scan_excludes_interpolated_strings_2026-07-17 | P2 | fixed | Lambda capture scan skips interpolated strings so vars used only in braces are undefined | 2026-09-13 |
| native_llvm_f64_enum_payload_argpass_2026-07-19 | P2 | fixed | LLVM backend loses f64 enum payloads: construct passes xmm0, extract sitofp-coerces | 2026-09-18 |
| native_llvm_narrow_field_load_type_mismatch_2026-07-19 | P2 | closed | Narrow struct-field readback emits a mistyped load that llc rejects | 2026-08-17 |
| native_loglevel_enum_self_corruption_kernel_lane_2026-07-19 | P3 | closed | LogLevel.to_i64 sees a corrupted enum self on the -kernel boot lane only | 2026-09-13 |
| native_mixed_numeric_ordering_codegen_2026-07-16 | P2 | closed | Mixed int/float ordering comparison result depends on operand order under native codegen | 2026-08-17 |
| native_mixed_tuple_field1_statement_drop_2026-07-29 | P1 | fixed | Reading field 1 of a mixed (text,i64) tuple silently drops subsequent statements | 2026-09-13 |
| native_module_i32_derived_constant_tag_shift_2026-07-27 | P2 | closed | Module-level derived i32 constant reads tag-shifted under native codegen | 2026-08-17 |
| native_multiple_module_initializers_declaration_order_2026-07-19 | P2 | fixed | Multiple dynamic module globals lose declaration order so dependent globals fail | 2026-09-18 |
| native_nested_struct_value_copy_alias_2026-07-17 | P1 | closed | Native nested struct value copies retain aliases so writes leak into the source struct | 2026-09-13 |
| native_nil_dict_get_phantom_option_rootcause_2026-07-27 | P2 | closed | Native .get() on a nil Dict receiver returns a phantom Some and .len() returns -1 | 2026-09-13 |
| native_nil_receiver_crossmodule_method_scalar_return_2026-07-27 | P1 | closed | Cranelift AOT mis-tags a cross-module struct method's scalar return: x as i64 yields 0 | 2026-08-17 |
| native_optional_tuple_payload_extraction_broken_2026-07-29 | P1 | fixed | Optional-tuple payload extraction is wrong in every consumption form on the native lane | 2026-08-17 |
| native_option_bool_eq_against_raw_literal_2026-08-08 | P1 | fixed | Native Option<bool> compared against a raw bool literal returns the wrong answer | 2026-09-13 |
| native_pool_loop_closure_capture_fanout_2026-06-07 | P3 | fixed | Pool loop closure capture fanout count mismatches expectation in the perf lane | 2026-09-13 |
| native_provider_so_routed_to_simpleos_registry_2026-08-14 | P2 | fixed | A native provider .so is routed to the SimpleOS registry instead of the host dynlib loader | 2026-09-18 |
| native_reference_stable_place_writeback_2026-07-27 | P2 | closed | Native references lack stable-place write-back so mutations through a reference are lost | 2026-08-17 |
| native_renderdoc_inspector_else_parse_2026-07-10 | P3 | closed | RenderDoc replay inspector fails to parse an Else branch | 2026-08-17 |
| native_rt_to_string_boxed_i64_array_probe_sigsegv_2026-07-29 | P2 | fixed | rt_to_string SIGSEGVs when probing a boxed-integer array | 2026-09-13 |
| native_runtime_path_optional_lifecycle_rejected_2026-07-12 | P2 | closed | Native runtime path rejects archives that omit optional lifecycle hooks | 2026-08-17 |
| native_sspec_expect_step_stub_host_gpu_lane_2026-06-14 | P2 | closed | Native SSpec expect-step stub crashes in process SFFI on the host-GPU lane | 2026-08-17 |
| native_static_ctor_nil_symbol_crash_2026-07-14 | P2 | fixed | native-build of a struct/class with a 'static fn new()' crashes with a nil-symbol error | 2026-08-17 |
| native_string_methods_unresolved_in_mir_2026-07-17 | P2 | fixed | .parse_f64()/.to_upper() fail MIR lowering as unresolved methods on native-build | 2026-09-13 |
| native_string_relational_operators_compare_raw_handles_2026-07-17 | P2 | fixed | Native string < > <= >= compare tagged handles instead of lexicographic content | 2026-09-18 |
| native_struct_text_field_interp_misrender_2026-07-23 | P2 | closed | Struct text fields misrender inside string interpolation under native --entry-closure | 2026-08-17 |
| native_text_eq_any_untagged_smallint_deref_2026-07-23 | P2 | fixed | rt_text_eq_any derefs an untagged small int as char*, SIGSEGV at addr value<<3 | 2026-09-18 |
| native_to_i64_nil_coalesce_print_tagbox_leak_2026-07-20 | P2 | fixed | text.to_i64() ?? default prints tag-box representation instead of the i64 value | 2026-09-18 |
| native_trailing_default_param_guard_red_at_origin_tip_2026-08-15 | P2 | closed | check-native-trailing-default-param.shs exits 1 with 'native-build worker exited with co | 2026-09-13 |
| native_triple_quote_string_interpolates_unlike_oracle_2026-07-17 | P2 | fixed | Native path interpolates {..} inside triple-quoted strings; oracle treats them as raw | 2026-09-13 |
| native_unsigned_float_ordering_codegen_2026-07-16 | P2 | closed | Mixed unsigned-int/float ordering converts operands as signed, wrong for high-bit values | 2026-08-17 |
| native_untyped_array_push_and_fill_literal_2026-07-11 | P2 | closed | .push() on untyped array is fatal unresolved method and [; N] emits invalid LLVM IR | 2026-08-17 |
| nested_fn_closure_mutation_not_propagated_2026-07-20 | P2 | closed | Nested fn passed by value as callback does not propagate mutation of an outer var to cal | 2026-09-13 |
| nested_run_subprocess_empty_stdout_under_test_2026-07-20 | P2 | closed | Nested 'bin/simple run app/main.spl' subprocess returns empty stdout under bin/simple test | 2026-08-17 |
| newtype_run_path_and_enforcement_gaps_2026-06-29 | P2 | closed | newtype gives no type-safety enforcement: mix(Lba, Ppn) accepted and JIT cannot lower it | 2026-08-17 |
| noalloc_decorator_unbound_in_seed_interpreter_2026-08-08 | P2 | fixed | @noalloc is unbound in the seed interpreter: module fails to load with 'variable noalloc | 2026-08-17 |
| nogc_engine2d_backend_lane_missing_helpers_availability_2026-07-06 | P3 | closed | nogc Engine2D backend_lane lacks helpers_availability so qualcomm/intel font-offload pic | 2026-08-17 |
| office_md_block_named_field_on_unlabeled_tuple_2026-07-20 | P2 | fixed | parse_markdown_document reads .block on an unlabeled Tuple: 'undefined field block on Tu | 2026-08-17 |
| office_render_adapter_unknown_name_and_naming_drift_2026-07-20 | P3 | fixed | office_render accepts unknown adapter names silently and 'word' output says LibreOffice | 2026-08-17 |
| opencl_backend_helper_compiled_module_shadow_2026_06_04 | P2 | closed | compile_module_with_backend(opencl) to_compiled_module hits 'CompiledModule has no fie | 2026-09-13 |
| openocd_bscan_tunnel_incompatible_with_v1_bridge_2026-07-24 | P3 | closed | OpenOCD 0.12 RISC-V BSCAN tunnel framing cannot drive bscane2_tap_bridge v1 de-framer | 2026-08-17 |
| p256_fe_from_bytes_missing_ct_property_blocked_2026-07-20 | P2 | fixed | ecdh_p256.spl calls fe_from_bytes which has no P-256-field implementation | 2026-09-13 |
| p256_stack_imports_nonexistent_fe_p256_module_2026-08-04 | P1 | closed | p256.spl imports std.common.math.field.fe_p256 which does not exist; P-256 unloadable | 2026-08-17 |
| paren_less_accessor_whole_module_de_jit_2026-08-08 | P2 | fixed | Paren-less .length/.len/.size accessor drops the whole module out of JIT on compile lane | 2026-08-17 |
| parser_array_index_misread_as_generics_2026-06-14 | P2 | closed | Array indexing name[expr] is misread as a [...] generic type application in some contexts | 2026-08-17 |
| parser_bare_trailing_neg_literal_folds_prev_line_2026-07-27 | P1 | closed | A bare trailing `-1` return line folds into the previous line, silently wrong value | 2026-08-17 |
| parser_trailing_comparison_line_continuation_2026-08-04 | P2 | closed | Parser rejects line continuation after a trailing comparison operator (`if a >` nl `b:`) | 2026-09-13 |
| parser_trailing_operator_line_continuation_2026-07-13 | P2 | fixed | Trailing-operator continuation with a single-line body fails `expected expression, Dedent` | 2026-08-17 |
| paseto_v4_tampered_token_signature_accepted_2026-07-20 | P1 | fixed | PASETO v4 verification accepts a tampered token instead of rejecting the bad signature | 2026-08-17 |
| pem_encode_bytes_method_not_found_on_array_2026-07-20 | P2 | fixed | os.crypto.pem pem_encode chain calls .bytes() on an array value that has no such method | 2026-08-17 |
| poly1305_key_gen_missing_2026-07-20 | P2 | fixed | std.crypto.poly1305 does not export poly1305_key_gen (RFC 8439 2.6.2); 2 of 9 examples red | 2026-08-17 |
| pool_linked_list_push_fails_complex_indexed_field_receiver_2026-08-07 | P2 | fixed | Interpreter rejects assignment through a complex indexed-field receiver (pool[i].next = x) | 2026-09-13 |
| portable_compute_cuda_emitter_pure_simple_segfault_2026-07-17 | P1 | closed | portable_compute_emit main.spl segfaults on the release binary, emitting empty PTX source | 2026-08-17 |
| pristine_seed_cargo_build_broken_blocks_virtio_arm64_repro_2026-08-11 | P2 | fixed | Pristine seed cargo build --release fails at origin/main, blocking virtio arm64 repro | 2026-09-13 |
| private_helper_name_collision_across_modules_has_2026-08-17 | P1 | fixed | Private helper `_has` resolves to a same-named private fn in another module, wrong answers | 2026-09-18 |
| processing_ir_cuda_vulkan_fill64_parity_2026-07-26 | P2 | closed | ProcessingIR Vulkan FillU32 gives size-dependent wrong values at 64 elements, 8 passes | 2026-08-17 |
| production_gui_web_parity_refresh_hang_2026-06-27 | P3 | closed | GUI/web parity evidence refresh hangs with no stdout for >2 min on position_z_index_matrix | 2026-09-13 |
| proton_wine_fixture_api_redesign_2026-07-20 | P3 | fixed | wine_hello_fixture/proton_session specs construct an evidence API richer than the shipped | 2026-09-18 |
| pure_simple_cranelift_lexer_keyword_corruption_2026-07-24 | P1 | closed | Pure-Simple Cranelift-built CLI corrupts lexer keyword tokens, breaking self-hosted VHDL | 2026-08-17 |
| pure_simple_default_trait_is_empty_link_gap_2026-07-14 | P2 | closed | Native pipeline resolves is_empty() to Len.is_empty default without emitting the body, | 2026-08-17 |
| pure_simple_field_type_identity_keys_dispatch_2026-07-14 | P1 | closed | Field expr losing Dict<K,V> type misdispatches .keys() to Map.keys and segfaults natively | 2026-08-17 |
| pure_simple_full_cli_process_run_inherit_spipe_docgen_crash_2026-07-18 | P2 | closed | Pure-Simple full CLI crashes in rt_process_run_inherit delegating spipe-docgen | 2026-09-13 |
| pure_simple_native_build_load_sources_segfault_2026-07-13 | P2 | closed | Pure-Simple native-build stalls before native object discovery in all three bounded | 2026-08-17 |
| pure_simple_parser_missing_pipe_lambda_form_2026-08-08 | P3 | fixed | Pipe-lambda per-param types are parsed and validated then dropped: flat AST has no slot | 2026-08-17 |
| pure_simple_spipe_docgen_vector_font_spec_crash_2026-07-11 | P2 | closed | Pure-Simple binary exits with signal 11 running spipe-docgen on | 2026-09-13 |
| pure_simple_test_runner_core_c_runtime_abi_gap_2026-07-17 | P2 | closed | Stage-2-compiled src/app/test_runner_new/main.spl does not link against core-c-bootstrap | 2026-08-17 |
| pure_simple_text_extern_abi_audit_2026-07-30 | P1 | fixed | Self-hosted codegen passes `text` extern arguments divergently from the (ptr,len) | 2026-09-13 |
| pure_simple_untyped_list_element_read_unconditional_int_decode_segv_2026-08-08 | P1 | fixed | Untyped `list` element read unconditionally int-decodes, SIGSEGV on non-int content | 2026-09-18 |
| query_visibility_option_i64_match_exhausted_2026-07-20 | P1 | fixed | query_visibility and lsp_query crash: Option<i64> match exhausted on a raw i64 in symbol | 2026-09-13 |
| rain_parity_volatile_channel_recovery_dataloss_2026-07-18 | P1 | closed | Ftl.rain_recover_channel rebuilds from an in-DRAM parity table, so recovery loses data | 2026-08-17 |
| range_builtin_missing_step_argument_2026-07-20 | P2 | closed | Builtin range(start, end, step) ignores the third argument and yields every integer | 2026-08-17 |
| rawhandle_generational_id_api_drift_2026-07-20 | P3 | fixed | RawHandle/NodeId/TextureId are single-field but specs construct them as generational | 2026-09-18 |
| redeploy_gate_struct_copy_time_flip_2026-07-25 | P2 | closed | redeploy gate struct-copy-isolation prints 5 then deterministically 999 for | 2026-08-17 |
| ref_debug_profiler_handle_stops_aliasing_unless_tail_expression_2026-08-09 | P1 | closed | A capability handle stops aliasing its target unless the acquisition is the function's | 2026-08-17 |
| regeneration_spec_asserts_nonexistent_conversion_is_safe_theorem_2026-08-17 | P3 | fixed | regeneration_spec expects theorem conversion_is_safe that the memory_capabilities | 2026-09-13 |
| remote_exec_compile_remote_binary_is_a_stub_2026-08-07 | P2 | fixed | compile_remote_binary_in_dir returns fixed return-zero byte stubs instead of compiling | 2026-08-17 |
| render_session_second_render_match_arm_shadowing_bx_2026-08-02 | P2 | fixed | Second render on one SimpleWebRenderSession dies WebLayoutManager has no field bx via | 2026-08-17 |
| render_spl_specs_cannot_execute_mmio_externs_2026-08-06 | P3 | fixed | src/os/gui/render.spl cannot load in-tree: rt_mmio_read/write_u32 are baremetal externs | 2026-09-13 |
| resource_handle_anon_tuple_field_access_2026-07-20 | P2 | fixed | HandleArena spec fails on anonymous-tuple .0/.1 field access despite a complete | 2026-08-17 |
| result_unwrap_receiver_type_erasure_2026-07-13 | P2 | closed | An unannotated local from Result<T,E>.unwrap() loses T, so codegen rejects the next | 2026-08-17 |
| return_type_lint_does_not_census_lambdas_2026-08-10 | P3 | closed | RET lint rtm_fn_header never walks lambda/closure bodies so lambda return mismatches are invisible | 2026-09-13 |
| riscv32_cranelift_emission_blocker_2026-07-20 | P2 | closed | No native-build path emits a bootable rv32 baremetal ELF, so rv32 serial shell is unverifiable | 2026-08-17 |
| riscv32_hosted_linux_contract_uses_elf64_crt_2026-07-15 | P3 | fixed | riscv_linux_target_contract(Riscv32) still selects crt_dir /usr/lib/riscv64-linux-gnu (ELF64) | 2026-09-13 |
| riscv64_cranelift_smf_fs_boot_regression_2026-06-14 | P1 | closed | Rebuilt riscv64 smf_fs kernel ELF emits no markers after OpenSBI handoff; lane green only from stale artifact | 2026-08-17 |
| riscv64_kernel_codegen_blocker_2026-07-20 | P2 | closed | rv64 full-kernel entry still not proven to boot to serial shell despite six 2026-08-06 sub-fixes | 2026-08-17 |
| riscv64_native_entry_call_compare_codegen_2026-06-30 | P1 | closed | Native entry-closure rv64 drops extern call when compared to a literal: `if rt_x() == 1` folds to a constant | 2026-08-17 |
| riscv64_source_qemu_build_requires_llvm_seed_support_2026-06-06 | P3 | closed | riscv64 source-to-QEMU gate aborts with native backend 'llvm' is not available on the selected seed | 2026-08-17 |
| riscv64_ssh_kex_ed25519_signature_mismatch_2026-06-30 | P3 | closed | RV64 SSH lane proven only for a single authenticated connection; multi-connection/bad-auth hardening unproven | 2026-08-17 |
| riscv_cross_target_nil_receiver_phase3_hir_2026-07-24 | P1 | closed | riscv{32,64}-unknown-none native-build dies with field access on nil receiver in phase3 HIR lowering | 2026-08-17 |
| riscv_gen2_hwir_qualification_contract_mismatch_2026-08-14 | P3 | fixed | Gen2 HWIR qualification composer accepts only --manifest/--run-id while runner expects --emit-evidence/--compose-receipt | 2026-09-13 |
| riscv_gen2_sequential_hwir_selfhost_runtime_blocker_2026-08-14 | P2 | closed | Mixed sequential HWIR datapath spec cannot run: lane blocked on a provenance-admitted Stage-4 self-hosted CLI | 2026-08-17 |
| riscv_ghdl_validate_rv32_analyze_only_blind_to_semantics_2026-07-28 | P2 | closed | ghdl_validate_rv32 --analyze exits 0 at line 35 before elaboration, so a semantically broken CPU passes the gate | 2026-08-17 |
| riscv_hw_gates_shared_log_path_race_and_fpu_coverage_gaps_2026-07-28 | P3 | closed | check-riscv-hardware-gates writes every probe to fixed build/riscv_hw_gates/<name>.log, racing concurrent sessions | 2026-08-17 |
| riscv_jtag_stage1_idcode_check_is_self_referential_2026-07-28 | P3 | closed | tb_jtag_dtm_dmi configures the DUT with its own expected IDCODE, so a wrong IDCODE cannot fail STAGE1 | 2026-08-17 |
| riscv_priv_mmu_rv64regression_findings_2026-07-21 | P2 | closed | rv32i_rtl CoreState has no privilege fields and no Sv32 MMU translation; addresses route direct | 2026-08-17 |
| root_cli_provider_activation_requires_process_callable_loader_2026-08-14 | P2 | fixed | Root CLI never binds provider query-call/owned-session slices to an SCI command record | 2026-09-18 |
| rt_cuda_module_load_data_bytes_cstring_rejects_binary_cubin_2026-08-07 | P2 | fixed | rt_cuda_module_load_data_bytes still calls CString::new(bytes), rejecting any cubin containing a NUL | 2026-09-18 |
| rt_enum_discriminant_is_enum_id_blind_name_hash_2026-08-08 | P2 | fixed | rt_enum_discriminant returns hash_variant_discriminant(variant_name) with no enum identity, so same-named variants collide | 2026-09-18 |
| rt_file_is_char_device_dejit_and_dual_abi_2026-08-10 | P2 | fixed | rt_file_is_char_device has two incompatible ABIs and de-JITs the whole process to the interpreter | 2026-09-13 |
| rt_file_truncate_4mib_cap_2026-07-06 | P3 | closed | rt_file_truncate extend appears capped at 4 MiB via the self-hosted binary despite no clamp in source | 2026-08-17 |
| rt_host_gpu_queue_duplicate_symbols_freebsd_fatal_2026-08-05 | P2 | fixed | rt_host_gpu_queue_* defined in both C and Rust, fatal duplicate symbols under FreeBSD lld | 2026-08-17 |
| rt_io_file_family_undefined_stubbed_silent_data_loss_2026-08-05 | P1 | closed | File.write returns Ok and writes nothing: rt_io_file_* externs get fabricated zero stubs under native/JIT | 2026-08-17 |
| rt_process_run_with_limits_argcount_and_missing_ptrlen_2026-07-31 | P2 | fixed | rt_process_run_with_limits RuntimeFuncSpec declares 5 I64 while the Rust fn takes 8 params | 2026-09-13 |
| rt_string_concat_quadratic_2026-06-12 | P3 | closed | MCP json.spl builders never adopted rt_string_builder, so the O(n) runtime primitive is unused there | 2026-09-13 |
| rt_time_now_micros_delta_prints_tagbox_blocks_in_language_benchmarking_2026-08-02 | P2 | closed | rt_time_now_micros() deltas interpolate as tagbox garbage, making in-language microbenchmarking unusable | 2026-09-13 |
| rt_typed_words_u32_is_not_a_packed_pixel_basis_2026-08-06 | P3 | closed | rt_typed_words_u32_* is an 8-byte-stride accessor, not the 4-byte packed pixel basis packed_span.spl claims | 2026-09-13 |
| rt_vulkan_only_executes_under_classic_interpret_2026-06-17 | P1 | closed | rt_vulkan_* silently report zero devices outside the classic interpreter; native stub returns 0 with no error | 2026-08-17 |
| runtime_compiler_temp_namespace_hardening_2026-07-17 | P3 | closed | Runtime C object temp paths simple_rt_<pid>_<raw-target>_<stem> collide across concurrent in-process links | 2026-08-17 |
| runtime_error_stack_absent_on_live_interpreter_2026-08-17 | P2 | fixed | Runtime errors print no Call stack: section naming frames on the live interpreter | 2026-09-18 |
| run_vs_test_harness_divergence_2026-07-28 | P3 | closed | bin/simple run and bin/simple test diverge on method dispatch; the 173ad044494 fixes landed unverified | 2026-08-17 |
| rust_recovery_runner_hangs_after_passing_examples_2026-07-19 | P2 | closed | SIMPLE_TEST_RUNNER_RUST=1 run prints '3 examples, 0 failures' then never exits | 2026-08-17 |
| rust_seed_accepts_reserved_on_identifier_2026-07-11 | P3 | closed | Rust seed accepts 'val on = ...' while the stage3 parser rejects reserved 'on' | 2026-08-17 |
| rust_seed_javanew_heuristic_blocks_identifier_named_new_2026-08-10 | P2 | fixed | Seed parser JavaNew heuristic rejects valid source using an identifier named 'new' | 2026-09-18 |
| rust_seed_native_bool_arg_inlined_call_wrong_value_2026-07-17 | P1 | fixed | Seed cranelift codegen returns the wrong value from a bool-arg call after inlining | 2026-09-13 |
| rv64_core_no_c_extension_opensbi_stall_2026-07-22 | P2 | closed | rv64gc RTL core has no RV64C compressed decode; real OpenSBI desyncs at insn ~5 | 2026-08-17 |
| rv64_dtb_overlay_not_materialized_in_soc_address_map_2026-07-27 | P2 | fixed | rv64 DTB overlay at 0x8800_0000 reads 0xD0 instead of DTB magic in addr4g_probe | 2026-09-18 |
| rv64_host_gpu_mmio_test_closure_2026-07-12 | P3 | closed | os.kernel.boot.mmio drags allocating test-region classes into the baremetal RV64 probe clo | 2026-08-17 |
| rv64_host_gpu_real_runtime_exit_facade_2026-07-12 | P3 | closed | x86_64 and ARM64 probe leaves still call runtime exits instead of an arch-owned exit facad | 2026-08-17 |
| rv64_opensbi_fw_platform_init_throughput_frontier_2026-07-22 | P3 | closed | OpenSBI banner unreachable on soc_top_64: ~60s watchdog plus interpreted lsu64_load fallba | 2026-09-13 |
| rv64_opensbi_wfi_park_before_banner_2026-07-23 | P2 | closed | OpenSBI hangs in fw_platform_init libfdt /cpus walk on soc_top_64 before the banner | 2026-08-17 |
| rv64_ssh_aes_gcm_post_newkeys_stall_2026-06-14 | P1 | fixed | RV64 sshd stalls inside AES-GCM encrypt for the first post-NEWKEYS packet (SSH_MSG_EXT_INF | 2026-09-13 |
| S61_interpreter_stack_overflow_app_io_mod_2026-07-17 | P2 | closed | 'use app.io.mod' stack-overflows both interpreters: loader has no is_currently_loading tra | 2026-08-17 |
| salsa20_xsalsa20_keystream_kat_mismatch_2026-07-20 | P1 | fixed | Salsa20/XSalsa20 keystream does not match the DJB/NaCl/libsodium published KAT vectors | 2026-08-17 |
| sci_provider_query_abi_digest_width_mismatch_2026-08-16 | P2 | fixed | SCI abi_digest is 64-hex SHA-256 text but SimpleProviderQueryResultV1.abi_digest is a u64 | 2026-09-13 |
| sdn_cross_module_variant_dispatch_2026-06-26 | P2 | closed | Any method on an SdnValue from std.sdn.parser.parse() fails 'unknown variant or method' | 2026-08-17 |
| sdoctest_coverage_loader_never_implemented_2026-07-28 | P2 | closed | load_sdoctest_blocks and compute_sdoctest_coverage are imported and exported but defined n | 2026-08-17 |
| sdoctest_mode_unknown_extern_rt_string_ends_with_2026-08-07 | P2 | closed | 'simple test --sdoctest <file>.md' fails on all input: unknown extern function rt_string_e | 2026-08-17 |
| security_event_enum_variant_construct_unresolved_under_test_2026-07-20 | P2 | closed | EnumName.Variant(named_args) is unresolved under 'simple test' via a transitively-called f | 2026-08-17 |
| seed_binary_detection_gaps_2026-07-25 | P3 | closed | is_rust_seed_simple() classifies by path substring, so a copied seed passes evidence gates | 2026-08-17 |
| seed_crossmodule_struct_field_option_poison_2026-06-14 | P2 | closed | Seed interpreter poisons cross-module struct field access to Option under a broad import c | 2026-08-17 |
| seed_gc_js_engine_typeof_undefined_and_for_desugar_regression_2026-08-15 | P1 | fixed | Seed breaks the in-process JS engine: 'for is not defined', '__simple_i is not defined', t | 2026-08-17 |
| seed_interp_defer_lazy_imports_module_globals_2026-07-24 | P1 | closed | Seed native-build --backend llvm dies parsing file 1: 'array index out of bounds: index 3, | 2026-08-17 |
| seed_interp_flat_nullable_unwrap_wrong_value_2026-07-16 | P1 | closed | Bare .unwrap() on flat-nullable T? routes to rt_enum_payload and returns wrong value | 2026-08-17 |
| seed_interp_float_print_1e18_non_roundtrip_2026-07-16 | P2 | closed | Seed run prints 1e-18 as 0.00000000000000000 which parses back as 0.0 (non-round-trip) | 2026-08-17 |
| seed_interp_option_match_falls_through_at_scale_2026-07-18 | P1 | fixed | if opt.? re-decides presence from payload truthiness so Some(0)/Ok(0) takes the wrong | 2026-09-13 |
| seed_interpreter_parse_probe_memory_accumulation_2026-07-03 | P2 | closed | Seed interpreter retains ~30MB per parse_module call; 118-file sweep crosses a 4GB cap | 2026-08-17 |
| seed_interpreter_to_int_wrong_dispatch_2026-07-03 | P1 | closed | .to_int() on a split()-produced string returns pointer-like garbage instead of the parsed | 2026-08-17 |
| seed_jit_boxed_int_61bit_drops_high_bits_2026-07-22 | P1 | closed | JIT boxes i64 as (v<<3)|TAG giving a 61-bit channel; 0x8010000000000000 loses bit 63 | 2026-08-17 |
| seed_jit_me_method_array_of_struct_writeback_nil_receiver_2026-07-23 | P1 | closed | me-method write-back into a self array-of-structs field aborts with field access on nil | 2026-08-17 |
| seed_jit_miscompiles_soc_top_64_masked_by_fallback_2026-07-22 | P1 | closed | With lowering fallbacks removed the seed JIT miscompiles soc_top_64: 57 probe failures vs | 2026-08-17 |
| seed_jit_spl_f64_to_bits_miscompile_2026-07-23 | P1 | closed | Seed JIT returns spl_f64_to_bits result float-tagged: array readback differs and i64 == | 2026-08-17 |
| seed_jit_string_to_i64_float_tagged_silent_wrong_2026-07-28 | P1 | closed | text.to_i64()/.to_int() return a FLOAT-tagged value under seed JIT so 42.to_i64() == 42 | 2026-08-17 |
| seed_jit_u32_cross_module_const_import_zero_2026-07-23 | P2 | closed | Seed JIT evaluates a top-level u32 val initialized from a cross-module const or an `as | 2026-08-17 |
| seed_jit_unresolved_symbol_segfault_and_silent_pass_2026-08-10 | P1 | closed | Seed JIT SIGSEGVs on `[i64]()` and silently passes a bare undefined-variable read the | 2026-08-17 |
| seed_jit_wide_i64_literal_miscompile_2026-07-27 | P1 | fixed | Seed JIT materializes 0x7FFFFFFFFFFFFFFF as -1 and 0x8000000000000000 as 0; interpreter | 2026-09-13 |
| seed_lexer_literal_soft_keyword_shadows_identifier_2026-07-30 | P2 | fixed | Seed lexer maps the bare word `literal` to TokenKind::Literal so reassigning a var named | 2026-09-13 |
| seed_nested_tuple_index_float_munch_2026-08-06 | P2 | fixed | Seed lexer munches r.0.1 as Float(0.1) so nested tuple indexing fails to parse | 2026-08-17 |
| seed_parser_no_return_expression_kills_jit_2026-07-26 | P2 | fixed | Seed parser has no `return` in expression position; `x ?? return e` hard-fails and drops | 2026-09-13 |
| seed_parser_rejects_multiline_if_expression_chain_2026-07-27 | P2 | closed | Seed parser rejects a multi-line if-expression chain in value position with expected | 2026-08-17 |
| seed_run_trim_recursion_overflow_browser_engine_2026-07-19 | P2 | closed | Seed interpreter overflows at recursion depth 1000 in 'trim' while loading the | 2026-08-17 |
| seed_text_char_code_at_custom_method_precedence_2026-07-19 | P3 | closed | Seed lowers the char_code_at builtin before custom dispatch so an `impl text` override is | 2026-08-17 |
| selfhost_bootstrap_unresolved_symbols_2026-06-24 | P1 | closed | Stage3 self-host stub forces stage4 onto the seed, producing 548 stub functions for | 2026-08-17 |
| selfhost_cross_module_result_ok_err_unresolved_2026-07-27 | P2 | closed | Qualified Result.Ok(x)/Result.Err(e) in an imported method body fails with variable | 2026-08-17 |
| self_hosted_fat32_lfn_interpreter_segv_2026-07-14 | P2 | closed | Self-hosted `simple test --mode=interpreter` on the FAT32 LFN spec exits 139 with no | 2026-09-13 |
| selfhosted_native_local_fn_body_dropped_2026-06-15 | P2 | closed | Native rv64 --entry-closure drops a file-local fn body, leaving the mangled name | 2026-08-17 |
| self_hosted_parser_block_lambda_call_arg_2026-07-11 | P2 | closed | Self-hosted parser rejects a block lambda as call argument with a dedented closing paren | 2026-08-17 |
| selfhost_native_build_const_eval_mapnew_body_on_string_2026-07-17 | P1 | closed | Frontend Map.new()/Dict.new() const-eval makes the seed report unknown property or | 2026-08-17 |
| selfhost_two_hop_field_method_mutation_lost_2026-07-27 | P1 | fixed | A mutating method call two struct-field hops from self (self.world.output_bufs.insert) | 2026-09-13 |
| serial_mcp_detect_tool_name_red_2026-08-09 | P2 | fixed | detect_tool_name returns the wrong value for a well-formed tools/call body so MCP | 2026-08-17 |
| serial_usb_sigsegv_cascade_2026-05-30 | P1 | closed | serial_open SIGSEGVs at address 0x8 on USB disconnect; forked children cascade and tear | 2026-09-13 |
| shared_font_pure_simple_shaping_gap_2026-07-11 | P2 | closed | Pure-Simple shaper omits advances/offsets/direction/script; GSUB is identity so it cann... | 2026-08-17 |
| shared_font_req015_deployed_selfhost_segv_2026-07-14 | P2 | closed | Deployed self-host CLI exits 139 on font_render_config_spec and on check of font_types.spl | 2026-09-13 |
| shared_wm_qemu_direct_mmio_backend_perf_2026-07-06 | P3 | closed | SimpleOS WM renders to a temp pixels buffer then copies every pixel to BGA MMIO each frame | 2026-08-17 |
| short_grammar_placeholder_outermost_scope_hoist_2026-06-26 | P2 | closed | _N placeholder binds the lambda to the outermost expression, swallowing the inner call | 2026-08-17 |
| showcase_lanes_regressions_2026-07-18 | P2 | closed | Showcase lanes: remaining compiled-lane resolution/completion gaps after five in-sweep... | 2026-08-17 |
| signal_handlers_global_cleanup_fnptr_data_export_2026-07-17 | P2 | closed | Cross-module fn-pointer var _global_cleanup_handler resolves as a DATA export and misfires | 2026-08-17 |
| simd_f32x4_vec_field_boxed_float32_not_unwrapped_2026-07-20 | P2 | fixed | rt_simd_mul_f32x4 receives a boxed Float32 in Vec4f.x instead of a raw f32 and aborts | 2026-08-17 |
| simple_check_parse_only_false_green_2026-07-19 | P1 | closed | simple check exits 0 with All checks passed on `val x: i64 = text` (HM never fatal) | 2026-08-17 |
| simple_core_archive_runtime_symbol_resolution_2026-07-23 | P2 | fixed | Generated NotEq calls shared rt_native_neq and panics missing runtime fn despite a loca... | 2026-09-13 |
| simple_core_pure_simple_archive_builder | P2 | fixed | check-simple-core-runtime-smoke still materializes libsimple_runtime.a from C, not pure... | 2026-09-13 |
| simple_db_perf_native_server_blockers_2026-06-21 | P3 | closed | DB compare wrapper reports server mode unavailable; embedded driver is timing-only | 2026-08-17 |
| simple_driver_cargo_test_lld_bus_error_2026-06-27 | P3 | closed | Filtered cargo test -p simple-driver links unrelated test bins and dies in rust-lld sig... | 2026-08-17 |
| simple_fix_spipe_missing_docstrings_corrupts_describe_string_literal_2026-08-07 | P2 | fixed | simple fix injects the generated docstring inside the describe ... literal, breaking... | 2026-08-17 |
| simple_lint_unknown_option_false_accept_2026-07-23 | P2 | closed | simple lint continues normally on --bogus and bare --profile instead of usage-erroring | 2026-08-17 |
| simpleos_backend_render_receipt_producer_parser_missing_2026-07-27 | P2 | fixed | No SimpleOS guest entry emits ordered backend render receipt records, so QMP pixels are... | 2026-08-17 |
| simpleos_clang_fs_pure_compiler_native_build_2026-07-11 | P2 | closed | Guest Clang links but the live in-guest compile/link/execute proof never completes | 2026-08-17 |
| simpleos_filesystem_trait_dispatch_sentinel_2026-07-20 | P2 | closed | FileSystem-layer trait calls lower to slot 4294967295 DUCK_DISPATCH_UNSUPPORTED_SLOT (4... | 2026-08-17 |
| simpleos_focused_compiler_entry_closure_2026-07-11 | P2 | closed | Focused SimpleOS compiler link fails with 397 missing externals; Cranelift emits one .t... | 2026-08-17 |
| simpleos_focused_emit_object_stage4_mir_error_2026-07-11 | P2 | closed | MirLowering.new created errors/loop_stack as Dicts so array len misread capacity 8 as a... | 2026-08-17 |
| simpleos_freestanding_text_split_abi_parse_html_2026-07-12 | P2 | closed | Split-ABI fixed but a deeper freestanding cranelift fault (cr2=0xNN00000000) still blocks | 2026-09-13 |
| simpleos_libc_float_port_blocked_f64_2026-06-28 | P2 | closed | strtod/math/printf_float cannot be ported to pure Simple because f64 is unreliable across | 2026-08-17 |
| simpleos_optimizer_loses_alias_key_array_2026-07-13 | P1 | closed | Optimizer passes tagged nil as local_ids so local_count_index faults loading array length | 2026-08-17 |
| simpleos_riscv64_defsym_unknown_symbol_aliasing_2026-07-28 | P1 | closed | link_simpleos_riscv64 aliases 13 lost-call-target unknown_N symbols onto 5 real kernel | 2026-08-17 |
| simpleos_riscv64_inguest_simple_payload_corec_gap_2026-07-25 | P2 | fixed | riscv64 in-guest simple payload fails ld.lld link on 6 rt_* symbols absent from the | 2026-09-13 |
| simpleos_rv64_wm_live_framebuffer_gate_2026-06-30 | P2 | closed | RV64 WM live status is missing because font/input transport and pmemsave evidence cannot | 2026-08-17 |
| simpleos_ssh_qemu_gate_uses_probe_service_not_sshd_2026-06-06 | P2 | fixed | Live SSH gate emits a corrupt server KEXINIT (payload starts 0x54 not 0x14) so OpenSSH | 2026-09-18 |
| simpleos_static_axes_fonts_rejected_by_selected_asset_validation_2026-08-09 | P2 | fixed | Bungee and UnifrakturCook are rejected by selected-asset validation because default_axes | 2026-08-17 |
| simpleos_wm_cell7_gate_blocked_mtools_missing_2026-08-01 | P3 | fixed | Showcase cell 7 gate fails closed at browser-demo-real-elf-not-staged because mcopy | 2026-09-13 |
| simpleos_wm_content_provenance_material_fallback_none_2026-07-25 | P2 | closed | WM frame rejected with material_fallback_kind=none because the guest HTML parse | 2026-09-13 |
| simpleos_wm_host_qmp_mouse_input_no_framebuffer_delta_2026-06-11 | P2 | fixed | Host-injected QMP/HMP mouse events move nothing: the framebuffer is byte-identical after | 2026-09-13 |
| simpleos_wm_pointer_release_font_metrics_hang_2026-07-26 | P2 | closed | Pointer-release render hangs forever in taskbar-tray text measurement at begin=76 | 2026-08-17 |
| simple_portal_dbfs_mount_write_not_visible_to_load_2026-07-20 | P2 | fixed | File written through _write_mount_file is not visible to portal_content_db_load_from_mount | 2026-08-17 |
| simple_portal_playground_status_code_200_vs_202_2026-07-20 | P3 | fixed | Authorized POST /api/playground/run returns 200 OK where the spec requires 202 Accepted | 2026-09-13 |
| simple_runaway_oom_host_crash_2026-06-14 | P2 | closed | A single simple process reaches ~117 GB anon-rss and triggers global OOM kills that take | 2026-08-17 |
| simple_runner_native_perf_hash_gap_2026-06-01 | P1 | closed | LLVM native-build of simple_runner emits fill hash 2575739855 instead of C reference | 2026-08-17 |
| simple_shared_parameter_llvm_global_load_2026-07-17 | P1 | closed | A parameter named `shared` lowers to an undeclared LLVM global `Shared`, failing Stage 2 | 2026-08-17 |
| simple_test_runner_memory_leak_2026-06-14 | P1 | closed | The long-lived parent `bin/simple test` process grows to 45-118 GB RSS and is OOM-killed | 2026-08-17 |
| simple_web_gradient_dither_residual_2026-06-26 | P3 | closed | Small no-repeat linear-gradient tiles still mismatch Chromium quantization on | 2026-08-17 |
| simple_web_readiness_marker_aspirational_diskless_2026-07-20 | P2 | closed | gui_entry_desktop prints simple_web=content-frame as a hardcoded literal while zero web | 2026-08-17 |
| simple_web_widget_css_divergence_vs_chromium_2026-07-03 | P2 | closed | Simple web engine matches Chromium only 50.31% on widget CSS while Chrome and Electron | 2026-08-17 |
| single_example_hardware_gated_spec_reports_zero_examples_fail_2026-08-11 | P2 | closed | A spec whose only example is skip_if-skipped reports reason=zero-examples FAIL instead of | 2026-09-13 |
| skia_bitmap_zeros_plus_u8_param_breaks_u8_resolution_2026-07-20 | P2 | closed | A Bitmap.zeros call plus a u8-typed param in one file yields `semantic: variable u8 not | 2026-08-17 |
| skia_matrix3x3_missing_is_identity_2026-07-20 | P2 | fixed | Matrix3x3 has no is_identity() method so 5 of 18 matrix_spec examples fail | 2026-08-17 |
| skia_path_op_boolean_algorithm_2026-07-20 | P2 | fixed | path_op boolean polygon ops fail 2 of 6 point-membership/bbox examples | 2026-08-17 |
| skip_reserved_token_blocks_struct_field_2026-06-15 | P3 | closed | A struct field named `skip` fails to parse: expected identifier, found Skip | 2026-08-17 |
| smf_elf_text_selection_diverges_on_truncated_and_function_sections_objects_2026-08-08 | P2 | closed | extract_code_from_object and extract_elf_relocations disagree on truncated .text sections | 2026-09-13 |
| smf_header_source_hash_offset_mismatch_2026-06-13 | P2 | closed | SMF header writes source_hash at offset 68 but cache_validator reads it at header_start+84 | 2026-08-17 |
| smf_reader_bridge_silent_nil | P1 | fixed | rt_smf_reader_open has no implementation so SmfReaderFfi.open returns Ok for any path | 2026-08-17 |
| smux_legacy_specs_zero_examples_red_2026-08-16 | P2 | fixed | smux_spec.spl is main()/print-based so the runner reports executed=0 reason=zero-examples | 2026-08-17 |
| spawn_call_expr_silently_becomes_nillit_2026-07-29 | P1 | fixed | spawn(...) call expressions lower to HirExprKind.NilLit, discarding callee and args with | 2026-08-17 |
| spec_harness_module_global_mutation_via_function_invisible_2026-08-07 | P1 | closed | Under bin/simple test a module var mutated inside a called fn reads back unchanged; run | 2026-09-13 |
| spec_it_block_reads_stale_module_var_2026-08-04 | P1 | fixed | An it body reads a module var at its registration-time value even after a helper writes it | 2026-09-13 |
| spec_matcher_nested_call_dispatch_2026-07-27 | P2 | closed | to_equal is unresolvable when chained onto a user-defined method call result in nested | 2026-08-17 |
| spec_runner_child_summary_scraper_returns_zero_2026-08-08 | P2 | closed | parse_child_example_summary returns has_summary=0 on every run, a silently dead scraper | 2026-09-13 |
| spec_runner_drops_sibling_top_level_describe_2026-06-28 | P1 | closed | Only the LAST sibling top-level describe runs; earlier groups are dropped and still | 2026-08-17 |
| spec_value_type_helper_mutates_copy_family_2026-08-10 | P2 | fixed | Spec helpers taking a struct by value mutate a copy, so absence assertions test nothing | 2026-09-13 |
| spipe_before_all_after_all_not_found_t32_hw_2026-07-20 | P2 | closed | before_all/after_all are unresolved when imported via std.spipe, so t32_hw specs run zero | 2026-08-17 |
| spipe_docgen_silent_no_output_wm_glass_2026-07-19 | P2 | closed | spipe-docgen exits 0 without creating the mirrored manual, so verification mistakes it | 2026-08-17 |
| spipe_docgen_stale_syntax_detection_2026-07-19 | P2 | closed | validate_spec counts scenarios only via legacy `it ` so modern it(...) specs render as | 2026-08-17 |
| spipe_to_be_true_matcher_errors_in_interpreter_itblock_2026-06-04 | P2 | closed | expect(x).to_be_true() fails inside an interpreter it block even when x is genuinely true | 2026-08-17 |
| spipe_wrapped_entry_bare_expect_matcher_to_int_2026-07-20 | P2 | closed | Bare expect X matcher(Y) inside fn main(): wrapper emits 'cannot convert matcher to int' | 2026-08-17 |
| src_os_dangling_imports_never_implemented_2026-07-28 | P2 | closed | src/os imports ~14 symbols (FeP256 md5 display_protocol current_architecture | 2026-08-17 |
| ssh_kex_rsa_contract_no_examples_executed_2026-07-20 | P2 | closed | ssh_kex_rsa_contract_spec compiles after import fix but runs 0 examples in ~64s | 2026-08-17 |
| sspec_expect_eq_to_equal_false_silently_wrong_2026-07-17 | P1 | closed | expect(a == b).to_equal(false) is rewritten to expect(a).to_equal(b) asserting the | 2026-08-17 |
| sspec_extern_array_arg_marshaling_empty_result_2026-07-20 | P2 | closed | extern fns taking [u8] array args return empty results under bin/simple test but are | 2026-08-17 |
| sspec_long_command_tail_assertions_2026-06-28 | P2 | closed | Assertions placed after a very long command-construction step are silently skipped by the | 2026-08-17 |
| sspec_matcher_to_equal_zero_falsy_2026-06-29 | P2 | closed | expect(0).to_equal(0) fails with 'expected call result to be truthy, got 0' | 2026-08-17 |
| sspec_module_docstring_plus_subprocess_it_false_green_2026-08-08 | P1 | fixed | Large module docstring plus subprocess-heavy it blocks makes later false assertions | 2026-09-20 |
| sspec_runner_10s_example_timeout_heavy_subprocess_2026-06-29 | P2 | closed | Runner kills a subprocess example at a fixed 10s cap yet still tallies the file as Failed | 2026-08-17 |
| sspec_runner_process_exit_and_elif_2026-06-29 | P1 | closed | process_run exit code returns 0 for a failing child under test and 3-way if/elif/else | 2026-08-17 |
| sspec_runner_suppresses_child_failure_diagnostic_2026-07-26 | P2 | closed | Runner reports '0 passed 1 failed' without forwarding the child assertion/import/runtime | 2026-08-17 |
| sspec_simple_check_superlinear_two_impls_2026-06-29 | P2 | closed | bin/simple check hangs or crashes non-deterministically on structs with >=3 array fields | 2026-08-17 |
| sspec_test_path_value_semantics_divergence_2026-07-20 | P1 | closed | The .? operator and class-in-array aliasing give wrong values under simple test but | 2026-08-17 |
| stage2_native_build_link_undefined_method_symbols_2026-08-09 | P1 | fixed | Stage-2 native-build link fails with 9 undefined unmangled Simple method symbols (rfind | 2026-09-13 |
| stage2_native_sspec_process_run_sigsegv_2026-07-29 | P2 | fixed | Native-built SSpec binary SIGSEGVs in memcpy inside rt_process_run before printing a | 2026-09-13 |
| stage2_seed_incremental_silent_spin_2026-08-08 | P2 | closed | Stage-2 seed incremental bootstrap burns a core for 5m32s writing zero log bytes and no | 2026-09-13 |
| stage3_freestanding_struct_by_value_corrupts_pmm_2026-07-11 | P1 | closed | Stage3 freestanding passes a 4-field u64 struct by value corrupted so _bitmap_clear | 2026-08-17 |
| stage3_host_entry_closure_retains_unresolved_modules_2026-07-11 | P2 | closed | Stage3 --entry-closure host WM build emits 23 unresolved-symbol stubs and the evidence | 2026-08-17 |
| stage3_native_build_sigsegv_call_to_zero_root_cause_2026-08-11 | P1 | fixed | Self-hosted stage2/stage3 native-build SIGSEGVs on a call 0x0 baked in by an unpatched | 2026-09-13 |
| stage3_selfhost_entry_module_zero_functions_2026-08-11 | P1 | fixed | Stage 3 loads 573 HIR modules but the entry module has an empty function list so it | 2026-09-13 |
| stage3_selfhost_parser_case_multielem_pattern_2026-07-17 | P1 | closed | Stage3 self-hosted parser rejects multi-element case pattern CallIndirect(_,ptr,args,_) | 2026-08-17 |
| stage3_selfhost_reaches_mir_entry_module_not_captured_2026-08-10 | P1 | fixed | bootstrap flat HIR entry module app.cli.bootstrap_main not captured in flat accumulator | 2026-09-13 |
| stage3_whole_tree_parse_state_vhdl_helpers_2026-07-30 | P2 | closed | Whole-tree stage3 build mis-parses vhdl_codegen_helpers.spl via parser state, flaky 45 | 2026-09-13 |
| stage4_aot_native_build_struct_field_access_sigill_2026-07-24 | P1 | closed | Self-hosted native-build SIGILLs field access on nil receiver for any struct field read | 2026-08-17 |
| stage4_codegen_compact_form_hazards_2026-07-02 | P2 | closed | Seed cranelift codegen mis-executes compact .spl forms it accepts (bool cond, pattern | 2026-08-17 |
| stage4_cranelift_direct_enum_text_cross_function_2026-07-24 | P1 | closed | Enum text payload matched in a different function than constructed prints a raw heap | 2026-08-17 |
| stage4_cranelift_direct_origin_regression_2026-07-23 | P1 | closed | cranelift-direct stage4 SEGVs while compiling simple fn probes (probe_rich, pm5, pm6) | 2026-08-17 |
| stage4_db_atomic_hir_names_2026-08-02 | P3 | fixed | db_atomic async mirror still matches Ok(_) which Stage4 treated as an unresolved | 2026-09-13 |
| stage4_delayed_explicit_import_facade_origin_2026-08-03 | P2 | fixed | Delayed explicit-import chain reports ambiguous facade export for app.io.mod | 2026-09-13 |
| stage4_deploy_no_seed_test_runner_blocked_2026-06-11 | P2 | fixed | bin/simple test still needs SIMPLE_BOOTSTRAP_DRIVER seed delegation instead of a | 2026-09-13 |
| stage4_entry_closure_duplicate_parse_2026-07-17 | P2 | closed | Stage4 full-CLI entry closure completed only 202 of 2095 parses in 750s, exceeding the | 2026-08-17 |
| stage4_err_propagation_characterization_2026-07-04 | P1 | closed | ? operator does not short-circuit on Err in compiled binaries; v gets garbage and | 2026-08-17 |
| stage4_focused_subbuild_star_import_unresolved_2026-07-27 | P1 | closed | Stage4 focused sub-builds still fail star-import resolution; 2224 unresolved names remain | 2026-08-17 |
| stage4_full_cli_closure_spin_2026-07-18 | P2 | closed | Stage4 full-CLI compile recompiles 662-1278+ files with no progress output, reads as an | 2026-08-17 |
| stage4_full_cli_source_check_blank_exit8_2026-07-23 | P1 | fixed | Stage4 candidate exits 8 with empty stdout/stderr on check src/app/cli/bootstrap_main.spl | 2026-09-13 |
| stage4_hazard_sweep_int_and_bare_patterns_2026-07-03 | P2 | closed | int(text) returns the first char code instead of parsing decimal at 40+ compiler call | 2026-08-17 |
| stage4_phase3_flat_ast_arena_desync_2026-08-01 | P1 | fixed | Stage4 dies in phase 3 on a flat-AST statement-arena desync masking unresolved-type errors | 2026-09-13 |
| stage4_process_provider_owner_gap_2026-07-18 | P2 | closed | Stage4 owner table omits the process-timeout provider so spl_* process slice is unowned | 2026-08-17 |
| stage4_pure_simple_driver_no_thread_fanout_2026-07-18 | P2 | closed | Stage4 --threads is discarded by two layers; aot_native_project_with_backend_fixed never fans out | 2026-08-17 |
| stage4_raw_compiler_backfill_admission_2026-07-17 | P2 | closed | Stage4 admits no compiler-backfill capsule so raw compiler symbols stay unowned | 2026-08-17 |
| stage4_runtime_core_owner_gap_2026-07-18 | P2 | closed | Stage4 omits core C runtime owners leaving unresolved runtime symbols and ctor sections | 2026-08-17 |
| stage4_runtime_legacy_compat_owner_gap_2026-07-18 | P3 | closed | Stage4 runtime-native legacy compat owner gap: source-fixed but never executed | 2026-08-17 |
| stage4_seed_interpreter_statement_dispatch_regression_2026-08-16 | P1 | fixed | Rust seed interpreter mis-dispatches statement/assignment nodes breaking stage4 interpretation | 2026-08-17 |
| stage4_seed_llvmlib_method_arity_2026-07-06 | P2 | closed | Seed llvm-lib backend miscomputes method-call arity and extern signatures blocking stage4 redeploy | 2026-08-17 |
| stage4_selfhost_log_modes_lexer_state_corruption_2026-07-24 | P2 | closed | Stage4 self-host corrupts lexer state while compiling log_modes.spl | 2026-08-17 |
| stage4_selfhost_sha3_hir_infer_and_stubs_2026-06-28 | P1 | closed | Stage4 emits 574 unresolved-symbol stubs and fails HIR inference on sha3.spl | 2026-08-17 |
| stage4_test_runner_bounded_capture_empty_2026-07-23 | P2 | closed | Stage4 test runner returns empty bounded child output and loses exit status | 2026-08-17 |
| stage4_test_runner_main_hir_names_2026-08-02 | P2 | fixed | test_runner_main leaves time_now_unix_micros duration_ms to_int dir_create_all unresolved via std.io facade | 2026-09-13 |
| stage4_test_runner_pipe_capture_truncation_rt_fork_2026-07-20 | P1 | fixed | rt_fork_parent_wait_bounded exits its read loop early truncating captured test output | 2026-08-17 |
| stage4_tip_link_bare_extern_symbols_2026-07-26 | P2 | fixed | Stage4 one-binary build emits cross-module calls as bare extern symbols failing the link | 2026-09-13 |
| stage4_unstub_multifn_silent_noop_2026-07-03 | P2 | closed | Stage4 unstub path silently no-ops on multi-function run files; deploy was rolled back | 2026-08-17 |
| stage4_windows_c_abi_inference_2026-07-17 | P3 | fixed | Stage4 inferred the Windows C ABI from the object-file suffix instead of the resolved compiler | 2026-09-12 |
| stage54_hosted_entry_closure_symbol_ownership_2026-07-13 | P2 | closed | Hosted entry/build objects retain unresolved run_check and json_serialize with no provider | 2026-08-17 |
| star_import_does_not_reach_expect_not_in_std_spec_2026-08-04 | P2 | closed | use std.spec.* does not import expect_not; only the explicit brace form resolves it | 2026-08-17 |
| std_async_runtime_native_backend_gaps_2026-06-11 | P2 | closed | std.async native backend lacks poll/sffi implementations so async ops fall back or stub | 2026-08-17 |
| std_crypto_sha512_common_digest_aborts_in_harness_2026-06-15 | P2 | closed | std.crypto SHA-512 common digest aborts under the spec harness on an empty-string input | 2026-08-17 |
| std_facade_shadows_tier_module_family_2026-08-08 | P2 | fixed | src/lib/<name>.spl facades shadow tier modules via src/std->lib, dropping tier APIs | 2026-08-17 |
| std_hash_facade_shadows_noalloc_hash_package_2026-08-08 | P2 | fixed | std.hash facade shadows the noalloc hash package and drops its API; unresolved use is only a warning | 2026-09-13 |
| stdlib_uses_letelse_ahead_of_deployed_compiler_2026-07-25 | P3 | closed | stdlib env/variables.spl uses refutable val-else syntax no shipped binary could parse | 2026-08-17 |
| std_math_abs_f64_returns_zero_2026-08-08 | P1 | fixed | math_abs(-3.0) returns 0.0 on the interpreter path | 2026-09-13 |
| strict_stage3_selfhost_body_failures_2026-07-13 | P2 | closed | Strict stage3 self-host fails on ambiguous/misresolved method bodies | 2026-08-17 |
| string_interp_brace_across_concat_literals_2026-07-03 | P2 | closed | Interpolation brace scanner runs past a string boundary across concatenated literals | 2026-08-17 |
| string_literal_double_brace_collapse_2026-06-16 | P2 | closed | {{ and }} collapse to a single brace in ALL string literals, not just interpolated ones | 2026-08-17 |
| struct_ctor_field_var_cross_module_2026-06-15 | P2 | fixed | Struct ctor Type(field: var) fails unknown argument in a cross-module spec context | 2026-08-17 |
| struct_field_aliases_under_jit_2026-08-08 | P1 | closed | A struct stored in a class field aliases under the JIT, violating value semantics | 2026-08-17 |
| struct_field_array_pop_no_shrink_2026-07-30 | P1 | fixed | .pop() on a struct-field array does not shrink the array on current main | 2026-08-17 |
| struct_shorthand_arg_order_binds_wrong_field_2026-07-20 | P1 | closed | Struct-literal shorthand arg after an explicit named arg binds to nil/the wrong field slot | 2026-08-17 |
| svmg_a2_record_ring_head_counter_diverges_from_d2_ref_vm_2026-08-07 | P2 | fixed | A2 record-ring layout has no head-counter word, diverging from D2/ref_vm | 2026-09-13 |
| symbolkind_enum_match_fails_cross_module_discriminant_minus_one_2026-07-29 | P1 | fixed | rt_enum_discriminant returns -1 so SymbolKind variant patterns never match through HirLowering.symbols | 2026-09-13 |
| t16_blend_span_c_symbol_not_reachable_three_implementations_2026-08-07 | P2 | fixed | rt_engine2d_simd_fill_span_u32 absent from libsimple_runtime.a; 3 divergent kernel impls | 2026-09-13 |
| table_lib_missing_set_import_and_method_gaps_2026-07-20 | P2 | closed | table.spl still lacks any Set import; group_by/agg/value_counts gaps unfixed | 2026-08-17 |
| tag_boxing_value_corruption_family_triage_2026-08-01 | P1 | fixed | ?? on a raw i64 whose value is 3 returns none under JIT (TAG_SPECIAL=0b011 collision) | 2026-09-13 |
| target_arch_enum_enum_collision_option_2026-07-18 | P2 | fixed | Duplicate TargetArch enum in backend_selector.spl corrupts Option<TargetArch>.? under full | 2026-09-13 |
| tauri_mdi_input_to_paint_validator_hang_2026-07-04 | P3 | closed | tauri mobile MDI input-to-paint validator hangs 60s+ on malformed detail rows | 2026-08-17 |
| tauri_shell_mdi_bootstrap_css_inset_assertion_stale_2026-07-07 | P2 | closed | lib.rs:2546 asserts '#wm-desktop{position:fixed;inset:0' but bootstrap emits 'inset:0 0 58 | 2026-08-17 |
| test_daemon_client_deadline_not_forwarded_2026-07-19 | P3 | closed | Light-daemon client stops waiting after 1s while daemon holds child to fixed 600s bound | 2026-08-17 |
| test_db_cold_start_never_created_2026-08-10 | P3 | fixed | Test DB cold-start fixed but residual gap remains: warning path still records nothing in o | 2026-08-17 |
| test_helpers_namespace_unresolved_deep_paths_2026-07-06 | P2 | closed | test.helpers.* module namespace fails to resolve from spec paths at depth >= 5 below test/ | 2026-08-17 |
| test_level_filters_never_match_numbered_trees_2026-07-27 | P2 | closed | --unit/--integration/--system filters match only legacy test/unit mirror, never test/01_un | 2026-08-17 |
| test_runner_emits_no_result_summary_silent_exit0_2026-08-17 | P1 | fixed | bin/simple test <spec> prints no pass/fail summary and exits 0 (silent green) on deployed | 2026-08-17 |
| test_runner_expect_failure_swallowed_u8_bytes_2026-07-03 | P2 | closed | Sabotaged expect() in wav_encode_spec u8 byte-array case is swallowed; spec still reports | 2026-08-17 |
| test_runner_interpreter_file_summary_greenwash_2026-07-03 | P1 | closed | Interpreter-mode file summary reports 'Failed: 0' while individual it blocks fail | 2026-08-17 |
| test_runner_json_format_not_machine_readable_2026-07-24 | P3 | closed | Test runner --format=json output is not machine-parseable (interleaved non-JSON text) | 2026-08-17 |
| test_runner_phantom_failed_after_all_examples_pass_2026-07-20 | P1 | closed | File-level Failed count adds a phantom +1 after all it examples pass (9+ confirmed specs) | 2026-08-17 |
| test_runner_stray_full_repo_lint_scan_false_fail_2026-07-20 | P2 | closed | A single spec run triggers a full-repo lint scan whose warnings flip a green spec to FAIL | 2026-08-17 |
| test_spec_tracking_docgen_orphaned_2026-06-16 | P3 | closed | doc/08_tracking/test/test-spec.md no longer regenerated by bin/simple test (pure-Simple pa | 2026-08-17 |
| test_unit_legacy_mirror_divergence_2026-08-04 | P1 | fixed | test/unit is a frozen 8,308-file mirror of test/01_unit and BOTH run, giving conflicting v | 2026-09-13 |
| text_byte_len_vs_codepoint_index_family_2026-08-06 | P2 | fixed | char_at(i) fed byte-length loop bounds corrupts non-ASCII in ui/theme_package_wire and htm | 2026-09-13 |
| text_find_native_exposure_audit_2026-07-31 | P3 | closed | .find() byte-offset sites in src/**; audit retracted its BYTE/CHAR-RISK premise same day | 2026-09-13 |
| text_index_of_on_substring_receiver_reported_bool_2026-08-09 | P2 | closed | text.index_of on a substring receiver is typed as returning bool, so idx compares wrong | 2026-08-17 |
| text_index_of_returns_nil_in_simpleos_freestanding_2026-07-28 | P2 | fixed | text.index_of yields the ?? default instead of index 3 on non-erased receivers | 2026-08-17 |
| text_index_of_start_arg_dropped_and_error_sentinel_leak_2026-07-28 | P1 | closed | text.index_of(needle,start) drops start; run lane leaks the error sentinel as a data value | 2026-08-17 |
| text_len_bytes_vs_index_codepoints_2026-07-02 | P1 | closed | text.len() returns bytes while text[i] indexes codepoints, so ASCII-safe loops panic on | 2026-08-17 |
| text_starts_with_miscompiled_to_bytespan_name_collision_2026-07-27 | P1 | closed | cranelift resolves methods by name only, so text.starts_with compiles to | 2026-08-17 |
| text_static_method_hir_lowering_2026-07-23 | P2 | closed | static method call on builtin type name `text` is unresolved in HIR entry-closure lowering | 2026-08-17 |
| text_substring_o_offset_parse_html_quadratic_2026-07-07 | P2 | fixed | text.substring cost scales with start offset (UTF-8 rescan), making offset loops quadratic | 2026-09-13 |
| theme_package_missing_deps_2026-06-26 | P3 | closed | theme_package_spec cannot run: required runtime modules are absent with no git history | 2026-08-17 |
| theme_package_source_capture_design_hard_stop_2026-07-27 | P3 | closed | theme package source-capture design series rejected; wire format landed but capture | 2026-08-17 |
| theme_package_transaction_sync_owner_blocker_2026-07-27 | P2 | closed | theme package install transaction has no synchronization owner, so concurrent installs | 2026-08-17 |
| theme_service_notification_transport_contract_2026-07-24 | P2 | closed | theme_service has no notification transport contract, so theme-change subscribers get | 2026-08-17 |
| theme_web_frame_acceptance_unguarded_2026-07-27 | P1 | closed | external Web frame acceptance never reads or stores a theme identity, so every frame is | 2026-08-17 |
| threadpool_duplicate_export_collapses_type_2026-08-02 | P1 | fixed | two exported classes named ThreadPool collapse into one type exposing neither class's API | 2026-09-13 |
| todo_call_collapses_to_pass_todo_node_reqc003_unreachable_2026-08-07 | P3 | fixed | todo(...) parses to the same AST node as pass_todo(...), leaving REQC003's branch | 2026-09-13 |
| to_int_optional_lies_and_some_i64_payload_shift_2026-07-27 | P1 | closed | text.to_int() optional never signals failure and Some(<i64>) payload is shifted x8 under | 2026-08-17 |
| top_level_return_falls_through_2026-08-01 | P2 | fixed | statement-level return does not terminate the function in the pure-Simple MIR lane | 2026-08-17 |
| treesitter_real_specs_150_of_151_tautologies_pythontrue_lint_2026-08-06 | P2 | fixed | four treesitter_*_real_spec files report 151/151 green while 150 examples are literally | 2026-09-18 |
| try_operator_bare_nil_option_none_mismatch_2026-07-20 | P2 | closed | `?` rejects a bare nil returned from an Option<T>-typed function with got nil | 2026-08-17 |
| try_operator_on_option_no_early_return_2026-08-08 | P1 | fixed | Option try propagation emits a single-evaluation absence branch that returns None while Some yields its payload | 2026-09-14 |
| tuple_destructuring_does_not_bind_2026-07-27 | P1 | closed | val (a,b,c) = <non-tuple> silently binds nothing instead of erroring | 2026-08-17 |
| two_standing_limits_independently_verified_2026-08-08 | P3 | closed | the 42/29 shape-(d) oracle count is stale and the lexer harness does emit a verdict | 2026-09-13 |
| two_std_specs_reference_nonexistent_api_and_assert_nothing_2026-08-04 | P3 | fixed | test/01_unit/std/mock_simple_spec imports a nonexistent class; standalone_test asserts | 2026-09-18 |
| type_alias_declarations_discarded_at_parse_2026-07-29 | P1 | fixed | `type X = Y` alias declarations are dropped at parse time so no later stage can see them | 2026-09-13 |
| type_infer_correctness_spec_shadows_hminfercontext_2026-08-10 | P3 | fixed | type_infer_correctness_spec shadows HmInferContext with a 1-field stand-in, so it tests | 2026-09-13 |
| u8_index_generics_deprecation_false_positive_test_path_2026-06-28 | P2 | fixed | `[u8]` array indexing is mis-flagged as deprecated generics; migrate --fix-generics would | 2026-08-17 |
| ui_backend_isolation_gate_red_and_unreachable_2026-08-01 | P1 | fixed | UI backend-isolation gate has been red since 2026-07-25 and is never executed in CI | 2026-09-13 |
| ui_browser_shared_wm_flag_dropped_2026-07-05 | P2 | closed | ui.browser --shared-wm flag is silently dropped on the real launch path | 2026-08-17 |
| unify_occurs_check_unreachable_2026-08-02 | P2 | closed | occurs_check() never recurses into type structure so UNIFY_FAIL_OCCURS is unreachable | 2026-09-13 |
| unit_composite_to_conversion_and_power_operator_2026-07-20 | P2 | closed | Composite-unit .to() returns bool instead of converted value; `^` unsupported unit^number | 2026-08-17 |
| unit_return_fn_pointer_sigill_2026-06-14 | P2 | closed | Calling a `fn() -> ()` function pointer crashes with SIGILL rc=132 and no diagnostic | 2026-08-17 |
| unit_type_si_prefix_and_suffix_bugs_2026-07-20 | P2 | closed | Unit literal SI prefixes _k/_m do not scale and .suffix() returns the wrong string | 2026-08-17 |
| unknown_field_access_no_static_error_2026-08-10 | P1 | fixed | Nominal receivers reject fields owned only by unrelated structs while explicit Any lookup remains dynamic | 2026-09-14 |
| unresolved_type_nested_struct_projection_2026-07-17 | P2 | closed | Unresolved name in grouped `use` is silently accepted, then .x projection defaults to g... | 2026-08-17 |
| untyped_list_element_read_seed_rootcause_2026-07-30 | P1 | fixed | Untyped `list` element read lowers to a struct-field read, returning wrong values | 2026-09-13 |
| untyped_list_param_census_2026-07-29 | P3 | closed | 148 files / 1257 sites declare untyped `list` params exposing the element-read defect | 2026-09-18 |
| unwrap_or_return_default_value_dropped_2026-07-20 | P2 | closed | `unwrap or_return: <default>` drops the default and propagates like `?` instead | 2026-08-17 |
| user_class_named_promise_resolved_static_method_shadowed_2026-07-20 | P2 | fixed | User-defined class Promise<T> static fn resolved()/rejected() shadowed by builtin async... | 2026-09-13 |
| var_overlay_compiler_reloc_engine_no_callers_2026-06-29 | P3 | closed | linker/reloc_engine.spl has zero external callers - the variant-overlay seam is uninteg... | 2026-08-17 |
| vector_glyph_path_null_deref_desktop_render_pipeline_2026-07-19 | P2 | closed | Residual downstream render-pipeline fault remains after the glyph-cache null-deref was ... | 2026-09-13 |
| verification_lean_init_missing_use_before_export_2026-07-20 | P2 | closed | lean/__init__.spl bare `export` lines never import the symbols, so package-level `use` ... | 2026-08-17 |
| verification_std_cross_module_type_name_collision_2026-08-17 | P1 | fixed | ContractExpr/ContractExprKind resolve to the wrong module across verification/models | 2026-09-13 |
| vhdl_backend_branch_local_and_aggregate_codegen_gaps_2026-07-20 | P2 | closed | VHDL backend fails codegen for branch-local computation and struct/array aggregates | 2026-08-17 |
| vhdl_backend_spec_multi_api_mismatch_2026-07-20 | P2 | closed | vhdl_backend_spec: 22 failures from genuine backend API mismatches after import fixes | 2026-08-17 |
| vhdl_entryfile_crossmodule_enum_resolve_2026-07-18 | P2 | closed | VHDL entry-file compile leaves an imported cross-module enum type unresolved | 2026-08-17 |
| vhdl_sffi_rt_process_run_capture_extern_missing_2026-08-09 | P2 | fixed | vhdl_sffi declares extern rt_process_run_capture, which exists in neither runtime | 2026-08-17 |
| vmm_copyin_cross_page_bytes_lost_2026-07-20 | P1 | closed | vmm_copyin_bytes_from_space returns empty bytes when a copy crosses two mapped pages | 2026-08-17 |
| vulkan_ffi_loader_probe_inverted_2026-08-09 | P2 | fixed | loader_probe() returns false on a working loader: call0 returns 0 on success, tested !=0 | 2026-08-17 |
| vulkan_raster_kernels_noop_and_divergent_2026-06-17 | P2 | closed | 4 of 10 Vulkan raster kernels are still no-ops or diverge from the CPU reference | 2026-08-17 |
| vulkan_submit_and_wait_fence_blocks_unconditionally_no_nonblocking_submit_2026-08-07 | P2 | fixed | rt_vulkan_submit_and_wait_fence always waits on u64::MAX so a host fence timeout never ... | 2026-08-17 |
| vulkan_vm_executor_run_source_clobbers_arena_data_each_call_2026-08-08 | P2 | fixed | VulkanVmExecutor.run_source rebuilds a zeroed 128KiB arena per call, wiping cross-cell | 2026-09-13 |
| wasm_cli_emit_no_artifact_2026-05-30 | P2 | fixed | simple compile --target wasm32-wasi exits 3 (or 0) and writes no .wasm output file | 2026-09-18 |
| watchdog_externs_unregistered_module_uncalled_2026-07-08 | P3 | closed | extern rt_watchdog_start/rt_watchdog_stop have zero FFI registration in the Rust/C runtime | 2026-08-17 |
| web_compute_styles_residual_quadratic_2026-07-06 | P2 | closed | compute_styles remains superlinear after WEB-2 dedup fix; cost shifted to O(offset) | 2026-08-17 |
| web_font_provider_split_nested_call_resolution_2026-07-14 | P2 | closed | Seed compiler cannot resolve .split() on an erased receiver in nested call context | 2026-08-17 |
| web_gpu_paint_text_gradient_still_residual_blit_2026-07-06 | P3 | closed | Text/gradient/border draw commands still round-trip via CPU blit after the rect GPU | 2026-08-17 |
| webgui_font_path_seed_verification_2026-07-20 | P3 | closed | Web/GUI font path cannot be verified on the deployed seed; no independent evidence exists | 2026-08-17 |
| web_infra_interpreter_blockers_2026-06-04 | P2 | closed | Web framework router and sqlite runtime paths hit interpreter blockers in the web infra | 2026-09-13 |
| web_render_budget_interpreter_gap_2026-07-25 | P2 | closed | Paint-budget expiry under the interpreter yields a uniform (blank) frame instead of | 2026-08-17 |
| web_render_dpi_scaling_unsupported_2026-07-12 | P3 | closed | Web layout/paint engine has no device-pixel-ratio hook; HiDPI renders at 1x only | 2026-08-17 |
| web_renderer_duplicate_public_entry_binding_2026-08-04 | P1 | fixed | simple_web_render_html_to_pixels_with_engine2d_backend is defined in two modules; use | 2026-09-13 |
| web_renderer_layout_paint_hang_resolution_independent_2026-07-14 | P1 | closed | Pure-Simple web renderer hangs in compute_styles regardless of pixel count, blocking PPM | 2026-08-17 |
| web_render_file_gui_nil_receiver_2026-07-11 | P2 | closed | web_render_file_gui crashes with a nil-receiver method call on the file-render path | 2026-08-17 |
| web_render_file_gui_present_stall_large_page_2026-07-11 | P2 | fixed | web_render_file_gui presents small pages but stalls presenting a full google.com page | 2026-09-13 |
| web_render_full_engine_call_order_nondeterminism_2026-07-12 | P1 | closed | Full HTML layout engine emits different pixels for identical input depending on call order | 2026-08-17 |
| web_render_full_engine_content_frame_reroute_perf_2026-07-12 | P3 | closed | Full HTML layout engine is 55-60x slower per content-frame re-render than the tag-strip | 2026-08-17 |
| web_render_gpu_backend_provenance_fabricated_2026-06-17 | P1 | closed | Web-render reported a GPU backend provenance it never obtained from a device | 2026-08-17 |
| web_render_iframe_material_fallback_provenance_2026-07-24 | P3 | closed | Nested-iframe material fallback reports provenance that does not identify the real | 2026-08-17 |
| web_wm_modern_shell_spec_perf_2026-06-04 | P3 | closed | Web WM modern shell spec exceeds the runner's perf threshold | 2026-08-17 |
| while_val_pattern_binding_not_visible_in_body_2026-07-20 | P2 | closed | while val Pattern(x) = expr: body reports variable not found for the bound x | 2026-08-17 |
| whole_test_runner_doctest_import_comment_guard_2026-07-18 | P3 | closed | Whole test runner skips doctest files whose imports are comment-only | 2026-08-17 |
| widget_showcase_frame_distribution_unverified_2026-07-27 | P3 | closed | Widget showcase frame distribution has never been verified against captured evidence | 2026-08-17 |
| wildcard_std_spec_import_drops_expect_not_2026-08-04 | P1 | fixed | use std.spec.* silently omits expect_not, the matcher the linter and checker_spipe emit | 2026-09-13 |
| windows_build_subcommand_silent_noop_stale_binary_2026-08-05 | P1 | fixed | bin/simple build (incl. build bootstrap) silently no-ops on native Windows, leaving a | 2026-09-20 |
| windows_materialized_symlink_alias_git_state_timeout_2026-09-09 | P1 | fixed | Windows materialized aliases use receipt-aware directory collapse and bounded git-state enumeration | 2026-09-14 |
| window_scene_draw_ir_spec_timeout_2026-07-24 | P3 | closed | window_scene_draw_ir focused spec times out instead of completing | 2026-08-17 |
| wine_hello_fixture_spec_orphaned_api_drift_2026-07-20 | P2 | closed | wine_hello_fixture_spec.spl imports 4 symbols removed from the old Wine-exe-probe API | 2026-08-17 |
| wine_proton_runtime_modules_missing_2026-07-20 | P2 | closed | common.wine_proton_gate and common.wine_proton_runtime modules do not exist, so their | 2026-08-17 |
| win_fs_window_record_encode_gap_and_entries_field_2026-07-20 | P2 | closed | window_record_encode is undefined and WindowRecord lacks the entries field its callers | 2026-08-17 |
| with_statement_exit_self_field_mutation_lost_2026-07-20 | P2 | closed | with-as invokes __exit__ but implicit-self field mutations inside __exit__ are discarded | 2026-08-17 |
| wm_click_semantics_and_hit_test_recompute_2026-07-05 | P2 | closed | WM close-button/drag actions fire on mouse-DOWN with no release-inside or drag-away cancel | 2026-08-17 |
| w_mc_res_001_app_code_triage_2026-08-08 | P3 | fixed | dwarf_load forwarder re-exposes raw rt_dwarf_load handle beside an existing managed | 2026-09-13 |
| wm_font_config_language_corrupted_by_cross_struct_copy_2026-08-11 | P1 | fixed | config.language reads 'normal' instead of 'und' via cross-struct copy; all 8 text Draw IR | 2026-09-13 |
| wm_glass_material_mode_blocks_all_provenance_2026-07-26 | P3 | closed | WM glass material provenance unverified on current runtime after 6b18dcd874f source | 2026-08-17 |
| wm_mouse_wheel_events_dropped_2026-07-05 | P2 | closed | Mouse wheel events decoded by ps2_mouse driver are dropped above the compositor layer | 2026-08-17 |
| wm_native_resize_ignored_stale_buffer_2026-07-05 | P2 | closed | Hosted WM ignores EVENT_WINDOW_RESIZED; winit backend allocates pixel buffer once at | 2026-08-17 |
| wm_showcase_no_headless_lane_2026-07-25 | P3 | closed | host-WM showcase wrappers require SIMPLE_GUI=1 and have no offscreen presentation lane | 2026-08-17 |
| wm_theme_css_loaded_not_applied_2026-07-20 | P2 | closed | Guest CSS theme loads (bytes=1276) but in-guest chrome colors never change | 2026-08-17 |
| wm_widget_headless_default_ppm_path_write_fails_2026-07-25 | P2 | closed | Headless WM capture writes ppm-write-failed on the default path, passes with an explicit | 2026-08-17 |
| wm_window_title_text_not_rendered_2026-07-20 | P2 | closed | WM window titlebar title text renders zero pixels in-guest while close X and taskbar | 2026-08-17 |
| x25519_extern_not_registered_interp_2026-06-15 | P1 | closed | X25519 returned the wrong shared secret for every input; RFC 7748 5.2/6.1 vectors failed | 2026-09-13 |
| x25519mlkem768_cuda_kernel_artifact_missing_2026-08-05 | P2 | fixed | X25519MLKEM768 CUDA kernel source and cubin generator exist only uncommitted in a foreign | 2026-09-13 |
| x25519mlkem768_vulkan_ntt_negative_modulo_driver_defect_2026-08-05 | P2 | fixed | Negative-operand % on the NVIDIA Vulkan compute path yields mismatched ML-KEM NTT | 2026-09-13 |
| x25519mlkem768_vulkan_spirv_artifact_missing_2026-08-05 | P2 | fixed | X25519MLKEM768 Vulkan SPIR-V .comp source and generator are uncommitted, absent from this | 2026-09-13 |
| x64_freestanding_layout_sensitive_dup_displaced_stores | P1 | closed | Freestanding frame builder emitted duplicated slot stores displacing later stores by +16 | 2026-09-13 |
| x64_freestanding_mmio_read_u8_address_dependent_zero | P1 | closed | Freestanding rt_mmio_read_u8 returns 0 where a C load at the same address reads 127 | 2026-09-13 |
| x64_freestanding_module_level_val_u32_desktop_gui_2026-07-12 | P2 | closed | Freestanding native-build silently corrupts a module-level val: u32 read inside | 2026-08-17 |
| x64_freestanding_module_vs_entry_ring3_handoff | P2 | fixed | clang aborts 134 during static-libc init in ring-3; freestanding CRT/syscall surface | 2026-09-13 |
| x64_sshd_version_exchange_freestanding | P2 | fixed | x86_64 in-guest sshd reads an EMPTY client version and aborts the SSH version exchange | 2026-09-13 |
| x86_64_baremetal_fake_clock_budget_burn_2026-07-26 | P2 | closed | Guest compute_styles breaks on its wall-clock budget at node 0, so every node keeps the | 2026-08-17 |
| x86_freestanding_guarded_optional_unwrap_returns_bool_2026-07-25 | P1 | closed | x86 freestanding guarded optional unwrap yields the guard boolean instead of the | 2026-08-17 |
| zstd_fresh_table_literal_decoder_and_contradictory_specs_2026-06-30 | P2 | closed | Two specs demand different errors for the same 22-byte zstd frame; fresh-table literal | 2026-08-17 |
| zstd_fse_sequence_lsb_reader_blocks_host_frames_2026-06-30 | P2 | closed | zstd FSE sequence decoder uses LSB-first backward reader, so any real host frame with | 2026-08-17 |
| zstd_sequence_rle_normal_offset_mismatch_2026-07-20 | P3 | closed | zstd normal-offset sequence decodes as a back-reference copy, giving [97,98,99,97,98,99] | 2026-08-17 |
| dashboard_main_api_never_implemented_2026-07-28 | P2 | closed | app.dashboard.main is a 14-line stub — both dashboard modules import an API that was never written | 2026-08-21 |
| engine2d_factory_returns_dict_under_test_runner_2026-08-19 | P1 | closed | Engine2D factory returns a module-namespace dict under the test runner (match-arm binding shadowed by MODULE_G | 2026-08-21 |
| jit_array_element_i64_storage_truncation_2026-08-17 | P1 | closed | An i64 stored in an array is TRUNCATED under the JIT (data loss not a print defect) | 2026-08-21 |
| jit_does_not_enforce_val_block_scope_2026-08-17 | P1 | fixed | JIT does not enforce val block scope; the interpreter does | 2026-09-13 |
| jit_is_some_is_none_method_dispatch_gap_2026-08-17 | P1 | closed | JIT: .is_some() / .is_none() method calls fail closed OR return a raw untagged bool | 2026-08-21 |
| jit_swallows_undeclared_extern_and_exits_zero_2026-08-17 | P1 | fixed | JIT hybrid execution reports an unbacked extern and exits 1 instead of fabricating nil | 2026-09-14 |
| narrow_int_result_unwrap_or_returns_boxed_shift_2026-08-17 | P1 | closed | Result<u8>.unwrap_or returns 222<<3; (u8?) via ! returns the nil tag | 2026-09-13 |
| native_build_fabricates_weak_stub_for_unimplemented_extern_2026-08-18 | P1 | fixed | native-build fabricates a WEAK stub for an unimplemented extern fn which returns garbage at runtime — and th | 2026-09-13 |
| stage3_lookup_or_invalid_returns_unrelated_symbol_id_2026-08-18 | P1 | fixed | Stage 3: lookup_or_invalid(name) returns the id of an UNRELATED symbol (2026-08-18) | 2026-09-13 |
| test_manifest_invalidation_is_size_only_mtime_never_read_2026-08-17 | P1 | fixed | Test manifest fingerprints use real filesystem mtime and force rescan on zero or metadata failure | 2026-09-14 |
| macos_seed_unbuildable_metal_module_ungated_2026-08-30 | P0 | fixed | macOS Rust seed unbuildable: Metal module gated on target_os only, not the metal cargo feature; 73 errors blocked every macOS bootstrap | 2026-08-30 |
| macos_bootstrap_lane_platform_defect_cluster_2026-08-30 | P0 | fixed | macOS bootstrap original eight-defect cluster: Stage 2 admitted and platform regression gates pass | 2026-09-21 |
| bootstrap_capsule_permission_scan_failure_admitted_2026-09-21 | P0 | fixed | Capsule permission traversal errors now fail closed; macOS contract suite passes | 2026-09-21 |
| seed_jit_app_module_function_call_segfaults_windows_2026-09-13 | P1 | fixed | Windows seed JIT refuses unresolved app-module imports instead of finalizing NULL call targets | 2026-09-14 |
| seed_jit_function_local_use_segfaults_2026-09-13 | P1 | fixed | Windows seed JIT de-JITs unresolved function-local-use calls instead of jumping through NULL imports | 2026-09-14 |
| env_platform_process_owner_spec_asserts_unauthored_layering_2026-09-14 | P2 | fixed | Process-owner contract spec follows the authored platform facade rather than asserting nonexistent layering | 2026-09-14 |
| macos_ctx_hook_gnu_sed_alternation_denies_all_bash_2026-08-30 | P1 | fixed | GNU-only sed backslash-pipe alternation in the ctx hook denied every Bash call on macOS (fail-closed hook) | 2026-08-30 |
| macos_seed_variadic_open_mode_t_u16_e0617_2026-08-30 | P1 | fixed | u16 mode_t passed to variadic open(2) fails to compile on Apple targets (E0617) | 2026-08-30 |
| macos_seed_st_mtimespec_absent_from_libc_e0609_2026-08-30 | P1 | fixed | st_mtimespec is absent from the libc stat struct on Apple targets (E0609) | 2026-08-30 |
| bootstrap_preflight_hardcodes_linux_mnt_data_cargo_dir_2026-08-30 | P1 | fixed | The mandated pre-bootstrap preflight gate hardcoded a Linux-only /mnt/data cargo dir and was therefore always RED on macOS | 2026-08-30 |
| capsule_immutability_check_fail_open_gnu_find_perm_2026-08-30 | P0 | fixed | Runtime-capsule and stage3-authority immutability checks used GNU-only find -perm /0222; on BSD find it errored to stderr and printed nothing, so the check was FAIL-OPEN | 2026-08-30 |
| weak_symbol_detection_elf_only_nm_kinds_macho_2026-08-30 | P1 | fixed | Weak-symbol detection used ELF nm kind letters W and V; Mach-O prints weak definitions as T, so every weak fallback looked strong and the Stage-4 capsule guard rejected the build | 2026-08-30 |
| process_group_setsid_absent_on_macos_2026-08-30 | P1 | fixed | setsid is util-linux and absent on macOS; used by two twin copies of io/process_ops.spl (src/lib and src/app) and by run-process-group-timeout.shs | 2026-08-30 |
| seed_interpreter_stdin_read_line_erases_eof_2026-09-06 | P1 | fixed | Seed interpreter's Stdin.read_line() erases EOF into Ok('') -- fixed in interpreter_extern/io/input.rs, seed not yet redeployed | 2026-09-06 |
| enum_variant_resolved_globally_by_bare_name_httpmethod_collision_2026-09-06 | P1 | fixed | MIR enum lookup prefers the HIR-resolved TypeId over a last-wins bare-name registry | 2026-09-14 |
| parser_hangs_on_it_block_inside_function_body_2026-09-06 | P1 | closed | Parser hangs forever on a spec it block nested inside a function body (hid 28 failing tests behind a 900s timeout) | 2026-09-06 |
| interpreter_process_is_running_false_for_unspawned_pid_2026-09-06 | P2 | fixed | Interpreter's rt_process_is_running returns false for any pid it did not spawn -- fixed in interpreter_extern/system.rs, seed not yet redeployed | 2026-09-06 |
| bootstrap_repository_full_tests_json_false_pass_2026_09_21 | P1 | fixed | Phase 3 and Phase 4 repository inventories reject duplicate JSON keys and multiple terminal rows through the canonical validator | 2026-09-21 |
| bootstrap_preflight_pass_not_retained_or_resume_bound_2026_09_21 | P0 | fixed | Full bootstrap retains source/head/config-bound preflight evidence and Stage 3/4 resumes verify and preserve its hash | 2026-09-21 |
| stage2_link_rt_array_bytes_basis_missing_in_rust_runtime_2026_10_19 | P0 | fixed | Stage 2 link fails: rt_array_bytes_basis_ptr/len missing from the Rust runtime (fixed upstream by #3809) | 2026-10-19 |
| stage3_bootstrap_closure_lower_module_default_args_segv_2026_10_19 | P0 | fixed | Stage 3 bootstrap-fixed closure loop SIGSEGVs: cross-module lower_module call omits defaulted params (fix 83ff46b0bc4) | 2026-10-20 |
| stage3_rt_criticality_validation_memory_spike_2026_10_19 | P0 | fixed | Stage 3 rt_criticality HIR validation grows the compiler from ~5 GB to >42 GB after HIR completes | 2026-10-19 |
| seed_setter_forwarding_silent_noop_2026_10_26 | P0 | fixed | Seed interpreter ignored set_<name> on obj.name = v (silent no-op, exit 0); undefined field now errors | 2026-10-26 |
| seed_hir_getter_setter_forwarding_dejit_2026_10_26 | P1 | fixed | Seed HIR lowering lacked get_/is_/set_ forwarding: Cannot infer field type dropped module to interpreter | 2026-10-26 |
| seed_trait_alias_forwarding_unsupported_2026_10_26 | P1 | fixed | Seed parser treated alias Trait = field as a field (variable inner not found); now expands trait forwarders | 2026-10-26 |
