# Handoff: seed, DevHub, caret suite, stdlib and SOSIX bugs (2026-11-04)

Generated from `bug_db.sdn` on release/1.0.0. The session that produced these lanes **stopped fixing** these areas on 2026-11-04 by user decision; they are handed to other agents.
Phase-3/4-essential bootstrap work stays with the phase-3 lane. Before starting a row: `sh scripts/check/bug-claim.shs claim <id>` and set status `fixing` in bug_db so work is not duplicated.
Rows marked `fixing` may still have an open PR from the stopping lanes: check `gh pr list --base release/1.0.0` first. `fix-implemented-verification-pending` = fix landed, needs a run on a redeployed seed/stage3.

## Seed (Rust seed: interpreter / JIT / compiler_rust)

| id | sev | status | title | file |
|-|-|-|-|-|
| stage2_struct_field_offset_model_mismatch_oob_read_2026-08-30 | P0 | fix-implemented-verification-pending | Erased-receiver field fallback uses the smallest in-bounds candidate index across local and imported metadata | src/compiler_rust/compiler/src/hir/lower/type_resolver.rs |
| bare_assert_statement_vacuity_2026-08-02 | P1 | fix-implemented-verification-pending | Bare `assert` parser and interpreter behavior restored; native link verification remains pending | src/compiler/10.frontend/core/parser_stmts.spl |
| bytespan_starts_with_dropped_from_kernel_closure_weak_nil_stub_2026-07-28 | P1 | fix-implemented-verification-pending | ByteSpan.starts_with is dropped from the SimpleOS kernel closure and replaced by a nil-ret | src/compiler_rust/compiler/src/pipeline/native_project/stubs.rs |
| codegen_rt_prefix_local_function_collision_sigsegv_2026-07-12 | P1 | fix-implemented-verification-pending | A local function whose name matches a runtime SFFI symbol compiles to a SIGSEGV | not a cal" |
| core_c_archive_failure_diagnostics_2026_10_12 | P1 | fix-implemented-verification-pending | Bootstrap core-C archive failures lose actionable diagnostics | src/compiler_rust/compiler/src/pipeline/native_project/tools.rs |
| duplicate_public_symbols_differing_return_types_jit_misdispatch_2026-08-09 | P1 | fix-implemented-verification-pending | 373 co-compiled symbol collisions per spec run; identical-signature ones silently vacate | src/compiler/10.frontend/core/interpreter/eval_tables.spl |
| env_get_cocompiled_signature_collision_2026_10_31 | P1 | fix-implemented-verification-pending | env_get resolves to the wrong co-compiled definition on the seed | doc/08_tracking/bug/env_get_cocompiled_signature_collision_2026_10_31.md |
| indexed_char_to_i64_silent_zero_family_2026-08-10 | P1 | fix-implemented-verification-pending | ADR-005 (PR #6249) seed slice: rt_string_to_digit returns Option never 0 (JIT symbol tables) | byte_len in interpreter+JIT; unfixed siblings: rt_string_char_code_at OOB returns 0 |
| interp_dict_class_value_index_mutation_loss_2026-11-03 | P1 | fix-implemented-verification-pending | Interpreter: class value read from Dict by d[k] is a copy (val e = d[\k\]; e.v = 2 leaves d[\k\].v == 0) and d | src/compiler_rust/compiler/src/interpreter |
| interp_me_method_first_param_times8_conditional_2026-06-29 | P1 | fix-implemented-verification-pending | Interpreter binds the first param of some multi-param me methods to value x 8 | src/compiler_rust/runtime/src/value/tags.rs |
| jit_silent_interpreter_fallback_on_unresolved_extern_2026_11_03 | P1 | fix-implemented-verification-pending | JIT silently falls back to interpreter on unresolved externs (rt_text_eq_any | crypto_text_to_bytes) |
| llvm_import_path_mangling_os_prefix_mismatch_2026-06-15 | P1 | fix-implemented-verification-pending | rv64 cross-module calls reference os__kernel__ names while definitions emit bare/weak symbols | link fails" |
| macos_bootstrap_capsule_duplicate_native_all_exports_2026_10_12 | P1 | fix-implemented-verification-pending | macOS Stage2 bootstrap capsule duplicates native-all ABI file and snapshot providers | src/compiler_rust/compiler/src/pipeline/native_project/tools.rs |
| module_name_shadows_function_parameter_2026-09-06 | P1 | fix-implemented-verification-pending | Lambda and thread-spawn parameters remain lexical locals and cannot be captured as same-named imported modules | src/compiler_rust/compiler/src/interpreter/expr/control.rs |
| native_build_reports_success_for_functionless_artifact_2026-08-10 | P1 | fix-implemented-verification-pending | native-build exits success for an artifact containing zero emitted functions | src/compiler_rust/driver/src/cli/native_build.rs |
| option_pattern_accepted_on_non_option_scrutinee_2026-07-27 | P1 | fix-implemented-verification-pending | Some(_) patterns and .unwrap_or are silently accepted on non-Option values; engines disa | src/compiler/10.frontend/core/interpreter/eval_calls.spl |
| phase1_test_monitor_session_escape_2026_10_05 | P1 | fix-implemented-verification-pending | Phase1 seed test monitor escapes admitted bootstrap resource session | src/compiler_rust/driver/src/main.rs |
| primitive_receiver_trait_impl_dispatch_2026-08-07 | P1 | fix-implemented-verification-pending | Trait impl on primitive Self honoured only by interpreter; JIT fails open | native SIGSEGVs" |
| s3_env_policy_digest_nondeterministic_2026-11-02 | P1 | fix-implemented-verification-pending | Frozen stage2 types Result<text,_>? as i64 in env-policy handoff concat/interp so the integrity digest hashes  | src/compiler/00.common/structural_contracts/environment_variant_policy_handoff_v1.spl |
| seed_emit_object_superlinear_hang_large_module_2026-07-20 | P1 | fix-implemented-verification-pending | native-build --emit-object never emits IR for a 479-fn module; runs killed at 1h | 3h and 6" |
| seed_enum_variant_bare_name_last_registration_wins_2026_10_19 | P1 | fix-implemented-verification-pending | Seed resolves enum variants by bare enum name (last registration wins); duplicate ByteOrder broke every native | src/compiler_rust/compiler/src/interpreter_method/mod.rs |
| seed_global_interface_cache_rebuild_latency_2026-10-05 | P1 | fix-implemented-verification-pending | Seed global interface cache key rebuilds unchanged modules | src/compiler_rust/compiler/src/pipeline/native_project/mod.rs |
| seed_if_val_typed_option_class_binds_option_or_segv_2026-11-03 | P1 | fix-implemented-verification-pending | Seed interp: if val c = <typed Option<Class> local or field> binds the Option itself or SEGVs rc=139 | src/compiler_rust/compiler/src/interpreter_control.rs |
| selfhosted_stage4_interpreter_string_interpolation_broken_2026-07-30 | P1 | fix-implemented-verification-pending | Self-hosted stage4 `run` prints the literal placeholder x={x} instead of interpolating | src/compiler/10.frontend/core/lexer_struct.spl |
| simple_cli_invocation_attempts_user_gitconfig_lock_2026-09-09 | P1 | fix-implemented-verification-pending | Simple CLI invocation attempts to lock the user's .gitconfig during a read-only smoke probe | src/compiler_rust/driver/src/main.rs |
| stage2_dotq_presence_value_is_nil_sentinel_2026-11-03 | P1 | fix-implemented-verification-pending | Seed interp fixed: bool-declared locals/consts/statics now take .? presence via present_value_as_bool_arg (was | in-development tag removed. Native/stage2 value-position lowering (mold.spl workaround) verification pending a stage3 rebuild; row moved out of bug_scope" |
| stage3_numeric_interpolation_slot_corruption_2026-08-13 | P1 | fix-implemented-verification-pending | Numeric interpolation of rt_heap_registry_count overwrites the ast_gen_harden_slot array | src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl |
| stage3_selfhost_vtable_field_offset_relro_segv_2026-08-06 | P1 | fix-implemented-verification-pending | Cross-module field read on vtable-bearing class uses wrong offset and writes into RELRO | src/compiler_rust/compiler/src/pipeline/native_project/compiler.rs |
| untyped_fn_result_erased_to_zero_2026-08-01 | P1 | fix-implemented-verification-pending | Value-producing unannotated functions preserve a tagged Any return while procedures and main remain void | src/compiler_rust/compiler/src/hir/lower/module_lowering/function.rs |
| jit_class_mutation_drop_characterization_2026-07-04 | P1 | fix-in-progress-verification-pending | Mutations to class instances read out of an array are silently dropped in interpret mode | src/compiler/70.backend/backend/mod.spl |
| codegen_isa_sffi_text_abi_misexpansion_2026_10_22 | P1 | open | Cranelift ISA/config SFFI wrappers hand-expand text with rt_string_data/rt_string_len; seed-built binaries re- | src/lib/nogc_sync_mut/sffi/codegen.spl |
| interp_class_field_and_nested_element_alias_copy_2026-11-03 | P1 | open | Interpreter default carrier: val a = h.inner (class field) | h.cells[i] and d[k][i] alias is a copy; mutation not visible through the container (JIT keeps it)" |
| jit_layout_run_full_with_ports_nil_receiver_2026-08-02 | P1 | open | layout_run_full_with_ports core-dumps on nil-receiver field access under JIT | src/lib/gc_async_mut/gpu/browser_engine/gpu_web/layout/cuda_execution_port.spl |
| simpleos_native_build_entry_closure_codegen_defects_2026-07-17 | P1 | open | Entry-closure cranelift drops module-global call initializers | nils if-val hits |
| enum_bare_name_collision_registry_2026-08-01 | P1 | verification-pending | Deterministic lookup landed: #6183 (8c7d63e2c36) current-module-first enum lookup in pure-Simple interpreter + | #6111 warning[enum-bare-name-ambiguous] on divergent re-registration |
| release_stage1_native_build_worker_sigsegv_2026_10_20 | P1 | verification-pending | release.yml stage1 native-build worker SIGSEGVs before producing a binary (linux HIR worker | windows immediate); test runner falls back to the bootstrap-only seed (@workaround)" |
| absolute_path_entry_asymmetry_native_build_and_test_2026-08-09 | P2 | fix-implemented-verification-pending | Absolute entries are canonicalized and targeted tests fail closed when no examples execute | src/compiler_rust/driver/src/cli/test_discovery.rs |
| enum_payload_type_mismatch_unresolved_try_2026-10-24 | P2 | fix-implemented-verification-pending | enum payload type mismatch unresolved try (workaround registered) | src/compiler/70.backend/backend/interpreter.spl |
| interpreter_gc_root_scan_blowup_large_array_2026-07-25 | P2 | fix-implemented-verification-pending | Font load goes from ~8s to 2+min merely by keeping an unrelated Engine2D alive on the interpreter stack | src/compiler_rust/compiler/src/value.rs |
| native_method_text_return_prints_handle_2026-07-16 | P2 | fix-implemented-verification-pending | Method returning text prints a raw handle integer instead of the string on non-llvm lanes | src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl |
| native_pattern_payload_text_interpolation_2026_10_31 | P2 | fix-implemented-verification-pending | Native enum text payload interpolated as raw integer: fixed in source by 0528a9ed3ac (decode_declared_enum_pay | 2026-10-30) which postdates the pinned producer 13d73267 that showed it; regression spec pins no rt_raw_i64_to_string on the bound payload; verify by native-building fresh_secured_db with a redeployed producer" |
| seed_list_comprehension_join_and_empty_native_2026_10_21 | P2 | fix-implemented-verification-pending | bootstrap comprehensions lower to nil and erase join receiver | test/fixtures/native/json_comprehension_join/explicit/main.spl |
| seed_receiver_text_join_resolves_to_thread_join_optional_2026-09-13 | P2 | fix-implemented-verification-pending | Builtin receiver method fallback ignores unrelated user-class methods instead of borrowing suffix-colliding re | src/compiler_rust/compiler/src/hir/lower/expr/mod.rs |
| seed_value_match_no_arm_yields_nil_2026-11-02 | P2 | fix-implemented-verification-pending | Seed value match with no matching arm silently yields nil | doc/08_tracking/bug/seed_value_match_no_arm_yields_nil_2026-11-02.md |
| smux_owner_jit_file_read_empty_2026-11-04 | P2 | fix-implemented-verification-pending | ROOT CAUSE (not rt_array_concat nil): if-val binding of a [u8]? extern result was untyped so joined.len() was  | stale deployed seed still affected. Verify: run bin/simple on test/01_unit/lib/text/text_bytes_jit_concat_spec.spl and a main() printing text_bytes_concat_checked result after seed redeploy. Windows smux owner and CLI clients fail under the default JIT lane: std file_read returns empty (rt_array_concat nil) |
| wm_production_fullscreen_evidence_security_registry_any_field_infer_2026-08-09 | P2 | fix-implemented-verification-pending | check-wm-production-fullscreen-evidence.shs still fails; fix 7fa2d06aaa8 not in deployed | src/compiler_rust/compiler/src/mir/lower/lowering_expr_control.rs |
| char_condition_type_check_staged_2026-11-03 | P2 | fixing | Staged: using a char as a condition (if/while/not/and) is a type error per ADR-005; runtime truthiness already | add pure-Simple + seed checker warning now |
| interpreter_pending_skip_dsl_intercept_bypasses_spl_body_2026-08-07 | P2 | fixing | Rust seed interpreter intercepts pending/skip_it/skip before the .spl body in spec.spl ever runs | src/compiler_rust/compiler/src/interpreter_call/bdd.rs |
| interpreter_struct_in_dict_with_closure_field_reads_nil_2026-08-10 | P2 | fixing | Struct stored in a Dict reads back nil on a field that has a closure-typed sibling field | src/lib/nogc_async_mut/actors/actor.spl |
| seed_main_entry_file_text_allocation_failed_2026-11-01 | P2 | fixing | Seed runtime: file reads inside an auto-invoked fn main fail with file text input allocation failed (silent em | src/lib/nogc_sync_mut/io/file_text_session.spl |
| source_fixture_spec_unescaped_interpolation_and_content_drift_2026-07-20 | P2 | fixing | Source-guard specs put {ident} in interpolating strings so they die with `variable | test/01_unit/compiler/hir/module_lowering_dict_keys_source_spec.spl |
| BUG-2026-10-12-CONTEXT-COMPARISON | P2 | open | Rust seed treats a context comparison tail as a context statement | src/compiler/80.driver/driver_hir_pipeline_lowering.spl |
| any_slot_holds_untagged_scalar_2026-08-05 | P2 | open | ANY-typed slots hold raw untagged scalars on the JIT lane | src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl |
| bool_typed_parameter_accepts_non_bool_and_jit_corrupts_it_2026-08-04 | P2 | open | A bool-declared parameter silently accepts a non-bool (rejection half still open) | src/compiler_rust/compiler/src/interpreter_call/core/arg_binding.rs |
| browser_engine_wikipedia_render_perf_2026-07-11 | P2 | open | Real-page software render is ~176s interpreted; 10s budget always degrades | src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl |
| cargo_test_lib_129_failures_triage_2026-08-10 | P2 | open | cargo test -p simple-compiler --lib has 129 remaining unit-test failures after 6 were fixe | src/compiler_rust/compiler/src/lint/checker_core.rs |
| compiler_test_sweep_residuals_2026-08-16 | P2 | open | Compiler test sweep residuals: 8 interpreter gaps plus backend integration fails | src/compiler/10.frontend/core/parser.spl |
| coverage_tooling_does_not_instrument_spl_2026-08-07 | P2 | open | No branch probes from MIR lowering; no coverage artifact on the .spl runner path | src/compiler_rust/compiler/src/mir/lower/lowering_coverage.rs |
| duplicate_type_name_collision_audit_2026-07-17 | P2 | open | Flat global class/enum registries let same-named types in different modules collide at | src/compiler/10.frontend/core/interpreter/eval_tables.spl |
| editor_jit_run_route_blockers_2026-05-28 | P2 | open | editor `bin/simple run` JIT route still blocked on item 2 (deferred) | items 1/3 addressed" |
| enum_discriminant_convention_split_hashed_seed_vs_positional_pure_simple_2026-08-08 | P2 | open | Rust seed hashes enum discriminants while pure-Simple uses positional index; nothing detects a mix | src/compiler_rust/compiler/src/codegen/instr/result.rs |
| image_builder_nvfs_rootfs_marker_preexisting_2026-06-28 | P2 | open | image_builder nvfs rootfs backend marker assertion fails (pre-existing red) | src/os/installer/image_builder.spl |
| interp_class_name_collision_breaks_test_db_persistence_2026-08-10 | P2 | open | Interpreter resolves a class by name across modules | breaking test-DB run persistence" |
| interp_flat_fn_table_load_config_shadowed_2026-11-03 | P2 | open | Interpreter flat function table lets a same-named load_config from another transitively loaded module shadow a | src/app/llm_caret/config.spl |
| interpreter_bdd_missing_structured_test_evidence_2026-07-19 | P2 | open | Pure-Simple BDD consumer still cannot authenticate interpreter results via --assert-ran | src/lib/nogc_sync_mut/spec.spl |
| interpreter_bytes_u64_false_green_memory_2026-08-11 | P2 | open | Interpreter byte allocation reports a U64 false-green and blows up memory on 1MiB push bench | src/compiler_rust/compiler/src/value.rs |
| interpreter_eval_access_calls_drifted_duplicate_definitions_2026-08-11 | P2 | open | Ten drifted duplicate interpreter fn definitions exist and the STALE copies win name resolution | src/compiler/80.driver/driver_source_loading.spl |
| interpreter_result_match_return_sigsegv_2026-07-17 | P2 | open | RunningType::Interpreter SIGSEGVs on a match over a Result with a return inside an arm | src/compiler_rust/compiler/src/interpreter_call/block_execution.rs |
| iso_borrow_check_unreachable_from_interpret_pipeline_2026-08-09 | P2 | open | iso/borrow-check pass is unreachable from the interpret pipeline so bin/simple test never runs it | src/compiler/80.driver/driver_pipeline_passes.spl |
| jit_closure_abi_refuses_lambdas_and_miscompiles_fn_refs_2026-08-06 | P2 | open | JIT refuses whole module containing a lambda | demoting it to the interpreter" |
| jit_lowering_module_alias_and_panic_2026-07-02 | P2 | open | JIT HIR lowering rejects module-alias references and the panic intrinsic | forcing interpreter fallback" |
| jit_struct_assignment_aliases_not_copies_2026-08-10 | P2 | open | JIT struct assignment aliases instead of copying; interpreter copies (residual cases after 2026-08-10) | src/compiler_rust/compiler/src/mir/lower/lowering_stmt.rs |
| jit_text_repeat_dispatch_and_silent_error_substitution_2026-08-01 | P2 | open | JIT text-method dispatch gap substitutes the literal string 'error'; 2 of 51 sibling methods still unwired | src/compiler_rust/compiler/src/codegen/instr/methods.rs |
| js_engine_missing_builtins_regex_promise_prototype_2026-07-11 | P2 | open | JS engine String.replace with a regex is a silent no-op | src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl |
| lean_native_constructor_default_argument_2026_10_21 | P2 | open | bootstrap seed cannot lower imported constructor-expression defaults | src/plugins/backend_lean/lean_backend.spl |
| llvm_inline_asm_dialect_false_green_2026_10_12 | P2 | open | LLVM seed drops Intel-syntax inline asm port instructions without an explicit dialect | src/lib/nogc_async_mut_noalloc/baremetal/x86/io.spl |
| mangler_bare_extern_sibling_split_part_2026-07-30 | P2 | open | Seed mangler emits a bare extern for a free fn shared across sibling split-part modules behind a facade | src/compiler_rust/compiler/src/pipeline/native_project/mangle.rs |
| match_on_enum_native_lowering_status_2026-08-07 | P2 | open | Payload-bearing enum match is still wrong under --native (LLVM AOT); payload-free is fixed | src/compiler_rust/compiler/src/pipeline/execution.rs |
| mcp_interpreter_startup_12s_2026-09-14 | P2 | open | MCP interpreter startup spends roughly 11-13 seconds in eager module loading | src/app/mcp/main.spl |
| mcp_stdio_interpreter_gate_exceeds_cpu_guard_2026-08-10 | P2 | open | MCP stdio interpreter gate exceeds the CPU guard; rt_file_is_char_device unresolved | src/compiler/80.driver/driver_source_pipeline_loading.spl |
| mem_infra_parity_specs_cranelift_arm_demotes_to_interpreter_2026-08-09 | P2 | open | guard/harden backend-parity specs cranelift arm silently demotes to interpreter so cranelift is never measured | test/01_unit/lib/mem_infra/guard_backend_parity_spec.spl |
| ml_kem_postfix_to_equal_chained_call_not_found_2026-07-20 | P2 | open | Postfix .to_equal() matcher is unresolved when the receiver is a chained call | blocking ML-KEM algebraic assertions" |
| mlkem_ntt_simd_public_interface_probe_crashes_not_pass_2026-08-05 | P2 | open | AC-4 SIMD byte-identity probe crashes on reproduction and the named .spl probe file was never created | so the reported PASS is unsupported" |
| native_env_closure_unsupported_methods_2026-07-16 | P2 | open | native-build of a std.env closure fails: array/text methods unsupported in MIR lowering | src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl |
| native_interp_logical_and_or_llc_type_mismatch_2026-07-16 | P2 | open | Interpolating '{a() and b()}' fails llc with a ptr vs i64 type mismatch on strict-llvm | src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl |
| os_crypto_jit_unresolved_symbol_rootcause_2026-07-30 | P2 | open | Any probe against os.crypto.* triggers a module-wide 'unresolved external symbol' JIT fa | src/compiler_rust/compiler/src/codegen/jit.rs |
| os_namespace_uninitialized_array_module_var_not_found_2026-08-02 | P2 | open | Module-level uninitialized array var is unresolvable in the os.* namespace only | src/compiler_rust/compiler/src/interpreter/node_exec.rs |
| parse_family_strips_option_jit_native_2026-08-02 | P2 | open | Re-scoped: JIT/native parse_* yield bare scalar/nil instead of Option::Some/None (value-level wrong answers al | src/compiler_rust/compiler/src/interpreter_method/string.rs |
| prelude_builtins_rebindable_by_transitive_import_2026-08-10 | P2 | open | 50 prelude builtins beyond `exit` remain silently shadowable by a transitive top-level fn | src/compiler_rust/compiler/src/interpreter_call/mod.rs |
| private_symbol_collision_sshd_four_names_2026-07-28 | P2 | open | Private cross-module symbol collision mis-dispatches silently under JIT; C1/C2 not landed | src/compiler/35.semantics/resolve.spl |
| result_struct_payload_pushed_into_struct_array_crashes_2026-10-25 | P2 | open | result struct payload pushed into struct array crashes (workaround registered) | src/compiler/80.driver/cache/cold_hir_semantic_seed_v1.spl |
| riscv64_arch_unit_specs_fail_interpreter_2026-06-06 | P2 | open | RV64 arch unit specs (boot/interrupt/trap_frame/trap_model) fail under interpreter mode | test/01_unit/os/kernel/arch/riscv64_boot_spec.spl |
| riscv_gate_evidence_seed_attributed_bin_release_clobbered_2026-07-27 | P2 | open | Every RISC-V gate result is attributed to bin/release/<triple>/simple which is a Rust seed | not self-hosted" |
| s68_cranelift_interpcall_boxed_result_generic_return_gap_2026-07-18 | P2 | open | Seed cranelift InterpCall returns wrong Object/Enum(Option) values in composite returns | src/compiler_rust/compiler/src/codegen/instr/core.rs |
| scram_sha1_examples_exceed_interpreter_10m_op_budget_2026-08-04 | P2 | open | SCRAM-SHA-1 RFC 5802 spec exceeds the interpreter's 10M-operation budget once PBKDF2 runs | src/compiler_rust/compiler/src/interpreter_state.rs |
| seed_coalesce_stateful_operand_twice_2026_10_12 | P2 | open | Seed coalesce evaluates a stateful optional operand twice in ast_semantic_hash_finish | src/compiler/10.frontend/generated/ast_semantic_value.spl |
| seed_hybrid_jit_spliced_u8_array_boxed_elements_2026_10_19 | P2 | open | Seed hybrid JIT returns [u8] through the interpreter splice with boxed elements; indexing and bulk rt_* calls  | src/compiler_rust/runtime/src/value/utf8_kernels.rs |
| seed_interp_ecs_lower_and_freefn_closure_byref | P2 | open | Seed interpreter cannot lower ECS Entity/ComponentStore<T>; free-fn mutation lost inside | src/os/services/devfs_service.spl |
| seed_interpreter_zeroize_not_guaranteed_2026_10_31 | P2 | open | Seed interpreter cannot guarantee zeroization through a parameter | doc/08_tracking/bug/seed_interpreter_zeroize_not_guaranteed_2026_10_31.md |
| seed_jit_lsu64_load_lowering_forces_interpreter_2026-07-22 | P2 | open | Seed JIT HIR lowering reports Unknown variable lsu64_load for a valid cross-module | src/lib/hardware/rv64gc_rtl/lsu.spl |
| seed_native_project_sqlite_tests_need_external_sqlite_sdk_2026_11_03 | P2 | open | native_project tests need a real external SQLite SDK (sqlite3.h) on Windows; contradicts embedded-SQL policy | src/runtime/runtime_sqlite.c |
| seed_windows_path_identity_errno_discovery_2026_10_06 | P2 | open | keep_nonwindows_errno_directives_out_of_windows_seed_discovery | src/lib/nogc_sync_mut/io/path_identity_abi.spl |
| selfhost_names_with_no_import_path_masked_by_seed_flat_resolution_2026-08-01 | P2 | open | 66 compiler names are declared in one module with no import path on any importer's graph | src/compiler/80.driver/driver_source_loading.spl |
| selfhost_noimport_carveouts_error_panic_blockdsl_nilname_2026-08-01 | P2 | open | `error` and `panic` are not both builtins in the self-hosted front end: both lower to | src/compiler_rust/compiler/src/hir/lower/expr/calls.rs |
| shim_init_keepalive_function_ptr_cast_breaks_interpreter_2026-08-06 | P2 | open | shim_init calls _shim_keepalive whose fn-ptr-to-u64 casts fail: cannot cast function to... | src/os/kernel/abi/syscall_shim.spl |
| spec_imports_declared_nowhere_2026-08-04 | P2 | open | 1003 names imported by 294 spec files are declared nowhere in owned src/ | only warned not" |
| stage2_binary_vulkan_backend_init_segfault_2026-08-09 | P2 | open | Stage2 self-hosted binary SIGSEGVs in VulkanBackend.init while the Rust seed runs the | src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl |
| stage3_unresolved_call_warning_family_2026-08-07 | P2 | open | run_check unresolved because Rust seed source collector hardcodes a *check.spl exclusion | src/app/cli/check.spl |
| stress_f03_manycall_sum_2026-07-17 | P2 | open | 300-call-chain sum diverges on the interpreter path only; compiled/JIT already correct | src/compiler_rust/compiler/src/interpreter_call/mod.rs |
| string_interpolation_silently_evaluates_literal_braces_2026-07-28 | P2 | open | Interpolation evaluates literal brace content with no guard or diagnostic | src/compiler_rust/parser/src/lexer/strings.rs |
| text_len_codepoint_switch_2026-11-03 | P2 | open | Held until phase 3: switch text.len() from bytes to code points per ADR-005; byte_len()/char_count() explicit  | src/compiler_rust/compiler/src/interpreter/expr/collections.rs |
| vulkan_8k_jit_retained_host_buf_sample_crash_2026-08-12 | P2 | open | Strict-JIT 8K retained host-buffer sample crashes on a retained u32 array read | test/fixtures/jit_class_u32_array_retained_read/main.spl |
| web_style_producer_4s_per_node_interpreted_lane_2026-07-29 | P2 | open | Web style producer costs ~4s per DOM node on the interpreted lane | blocking the showcase" |
| wildcard_import_c_backend_stubs_function_to_int_2026-07-30 | P2 | open | use compiler.backend.backend.c_backend_stubs.* poisons the session with cannot convert | src/compiler_rust/compiler/src/value_impl.rs |
| x25519mlkem768_jit_fallback_interpreted_execution_2026-08-05 | P2 | open | All X25519MLKEM768 hot-path operations run interpreted; JIT lost on the entire hybrid-KEM | src/os/crypto/x25519_mlkem768/execution_policy.spl |
| linux_vulkan_renderdoc_reason_forwarding_spec_daemon_timeout_2026-06-28 | P3 | fix-implemented-verification-pending | STALE ASSERTION FIXED: behavioral precedence covered; timeout cause unproven and pure-Simple Linux daemon veri | test/03_system/check/linux_vulkan_renderdoc_reason_forwarding_spec.spl |
| on_is_an_undocumented_reserved_word_2026-08-02 | P3 | fix-implemented-verification-pending | val on = ... fails to parse because 'on' is a hard keyword | with an error that never nam" |
| spec_cross_module_eval_warnings_not_observed_2026-08-05 | P3 | fix-implemented-verification-pending | A spec importing eval_tables and eval separately reads eval_warnings back as 0 after a | src/compiler/10.frontend/core/interpreter/eval.spl |
| coverage_probe_plan_skips_struct_method_decisions_2026-08-15 | P3 | open | Coverage probe plan skips struct-method decisions; SIMPLE_COVERAGE on run writes nothing | src/compiler_rust/compiler/src/mir/lower/lowering_coverage.rs |
| executable_checker_failed_only_retry_peak_rss_2026-08-02 | P3 | open | Failed-only executable-checker retry peaked at 40.6 GiB RSS across four workers | src/lib/nogc_sync_mut/js/engine/interpreter_native.spl |
| gate_oracle_soundness_census_2026-08-11 | P3 | open | census of check scripts whose oracle is exit-code-only | so a silent no-op run reads as a" |
| iterator_collect_generic_restoration_2026-07-17 | P3 | open | Iterator.collect loses its generic type parameter and needs restoration across the three vec types | src/compiler_rust/lib/std/src/core/list.spl |
| jit_dispatch_worklist_2026-07-29 | P3 | open | JIT builtin-method dispatch worklist: text.reverse arm is a no-op | rt_string_reverse does not exist" |
| jit_lowering_clamp_f_engine_color_2026-07-02 | P3 | open | JIT lowering cannot resolve a nested fn inside an impl method (Unknown variable: clamp_f) | src/lib/common/engine/color.spl |
| js_subset_interpreter_limitations_2026-06-30 | P3 | open | Browser-session JS subset interpreter gaps worked around in the ES-module transform instead of the engine | src/lib/gc_async_mut/web/browser_session_modules.spl |
| llvm_backend_yield_silent_noop_2026-07-19 | P3 | open | LLVM codegen matches MirInst::Yield to an empty arm | emitting no code for a yield" |
| mem_guard_owner_attribution_trap_report_missing_2026-08-05 | P3 | open | M2 guard-page SIGSEGV trap produces no owner-attribution report on either backend | src/compiler_rust/compiler/src/interpreter_extern/mem_guard.rs |
| native_jit_crypto_tls13_pbkdf2_no_extern_c_implementation | P3 | open | TLS1.3/PBKDF2/Ed25519 runtime symbols in the ABI list have no extern C impl | src/compiler_rust/common/src/runtime_symbols.rs |
| native_object_cache_whole_build_fingerprint_granularity_2026-08-02 | P3 | open | Native object cache invalidates the whole build when any compiler byte changes | src/compiler_rust/driver/src/cli/native_build.rs |
| notebook_cuda_exec_jit_lane_not_implemented_2026-08-08 | P3 | open | CudaExec cannot back jit(remote(cuda(...))) cells: no per-cell PTX compile path exists | src/lib/nogc_sync_mut/notebook/cuda_exec.spl |
| screenshot_sffi_api_declared_but_never_implemented_2026-08-04 | P3 | open | No rt_screenshot_* implementation exists in the C runtime | so native/baremetal links canno" |
| seed_enum_variant_arity_unchecked_2026-11-01 | P3 | open | Rust seed accepts enum-variant construction with extra payloads (5 for a 4-field variant) instead of rejecting | src/compiler_rust |
| smux_pty_input_throughput_wide_line_2026-11-04 | P3 | open | Windows smux pane input delivers a ~300 char command line in ~100 s (~5 chars/s | super-linear) under the interpreter lane |

## DevHub

| id | sev | status | title | file |
|-|-|-|-|-|
| os_crypto_native_failures_2026_10_31 | P1 | fix-implemented-verification-pending | OS crypto AES-128 GCM and X25519 fail natively and AES-256 GCM cannot link | doc/08_tracking/bug/os_crypto_native_failures_2026_10_31.md |
| tcp_accept_timeout_nonblocking_stream_windows_2026-10-31 | P2 | fix-implemented-verification-pending | TCP accept with timeout returns a non-blocking stream on Windows | doc/08_tracking/bug/tcp_accept_timeout_nonblocking_stream_windows_2026-10-31.md |
| seed_interpreter_zeroize_not_guaranteed_2026_10_31 | P2 | open | Seed interpreter cannot guarantee zeroization through a parameter | doc/08_tracking/bug/seed_interpreter_zeroize_not_guaranteed_2026_10_31.md |

## Caret suite / smux

| id | sev | status | title | file |
|-|-|-|-|-|
| caret_cs_host_provider_exports_2026_10_11 | P1 | fix-implemented-verification-pending | CS host provider aliases and missing sleep owner | src/lib/nogc_sync_mut/io.spl |
| mcp_native_array_extend_2026_10_12 | P1 | fix-implemented-verification-pending | Native array extend unresolved in MCP | src/app/mcp/main_lazy_caret_tools.spl |
| llm_caret_http_attempt_timeout | P2 | fix-implemented-verification-pending | http_request_raw has no timeout parameter so with_retry cannot cancel a blocked transport; FIXED a62f411a3c2 ( | spec llm_caret_attempt_timeout_spec.spl needs CARET_TIMEOUT_TEST_URL" |
| smux_owner_jit_file_read_empty_2026-11-04 | P2 | fix-implemented-verification-pending | ROOT CAUSE (not rt_array_concat nil): if-val binding of a [u8]? extern result was untyped so joined.len() was  | stale deployed seed still affected. Verify: run bin/simple on test/01_unit/lib/text/text_bytes_jit_concat_spec.spl and a main() printing text_bytes_concat_checked result after seed redeploy. Windows smux owner and CLI clients fail under the default JIT lane: std file_read returns empty (rt_array_concat nil) |
| caret_closure_enum_payload_binding_collection_gaps_2026_11_03 | P2 | open | Caret closure enum payload | local binding and collection method diagnostics (split from leaf provider gaps)" |
| interp_flat_fn_table_load_config_shadowed_2026-11-03 | P2 | open | Interpreter flat function table lets a same-named load_config from another transitively loaded module shadow a | src/app/llm_caret/config.spl |
| llm_caret_compiled_carrier_build_latency_2026-08-02 | P2 | open | LLM Caret compiled carrier link fails on unresolved stdlib symbols (trim/starts_with/unwrap_err) | src/app/llm_caret/messaging/hook_worker.spl |
| llm_caret_native_closure_admission_2026-08-11 | P2 | open | LLM Caret native closure admission fails on missing artifacts and unresolved Caret ABI symbols; depends on nat | scripts/check/check-llm-caret-native-closure.shs |
| native_mir_lambda_and_enum_eq_block_caret_cs_2026_10_19 | P2 | open | Native MIR for llm_caret cs_main: 21 lambdas hit E-MIR-EXPR-Lambda (closure conversion not run) | enum == lowered as missing struct __eq__ |
| bin_caret_dropped_native_only_launcher_policy_2026-09-06 | P3 | open | bin/caret dropped its native-only launcher policy (2 of 3 committed spec examples fail; deliberately not fixed | bin/caret |
| llm_caret_codex_app_server_piped_stdio_2026-08-02 | P3 | open | codex app-server --listen stdio:// spawned via app.io piped façade dies before first response | src/app/llm_caret/messaging/cli.spl |
| smux_pty_input_throughput_wide_line_2026-11-04 | P3 | open | Windows smux pane input delivers a ~300 char command line in ~100 s (~5 chars/s | super-linear) under the interpreter lane |

## Stdlib: src/lib/common

| id | sev | status | title | file |
|-|-|-|-|-|
| mir_chained_named_receiver_owner_2026_10_10 | P1 | fix-implemented-verification-pending | MIR loses ByteSpan owner on chained slice equals call | src/lib/common/bytes/span.spl |
| tree_wipe_module_damage_census_2026-08-04 | P1 | open | tree-wipe left 39 truncated modules; only 3 restored | the rest still short of their" |
| mir_text_bytes_unresolved_inferred_trim_receiver_2026-10-23 | P2 | fix-implemented-verification-pending | mir text bytes unresolved inferred trim receiver (workaround registered) | src/lib/common/sdn/parser.spl |
| divergence_byte_char_find_option_sweep_2026-08-01 | P2 | fixing | find/rfind/index_of return a raw i64 -1 sentinel but are consumed as Option across src/** | src/lib/common/text.spl |
| zstd_brotli_encoders_are_stored_only_2026-08-17 | P2 | fixing | zstd and brotli encoders emit container-only output LARGER than input (310/304 bytes for | src/lib/common/compress/zstd.spl |
| core_purity_runtime_split_blocked_native_const_resolution_2026-07-08 | P2 | open | Cross-module NATIVE_* constant resolution blocks the runtime.spl core-purity split | src/lib/common/js/engine/runtime.spl |
| native_entry_closure_common_import_type_loss_2026-07-27 | P2 | open | Entry-closure build loses declared types on symbols imported from common modules (draw_ir into draw_ir_adv) | src/lib/common/ui/draw_ir.spl |
| native_future_receiver_typeparam_2026_10_18 | P2 | open | Explicit real Future construction retains the concrete Poll and Result payload owners after static-call receiv | src/lib/common/io/read_only_file_view.spl |
| native_scalar_spill_clobber_loop_intervening_calls_2026-07-20 | P2 | open | Freestanding native: outer-scope scalar vals read corrupted in a while loop with calls | src/lib/common/ui/window_scene_draw_ir.spl |
| os_crypto_jit_unresolved_symbol_rootcause_2026-07-30 | P2 | open | Any probe against os.crypto.* triggers a module-wide 'unresolved external symbol' JIT fa | src/compiler_rust/compiler/src/codegen/jit.rs |
| sfnt_fvar_option_match_nil_baremetal_2026-08-04 | P2 | open | val-assigned Option match yields nil on freestanding native lane; table.offset faults | src/lib/common/encoding/sfnt.spl |
| svmg_device_arena_code_coresidency_diverges_from_ref_vm_2026-08-07 | P2 | open | Device single-buffer code/data co-residency diverges from ref_vm's separate code array | src/lib/common/svmg/ref_vm.spl |
| theme_ipc_k2_review_hard_stop_2026-07-27 | P2 | open | Theme IPC K2 stays fail-closed: no accepted design | K2 transport unimplemented" |
| wine_vm_module_family_destroyed_by_tree_wipe_2026-08-04 | P2 | open | wine_vm module family lost to a tree wipe and partly rebuilt by guess | so contents are" |
| widget_draw_ir_panel_title_not_rendered_2026-08-09 | P3 | fix-implemented-verification-pending | Panel titles are never emitted by the pixel Draw-IR pipeline | so titled panels look" |
| arity_census_reaudit_declaration_side_defects_2026-08-04 | P3 | open | Arity census re-audit: declaration side is not ground truth | remainder filed" |
| jit_lowering_clamp_f_engine_color_2026-07-02 | P3 | open | JIT lowering cannot resolve a nested fn inside an impl method (Unknown variable: clamp_f) | src/lib/common/engine/color.spl |
| pure_simple_ctype_perf_gap_2026-05-18 | P3 | open | Pure-Simple ctype predicates run 0.07x-0.46x of C under Cranelift with no inlining | src/lib/common/ctype.spl |
| return_type_result_mismatch_class_audit_2026-08-08 | P3 | open | Non-Result declared return types whose bodies return Ok()/Err() remain in owned src after partial fix | src/lib/common/validation.spl |
| theme_snapshot_catalog_review_hard_stop_2026-07-27 | P3 | open | theme snapshot catalog design fail-closed after three exhausted review cycles | src/lib/common/ui/theme_package_wire.spl |

## Stdlib: src/lib/nogc_sync_mut

| id | sev | status | title | file |
|-|-|-|-|-|
| caret_cs_host_provider_exports_2026_10_11 | P1 | fix-implemented-verification-pending | CS host provider aliases and missing sleep owner | src/lib/nogc_sync_mut/io.spl |
| hir_tui_builtin_len_resolution_2026_10_10 | P1 | fix-implemented-verification-pending | CS native closure cannot resolve TUI builtin len | src/lib/nogc_sync_mut/tui/widgets/input.spl |
| native_huffman_untyped_return_guard_2026_10_11 | P1 | fix-implemented-verification-pending | Native Huffman untyped returns block normal object generation | src/lib/nogc_sync_mut/compression/gzip/huffman.spl |
| test_runner_ulimit_caps_unusable_on_macos_2026-09-05 | P1 | fix-implemented-verification-pending | macOS safe-mode per-UID process cap starves child forks; source policy fixed and Phase 2 test verification pen | src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl |
| codegen_isa_sffi_text_abi_misexpansion_2026_10_22 | P1 | open | Cranelift ISA/config SFFI wrappers hand-expand text with rt_string_data/rt_string_len; seed-built binaries re- | src/lib/nogc_sync_mut/sffi/codegen.spl |
| convnodes_retained_file_result_tuple_u64_2026_10_25 | P2 | fix-implemented-verification-pending | retained_file result tuple u64 lowering | src/lib/nogc_sync_mut/io/retained_file.spl |
| gpu_ffi_loader_probes_linux_sonames_on_macos_2026_09_19 | P2 | fix-implemented-verification-pending | gpu_lib_candidates probes Linux sonames on macOS (SIMPLE_OS_TYPE never set) and spl_dlopen raises where DynLib | src/lib/nogc_sync_mut/gpu/engine2d/ffi_dispatch.spl |
| gzip_optional_collection_payload_provenance_2026_10_21 | P2 | fix-implemented-verification-pending | gzip optional collection payload provenance 2026 10 21 | src/lib/nogc_sync_mut/compression/gzip/compress.spl |
| gzip_untyped_reader_byte_array_text_dispatch_2026_10_21 | P2 | fix-implemented-verification-pending | gzip untyped reader byte array text dispatch 2026 10 21 | src/lib/nogc_sync_mut/compression/gzip/header.spl |
| llm_caret_http_attempt_timeout | P2 | fix-implemented-verification-pending | http_request_raw has no timeout parameter so with_retry cannot cancel a blocked transport; FIXED a62f411a3c2 ( | spec llm_caret_attempt_timeout_spec.spl needs CARET_TIMEOUT_TEST_URL" |
| map_insert_if_absent_missing_and_map_new_resolves_to_dict_2026-07-20 | P2 | fix-implemented-verification-pending | [insert_if_absent fixed map.spl:325; bare Map.new shadowing unverified] Map.new() resolves to a plain dict rat | src/lib/nogc_sync_mut/src/map.spl |
| native_tuple_spill_clobber_across_call_2026-07-19 | P2 | fix-implemented-verification-pending | Native tuple stack spill clobbered by intervening method call; derefs ASCII text as poin | src/lib/nogc_sync_mut/sffi/spl_fonts.spl |
| stage2_matrix_cg_modules_managed_tool_projection_invalid_2026_10_20 | P2 | fix-implemented-verification-pending | Stage 2 matrix src/app/_cg modules: managed tool projection role/path/digest invalid | src/lib/nogc_sync_mut/io/native_tool_authority_v1.spl |
| x25519mlkem768_neon_rvv_ntt_not_implemented_2026-08-08 | P2 | fix-implemented-verification-pending | NEON and RVV ML-KEM NTT candidates are declared but only the AVX2 i32x8 butterfly exists | src/lib/nogc_sync_mut/simd.spl |
| after_each_captured_var_compound_assignment_lost_2026-08-04 | P2 | fixing | Write in after_each that reads the captured var is lost; constant write is not | src/lib/nogc_sync_mut/spec.spl |
| cover_gate_fails_every_system_test_without_running_one_2026-08-04 | P2 | fixing | # @cover gate marks 227 system tests FAILED without running one | src/lib/nogc_sync_mut/test_runner/test_runner_files.spl |
| lsp_code_action_edit_emit_parse_mismatch_2026-06-16 | P2 | fixing | LSP code-action edits never apply: emitter output does not round-trip through the edit parser | src/lib/nogc_sync_mut/lsp/lsp_handlers.spl |
| seed_main_entry_file_text_allocation_failed_2026-11-01 | P2 | fixing | Seed runtime: file reads inside an auto-invoked fn main fail with file text input allocation failed (silent em | src/lib/nogc_sync_mut/io/file_text_session.spl |
| a174_aggregate_receiver_provenance_2026_10_16 | P2 | open | retain-explicit-aggregate-receiver-type | src/lib/nogc_sync_mut/database/core.spl |
| bootstrap-builder-owner-native-string-methods-2026-09-30 | P2 | open | bootstrap-builder-owner-native-string-methods-2026-09-30 | src/lib/nogc_sync_mut/io/windows_process_owner.spl |
| hir_generic_enum_self_match_2026-10-23 | P2 | open | hir generic enum self match (workaround registered) | src/lib/nogc_sync_mut/failsafe/core.spl |
| interpreter_bdd_missing_structured_test_evidence_2026-07-19 | P2 | open | Pure-Simple BDD consumer still cannot authenticate interpreter results via --assert-ran | src/lib/nogc_sync_mut/spec.spl |
| js_engine_es2015_parser_gaps_2026-07-05 | P2 | open | JS engine es2015 conformance: 13 of 38 cases fail on parser gaps | src/lib/nogc_sync_mut/js/engine/parser.spl |
| js_engine_missing_builtins_regex_promise_prototype_2026-07-11 | P2 | open | JS engine String.replace with a regex is a silent no-op | src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl |
| js_vm_dom_bridge_retention_quadratic_2026-07-30 | P2 | open | JS VM DOM bridge retention is frame-linear and property scan is quadratic | src/lib/nogc_sync_mut/js/engine/vm_object_store.spl |
| layoutglyph_struct_array_i64_field_tag_shift_readback_2026-07-20 | P2 | open | LayoutGlyph struct-in-array i64 fields read back tag-shifted on freestanding native lane | src/lib/nogc_sync_mut/text_layout/font_renderer.spl |
| native_build_cross_module_result_payload_struct_name_collision_2026-08-09 | P2 | open | Cross-module Result<T,E> payload struct-name recovery collides or misses across modules (6th layer still open) | src/lib/nogc_sync_mut/io/file.spl |
| native_build_nested_replace_method_resolution_2026-07-26 | P2 | open | Stage4 compiler cannot resolve .replace(...) on an erased receiver in nested call context | src/lib/nogc_sync_mut/database/pure_sql/_PureDatabase/row_value_helpers.spl |
| native_primitive_to_i64_ufcs_collision_2026-07-24 | P2 | open | Primitive to_i64 collides with an imported custom to_i64 method under native lowering | src/lib/nogc_sync_mut/failsafe/core.spl |
| native_tuple_array_local_text_provenance_2026-10-30 | P2 | open | Implicit text locals from tuple-array elements lose native text representation | src/lib/nogc_sync_mut/http/url.spl |
| native_u8_array_ne_compares_reference_2026_10_25 | P2 | open | native [u8] != compares references; element-wise compare | src/lib/nogc_sync_mut/io/retained_file.spl |
| p4p2_cross_module_generic_free_fn_not_instantiated_2026-10-20 | P2 | open | phase-2 producer emits no object symbol for generic free fns and leaves cross-module calls on the unspecialize | src/lib/nogc_sync_mut/concurrent/mutex.spl |
| puresql_native_mir_failures_2026_10_25 | P2 | open | pure_sql native MIR failures worked around at 9 sites | src/lib/nogc_sync_mut/database/pure_sql/_PureDatabase/pure_database.spl |
| seed_windows_path_identity_errno_discovery_2026_10_06 | P2 | open | keep_nonwindows_errno_directives_out_of_windows_seed_discovery | src/lib/nogc_sync_mut/io/path_identity_abi.spl |
| simpleos_server_credential_zeroization_gap_2026-08-14 | P2 | open | Server credential read into immutable [u8]/text has no compiler-resistant zeroization on | src/lib/nogc_sync_mut/database/server/capability.spl |
| vulkan_ffi_ledger_lost_under_spec_harness_2026-08-09 | P2 | open | VulkanFfi rejection ledger never accumulates under the spec harness but works under `run` | src/lib/nogc_sync_mut/gpu/engine2d/ffi_vulkan.spl |
| credential_v1_records_have_no_upgrade_on_write_owner_2026-08-08 | P3 | open | v1 credential records never rewritten; no config writer owns the upgrade | src/lib/nogc_sync_mut/terminal/credential/config_parser.spl |
| cross_module_collisions_debugconfig_and_pub_shell_entangled_2026-08-15 | P3 | open | DebugConfig and public shell collisions too entangled to rename | src/lib/nogc_sync_mut/io/process_ops.spl |
| cross_module_public_symbol_collisions_2026-08-16 | P3 | open | Cross-module public symbol collisions (bootstrap warnings | wrong-dispatch risk)" |
| executable_checker_failed_only_retry_peak_rss_2026-08-02 | P3 | open | Failed-only executable-checker retry peaked at 40.6 GiB RSS across four workers | src/lib/nogc_sync_mut/js/engine/interpreter_native.spl |
| image_wrapper_close_needs_live_handle_fixture_2026-08-07 | P3 | open | Image/FileLock wrapper double-close on a genuinely-acquired handle has no test fixture | src/lib/nogc_sync_mut/io/image_sffi.spl |
| network_coverage_illusion_and_spec_tree_duplication_2026-08-05 | P3 | open | Network e2e specs assert on source-text substrings | not sockets; spec tree duplicated 5," |
| notebook_cuda_exec_jit_lane_not_implemented_2026-08-08 | P3 | open | CudaExec cannot back jit(remote(cuda(...))) cells: no per-cell PTX compile path exists | src/lib/nogc_sync_mut/notebook/cuda_exec.spl |
| prevention_mock_deferred_arming_impossible_2026-08-07 | P3 | open | std.spec prevent/prevent_at_most cannot defer arming; no module state across it examples | src/lib/nogc_sync_mut/spec.spl |
| sspec_no_dir_wide_prevention_scope_2026-08-07 | P3 | open | SSpec has no per-directory config hook so directory-wide prevention-mock scope is | src/lib/nogc_sync_mut/spec.spl |

## Stdlib: src/lib/nogc_async_mut

| id | sev | status | title | file |
|-|-|-|-|-|
| starfive_check_deployed_simple_segv_2026-08-15 | P1 | fix-implemented-verification-pending | Deployed simple check segfaults on StarFive implementation files | src/lib/nogc_async_mut/fs_driver/ramfs.spl |
| optional_try_nominal_owner_missing_2026_10_21 | P2 | fix-implemented-verification-pending | Keep the declared table owner until rebuilt Try metadata recovery is qualified | src/lib/nogc_async_mut/database/bug.spl |
| gpu_compute_offload_not_wired_to_sffi_launch_2026-07-06 | P2 | fixing | std.compute offload always computes on CPU and only reports GPU provenance from an env | src/lib/nogc_async_mut/compute/backend_dispatch.spl |
| interpreter_struct_in_dict_with_closure_field_reads_nil_2026-08-10 | P2 | fixing | Struct stored in a Dict reads back nil on a field that has a closure-typed sibling field | src/lib/nogc_async_mut/actors/actor.spl |
| async_spec_promise_future_anon_tuple_state_inconsistency_2026-07-20 | P2 | open | Destructured Future from anon-tuple Promise.new() gives inconsistent poll() results | src/lib/nogc_async_mut/async/task.spl |
| generic_enum_pattern_self_subject_hir_2026_10_22 | P2 | open | selfhosted_hir_rejects_generic_enum_patterns_on_self_field_subjects_but_accepts_parameter_subjects | src/lib/nogc_async_mut/async/poll.spl |
| native_mir_lambda_and_enum_eq_block_caret_cs_2026_10_19 | P2 | open | Native MIR for llm_caret cs_main: 21 lambdas hit E-MIR-EXPR-Lambda (closure conversion not run) | enum == lowered as missing struct __eq__ |
| vulkan_icd_virtio_and_gpu_probe_report_no_real_device_enumeration_2026-08-11 | P2 | open | vulkan_icd_virtio and gpu_vendor_probe report no real device enumeration data | src/lib/nogc_async_mut/gpu/vulkan_icd_virtio.spl |

## SOSIX

| id | sev | status | title | file |
|-|-|-|-|-|
| mission_critical_infra_hardening_v2_wave1_red_2026-08-11 | P2 | open | Mission-Critical Infra Hardening V2 Wave 1 is RED across compiler_admission | draw_ir arena v3 and sosix certified_manifest specs" |
| os_namespace_uninitialized_array_module_var_not_found_2026-08-02 | P2 | open | Module-level uninitialized array var is unresolvable in the os.* namespace only | src/compiler_rust/compiler/src/interpreter/node_exec.rs |
| sosix_qemu_matrix_remaining_owners_2026-08-14 | P2 | open | RV64/x86_32/ARM32 SOSIX QEMU rows lack an admitted Stage-4 runner so no exit-37 reap | scripts/check/check-sosix-qemu-matrix.shs |
| sosix_qemu_v2_admission_record_hash_binding_2026-08-16 | P2 | open | v2 matrix manifest recorded admission_record_path_b64 without a sha256 binding the | src/os/sosix/qemu_evidence/trusted_importer.spl |
