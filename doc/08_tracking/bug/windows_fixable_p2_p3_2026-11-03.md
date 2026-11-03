# Windows-fixable open P2/P3 bugs (2026-11-03)

Snapshot of open P2 and P3 bugs in `doc/08_tracking/bug/bug_db.sdn` on `release/1.0.0` that look fixable on Windows:
not tied to another host (macOS, arm64, riscv, FreeBSD, SimpleOS/QEMU, bare-metal, GPU) and not needing a stage2/3,
native-build, codegen or MIR/HIR producer run to reproduce. Classification is by keywords in the bug id and file path,
so treat it as a work-planning list: confirm each bug against current code before fixing.

| Priority | Group | Count |
|---|---|---|
| P2 | Compiler | 46 |
| P2 | Lib / runtime | 45 |
| P2 | Interpreter / JIT | 44 |
| P2 | Seed | 12 |
| P2 | Tester | 8 |
| P2 | Other (apps, tools) | 67 |
| P3 | Compiler | 47 |
| P3 | Lib / runtime | 78 |
| P3 | Interpreter / JIT | 66 |
| P3 | Seed | 35 |
| P3 | Tester | 18 |
| P3 | Other (apps, tools) | 318 |
| **Total** | | **784** |

## P2

### Compiler

| Bug | File | Summary |
|---|---|---|
| `BUG-PHASE1-BDD-NEGATED-MATCHERS-20261011` | `test/01_unit/compiler/negated_matcher_consumer_predicate_spec.spl` | direct grammar regression remains unchanged. |
| `a174_enum_scalar_codec_wire_boundary_2026_10_16` | `src/app/compiler_schema/codec_gen.spl` | generate-typed-enum-prototypes-and-schema-owned-wire-nil-slots |
| `a174_nominal_enum_operator_resolution_2026_10_16` | `src/compiler/80.driver/smf/runtime_std_package_membership_v1.spl` | compare-exhaustive-canonical-section-names |
| `a174_struct_nil_comparison_dispatch_2026_10_16` | `src/app/compiler_schema/codec_gen.spl` | old-producer-record-presence-dispatch |
| `armv7_windows_backend_plugin_target_rejected_2026_10_26` | `src/compiler/70.backend/backend_plugin/builtin_adapter.spl` | armv7-w64-mingw32 native-build fails: BACKEND_SESSION_AUTHORITY load rejected: BACKEND_PLUGIN_TARGET |
| `bare_name_registry_collision_trigger_conditions_2026-07-30` | `src/compiler/10.frontend/core/types.spl` | Bare-name type registry collision real in situ but trigger conditions unreproduced |
| `bare_result_return_type_any_payload_2026-10-24` | `src/compiler/70.backend/linker/linker_wrapper_helpers.spl` | bare result return type any payload (workaround registered) |
| `borrow_check_spurious_errors_refuted_and_two_fail_opens_2026-08-08` | `src/compiler/55.borrow/borrow_check/nll.spl` | Borrow-check driver fail-opens (primary spurious-error claim refuted) |
| `builtin_dict_set_silent_insert_audit_2026-07-31` | `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl` | Builtin Dict .set() silently fails to insert when the receiver is not scope-resolved to a  |
| `c_parser_library_specced_but_never_implemented_2026-08-04` | `test/03_system/compiler/c_parser_spec.spl` | src/lib/common/c_parser/ specced by 56 system-test examples but never existed |
| `coherence_optional_payload_owner_2026_10_19` | `src/compiler/25.traits/trait_coherence.spl` | retain optional text metadata across Some/nil merge before enum construction |
| `compiler_test_sweep_residuals_2026-08-16` | `src/compiler/10.frontend/core/parser.spl` | Compiler test sweep residuals: 8 interpreter gaps plus backend integration fails |
| `dict_index_coalesce_text_decoded_before_nil_test_2026-10-25` | `src/compiler/80.driver/driver_phase_gates.spl` | dict index coalesce text decoded before nil test (workaround registered) |
| `duplicate_backend_types_terminal_declarations` | `src/compiler/70.backend/backend_types.spl` | Enums declared in multiple terminal modules with divergent variant orders are undetected |
| `entry_closure_runs_global_stdlib_pass_regardless_of_imports_2026-08-08` | `src/compiler/80.driver/driver.spl` | native-build --entry-closure runs a fixed global stdlib pass no matter what the program... |
| `enum_named_payload_default_dropped_2026_10_16` | `test/fixtures/compiler/archive_enum_declaration_prescan_repro.spl` | exercise the rich HIR/artifact boundary until flat enum defaults are transported. |
| `enum_payload_type_mismatch_tuple_pattern_binders_2026-10-24` | `src/compiler/30.types/type_infer/inference_control.spl` | enum payload type mismatch tuple pattern binders (workaround registered) |
| `enum_payload_type_mismatch_untyped_map_2026-10-24` | `src/compiler/30.types/type_infer/traits.spl` | enum payload type mismatch untyped map (workaround registered) |
| `float_literal_pattern_lowers_to_wildcard_2026-11-02` | `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl` | Float literal match patterns become wildcards |
| `for_in_dict_values_i64_2026-10-24` | `src/plugins/backend_vhdl/vhdl/vhdl_call_lowering.spl` | for-in over Dict.values() lowers with I64 collection type |
| `for_in_unresolved_if_match_route_type_2026-10-24` | `src/compiler/80.driver/driver_source_pipeline_loading.spl` | for in unresolved if match route type (workaround registered) |
| `if_expression_text_result_erased_to_i64_2026-10-25` | `src/compiler/70.backend/backend/runtime_compiler.spl` | if expression text result erased to i64 (workaround registered) |
| `indcall_try_then_member_2026_10_25` | `src/compiler/70.backend/linker/elf/archive_file.spl` | f(x)?.m() lexes as safe-navigation; try parenthesized |
| `item5_backend_error_opaque_enum_2026_10_14` | `src/compiler/70.backend/backend_plugin/session_authority_v2.spl` | Backend AOT diagnostics discard structured error details |
| `js_engine_es2015_parser_gaps_2026-07-05` | `src/lib/nogc_sync_mut/js/engine/parser.spl` | JS engine es2015 conformance: 13 of 38 cases fail on parser gaps |
| `lexer_imported_instance_methods_2026_10_06` | `src/compiler/10.frontend/core/lexer_struct.spl` | lexer imported instance methods 2026 10 06 |
| `lint_single_file_superlinear_timeout_on_line_count_2026-08-06` | `120-line file ~119s"` | bin/simple lint cost is superlinear in line count (~3.3-4.0s per fn decl) |
| `match_variant_pattern_shadowed_by_struct_name_2026-10-24` | `src/compiler/10.frontend/desugar/poll_generator.spl` | match variant pattern shadowed by struct name (workaround registered) |
| `mingw_liboldnames_msvc_abi_input_2026-11-02` | `test/01_unit/compiler/linker/windows_mingw_no_oldnames_spec.spl` | mingw link undefined unlink/close/open/read/write from /DEFAULTLIB:oldnames.lib in MSVC-ABI inputs; build the  |
| `module_namespace_member_call_in_spec_it_block_2026-07-27` | `src/compiler/10.frontend/core/parser.spl` | Module-namespace member call fails inside an sspec it block due to implicit-self injection in it-block closure |
| `option_generic_inner_collapses_below_named_base_2026_10_20` | `doc/08_tracking/bug/option_generic_inner_collapses_below_named_base_2026-10-20.md` | Option structured inner types lose generic payload |
| `optional_text_unwrap_truncates_at_nul_2026-10-25` | `src/app/compiler_entrypoint/inventory_scratch.spl` | optional text unwrap truncates at nul (workaround registered) |
| `p4p2_cross_module_generic_free_fn_not_instantiated_2026-10-20` | `src/lib/nogc_sync_mut/concurrent/mutex.spl` | phase-2 producer emits no object symbol for generic free fns and leaves cross-module calls on the unspecialize |
| `p4p2_flat_parser_noinit_module_var_struct_and_fn_types_2026-10-20` | `src/os/kernel/interrupts/idt.spl` | Self-hosted flat parser synthesizes a zero default only for scalar-element fixed arrays; struct/fn-typed modul |
| `private_symbol_collision_sshd_four_names_2026-07-28` | `src/compiler/35.semantics/resolve.spl` | Private cross-module symbol collision mis-dispatches silently under JIT; C1/C2 not landed |
| `pure_simple_nested_extern_registration_2026_10_12` | `src/compiler/00.common/parallel.spl` | Pure-Simple compiler does not register a function-nested extern declaration |
| `readme_arrow_match_arm_syntax_does_not_parse_2026-09-19` | `and the parser rejects them"` | BUG: README documents `/ Pattern -> expr` match arms as ""preferred" |
| `resource_borrow_pinning_not_enforced_2026-08-07` | `never borrows_of` | borrow_graph.record_move checks only moved_now |
| `resource_decl_and_sffi_attribute_not_parsed_2026-08-07` | `test/01_unit/compiler/resource/resource_sffi_pilot_spec.spl` | resource_sffi_pilot_spec stays RED for a structural reason after WP-A landed the |
| `scv_compile_event_refresh_lock_serializes_builds_2026-11-02` | `300s) around both reads and writes` | compiler inventory refresh takes one repo-global file_lock build/scv/compile-events/refresh.lock (src/app/comp |
| `simple_check_diagnostics_contract_raw_parser_error_not_stable_format_2026-07-20` | `src/app/check/main.spl` | simple check prints raw legacy parser text instead of error[Exxxx]; all 10 contract exa... |
| `text_method_arg_copied_through_extern_abi_per_call_2026-10-25` | `src/compiler/80.driver/driver_entry_closure_core.spl` | text method arg copied through extern abi per call (workaround registered) |
| `tldr_future_static_owner_typeparam_2026_10_25` | `src/compiler/80.driver/cache/reader/tldr_table_v1.spl` | tldr future static owner typeparam (workaround registered) |
| `trait_default_inherent_override_duplicate_symbol_2026-10-24` | `src/compiler/70.backend/backend/cranelift_type_mapper.spl` | trait default inherent override emits duplicate symbol |
| `type_alias_static_dispatch_unresolved_2026-08-04` | `src/compiler/35.semantics/lint/semantic_api/alias_registry.spl` | `type X = Y` does not resolve as a static-call receiver — X.new() sees nil |
| `vhdl_design_catalog_dict_to_i64_cast_2026-07-30` | `test/01_unit/compiler/backend/vhdl_design_catalog_spec.spl` | A second pre-existing defect under the dict->i64 cast remains open after the cast fix |

### Lib / runtime

| Bug | File | Summary |
|---|---|---|
| `a174_aggregate_receiver_provenance_2026_10_16` | `src/lib/nogc_sync_mut/database/core.spl` | retain-explicit-aggregate-receiver-type |
| `after_each_captured_var_compound_assignment_lost_2026-08-04` | `src/lib/nogc_sync_mut/spec.spl` | Write in after_each that reads the captured var is lost; constant write is not |
| `array_get_contract_drift_crypto_2026-10-18` | `test/01_unit/os/crypto/curve25519_bigint_nested_return_spec.spl` | use-proven-indexing-until-get-contract-is-resolved |
| `async_spec_promise_future_anon_tuple_state_inconsistency_2026-07-20` | `src/lib/nogc_async_mut/async/task.spl` | Destructured Future from anon-tuple Promise.new() gives inconsistent poll() results |
| `browser_dom_event_object_gc_retention_2026-07-31` | `src/lib/gc_async_mut/gpu/browser_engine/script/event_api.spl` | Browser DOM event object GC reachability reclamation not implemented |
| `browser_engine_css_contain_size_unimplemented_2026-08-08` | `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl` | CSS contain:size parses but is never consulted by the sizing pass |
| `browser_engine_css_position_fixed_not_viewport_anchored_2026-08-08` | `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl` | position:fixed resolves against nearest ancestor not the viewport |
| `browser_engine_wikipedia_render_perf_2026-07-11` | `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl` | Real-page software render is ~176s interpreted; 10s budget always degrades |
| `browser_renderer_spec_sequence_failures_2026-06-11` | `src/lib/gc_async_mut/gpu/browser_engine/browser_renderer.spl` | browser_renderer_spec 22 residual failures (sequence-dependent + :has(> )) |
| `char_code_at_quadratic_scan_and_core_string_ascii_probe_2026-07-30` | `src/runtime/simple_core/core_string.spl` | char_code_at is quadratic on non-ASCII text and core_string's ASCII fast path is itself O( |
| `check_run_diagnostics_help_text_and_type_check_gaps_2026-07-20` | `src/app/check/main.spl` | `simple check` misses help: annotations and does not detect type mismatches at all |
| `convnodes_retained_file_result_tuple_u64_2026_10_25` | `src/lib/nogc_sync_mut/io/retained_file.spl` | retained_file result tuple u64 lowering |
| `divergence_byte_char_find_option_sweep_2026-08-01` | `src/lib/common/text.spl` | find/rfind/index_of return a raw i64 -1 sentinel but are consumed as Option across src/** |
| `dynsmf_session_spec_pinned_to_a_6_entry_manifest_that_grew_to_12_2026-08-04` | `test/03_system/stdlib/dynload/dynsmf_session_unload_reload_spec.spl` | dynsmf_session_unload_reload_spec pins a 6-entry autoload manifest the product grew to 12 |
| `engine2d_draw_ir_free_function_state_visibility_2026-06-05` | `src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl` | Draw-IR executor free-function mutations are not visible to the caller |
| `gc_async_mut_missing_facade_wrapper_modules_2026-07-20` | `src/lib/gc_async_mut/__init__.spl` | std.gc_async_mut.compression.lz4 and database.sql.escape resolve to nothing; no facade |
| `gpu_compute_offload_not_wired_to_sffi_launch_2026-07-06` | `src/lib/nogc_async_mut/compute/backend_dispatch.spl` | std.compute offload always computes on CPU and only reports GPU provenance from an env |
| `gpu_probe_then_create_toctou_2026-08-04` | `src/lib/gc_async_mut/gpu/engine2d/engine.spl` | GPU probe-then-create TOCTOU: probe answer is a prediction that does not survive to the |
| `gzip_optional_collection_payload_provenance_2026_10_21` | `src/lib/nogc_sync_mut/compression/gzip/compress.spl` | gzip optional collection payload provenance 2026 10 21 |
| `gzip_untyped_reader_byte_array_text_dispatch_2026_10_21` | `src/lib/nogc_sync_mut/compression/gzip/header.spl` | gzip untyped reader byte array text dispatch 2026 10 21 |
| `hosted_wm_runtime_dso_unadmitted_security_evidence_2026-07-29` | `scripts/check/check-linux-hosted-wm-live-window-evidence.shs` | A bootstrap DSO copied from elsewhere can be presented with a caller-supplied matching |
| `isolated_thread_raw_worker_argument_heuristic_flake_2026-08-12` | `src/runtime/runtime_thread.c` | Isolated-thread raw worker argument heuristic is test-order dependent (flaky) |
| `js_vm_dom_bridge_retention_quadratic_2026-07-30` | `src/lib/nogc_sync_mut/js/engine/vm_object_store.spl` | JS VM DOM bridge retention is frame-linear and property scan is quadratic |
| `layoutglyph_struct_array_i64_field_tag_shift_readback_2026-07-20` | `src/lib/nogc_sync_mut/text_layout/font_renderer.spl` | LayoutGlyph struct-in-array i64 fields read back tag-shifted on freestanding native lane |
| `legacy_import_string_namespace_dict_ignores_source_content_2026-08-11` | `src/lib/string.spl` | import string builds a namespace dict that ignores src/lib/string.spl contents (char_at missing) |
| `lib_entry_file_cannot_resolve_app_prefix_imports_2026-08-17` | `doc/08_tracking/bug/lib_entry_file_cannot_resolve_app_prefix_imports_2026-08-17.md` | `use app.*` is unresolvable when a `src/lib/**` file is the entry file (E1034) |
| `linux_secure_server_perf_runtime_blockers_2026-08-14` | `src/app/postgres_mimic_server/main.spl` | Native PureDatabase fails first post-insert check with invalid-array-handle; HTTP server installs no listener |
| `llm_caret_http_attempt_timeout` | `src/lib/nogc_sync_mut/io/http_sffi.spl` | http_request_raw has no timeout parameter so with_retry cannot cancel a blocked transport |
| `lsp_code_action_edit_emit_parse_mismatch_2026-06-16` | `src/lib/nogc_sync_mut/lsp/lsp_handlers.spl` | LSP code-action edits never apply: emitter output does not round-trip through the edit parser |
| `map_insert_if_absent_missing_and_map_new_resolves_to_dict_2026-07-20` | `V> struct due to module-graph shadowing"` | Map.new() resolves to a plain dict rather than the Map<K |
| `module_load_24s_unless_window_winit_imported_2026-07-25` | `src/lib/gc_async_mut/gpu/engine2d/engine.spl` | Importing std.gpu.engine2d.engine costs 24s unless std.io.window_winit is also imported which drops it to 3s |
| `optional_try_nominal_owner_missing_2026_10_21` | `src/lib/nogc_async_mut/database/bug.spl` | Keep the declared table owner until rebuilt Try metadata recovery is qualified |
| `parse_claude_json_response_name_collision_2026-07-20` | `src/lib/nogc_async_mut/llm/claude_cli.spl` | parse_claude_json_response defined in two modules; registry mis-dispatch fails 8 examples |
| `positional_brace_dict_payload_parsed_as_struct_field_2026_10_20` | `V>"` | positional `V({text: i64})` payload is read as a named field `text: i64`; spelled Dict<K |
| `pure_nn_layers_mix_autograd_tensor_and_puretensor_2026-07-25` | `src/lib/gc_async_mut/pure/nn.spl` | std.pure.nn Linear.forward mixes autograd Tensor with raw PureTensor so it cannot be |
| `pure_simple_provider_host_runtime_capsule_link_required_2026-08-14` | `src/os/smf/provider_loader.spl` | Pure Simple provider host proof needs an admitted runtime capsule; --export-dynamic on |
| `rt_file_read_bytes_declared_with_six_return_types_2026-08-09` | `src/lib/nogc_sync_mut/io/file_ops.spl` | rt_file_read_bytes extern is redeclared repo-wide with four mutually incompatible return types |
| `simple_web_text_decoration_geometry_clip_2026-06-25` | `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl` | text-decoration-thickness and text-underline-offset produce no visibly changed pixels due |
| `svmg_device_arena_code_coresidency_diverges_from_ref_vm_2026-08-07` | `src/lib/common/svmg/ref_vm.spl` | Device single-buffer code/data co-residency diverges from ref_vm's separate code array |
| `text_index_char_int_context_warning_to_error_2026-11-03` | `same staging as exhaustive match)"` | Staged: flip s[i]-used-as-i64 WARNING to ERROR after phase 3 passes (ADR-005 |
| `value_access_ownership_spec_never_executes_2026-09-18` | `and it is hiding a contradiction with the audit script that replaced it"` | The compiler runtime-value-accessor ownership spec has never executed |
| `websocket_timestamp_owner_and_entropy_2026_10_16` | `src/lib/nogc_sync_mut/websocket/frame.spl` | undefined Platform timestamp owner; historical timestamp units unknown |
| `wm_content_kind_render_runtime_gate_2026-07-29` | `src/os/compositor/compositor.spl` | DesktopShell.run() still calls render_all() compatibility path instead of shared frame |
| `x25519mlkem768_neon_rvv_ntt_not_implemented_2026-08-08` | `src/lib/nogc_sync_mut/simd.spl` | NEON and RVV ML-KEM NTT candidates are declared but only the AVX2 i32x8 butterfly exists |
| `zstd_brotli_encoders_are_stored_only_2026-08-17` | `src/lib/common/compress/zstd.spl` | zstd and brotli encoders emit container-only output LARGER than input (310/304 bytes for |

### Interpreter / JIT

| Bug | File | Summary |
|---|---|---|
| `bool_typed_parameter_accepts_non_bool_and_jit_corrupts_it_2026-08-04` | `src/compiler_rust/compiler/src/interpreter_call/core/arg_binding.rs` | A bool-declared parameter silently accepts a non-bool (rejection half still open) |
| `duplicate_type_name_collision_audit_2026-07-17` | `src/compiler/10.frontend/core/interpreter/eval_tables.spl` | Flat global class/enum registries let same-named types in different modules collide at |
| `editor_jit_run_route_blockers_2026-05-28` | `items 1/3 addressed"` | editor `bin/simple run` JIT route still blocked on item 2 (deferred) |
| `fat32_microbench_jit_mut_capability_2026-05-27` | `test/05_perf/bench/fat32_microbench.spl` | fat32_microbench segfaults / hits W1006 mutation-without-mut before entering Fat32Core.write |
| `interp_brace_literal_collides_with_string_interpolation_2026-07-03` | `not interpolated"` | Literal `{ ... }` sharing a string with other `{placeholder}`s is silently swallowed |
| `interp_class_name_collision_breaks_test_db_persistence_2026-08-10` | `breaking test-DB run persistence"` | Interpreter resolves a class by name across modules |
| `interp_compositor_backend_put_pixel_clones_framebuffer_2026-07-03` | `src/compiler_rust/compiler/src/interpreter_method/collections.rs` | CompositorBackend.put_pixel clones the entire framebuffer on every pixel write |
| `interp_for_over_list_generic_2026-07-02` | `doc/08_tracking/bug/interp_for_over_list_generic_2026-07-02.md` | Interpreter: `for` cannot iterate `List<T>` — ""cannot iterate over this type"" |
| `interp_module_global_stale_read_in_spec_blocks_2026-07-05` | `src/lib/nogc_sync_mut/diag.spl` | Module global read inside a spec block returns a stale value |
| `interp_use_as_alias_not_visible_in_function_body_2026-07-20` | `src/compiler/90.tools/verify/checker.spl` | Module-level use <module> as <alias> is not resolvable inside a function body: variable <alias> not found |
| `interpreter_bdd_missing_structured_test_evidence_2026-07-19` | `src/lib/nogc_sync_mut/spec.spl` | Pure-Simple BDD consumer still cannot authenticate interpreter results via --assert-ran |
| `interpreter_bytes_u64_false_green_memory_2026-08-11` | `src/compiler_rust/compiler/src/value.rs` | Interpreter byte allocation reports a U64 false-green and blows up memory on 1MiB push bench |
| `interpreter_eval_access_calls_drifted_duplicate_definitions_2026-08-11` | `src/compiler/80.driver/driver_source_loading.spl` | Ten drifted duplicate interpreter fn definitions exist and the STALE copies win name resolution |
| `interpreter_pending_skip_dsl_intercept_bypasses_spl_body_2026-08-07` | `src/compiler_rust/compiler/src/interpreter_call/bdd.rs` | Rust seed interpreter intercepts pending/skip_it/skip before the .spl body in spec.spl ever runs |
| `interpreter_result_match_return_sigsegv_2026-07-17` | `src/compiler_rust/compiler/src/interpreter_call/block_execution.rs` | RunningType::Interpreter SIGSEGVs on a match over a Result with a return inside an arm |
| `interpreter_serial_net_sffi_dispatch_gap` | `tcp_listener_*/tcp_stream_*` | Interpreter extern dispatch gap: rt_serial_* |
| `interpreter_struct_in_dict_with_closure_field_reads_nil_2026-08-10` | `src/lib/nogc_async_mut/actors/actor.spl` | Struct stored in a Dict reads back nil on a field that has a closure-typed sibling field |
| `iso_borrow_check_unreachable_from_interpret_pipeline_2026-08-09` | `src/compiler/80.driver/driver_pipeline_passes.spl` | iso/borrow-check pass is unreachable from the interpret pipeline so bin/simple test never runs it |
| `jit_closure_abi_refuses_lambdas_and_miscompiles_fn_refs_2026-08-06` | `demoting it to the interpreter"` | JIT refuses whole module containing a lambda |
| `jit_lowering_module_alias_and_panic_2026-07-02` | `forcing interpreter fallback"` | JIT HIR lowering rejects module-alias references and the panic intrinsic |
| `jit_strict_coverage_gap_2026-07-30` | `src/compiler_rust/driver/src/exec_core.rs` | SIMPLE_JIT_STRICT fails open on unresolved globals: lowering proceeds and the error only surfaces at call time |
| `jit_struct_assignment_aliases_not_copies_2026-08-10` | `src/compiler_rust/compiler/src/mir/lower/lowering_stmt.rs` | JIT struct assignment aliases instead of copying; interpreter copies (residual cases after 2026-08-10) |
| `js_engine_missing_builtins_regex_promise_prototype_2026-07-11` | `src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl` | JS engine String.replace with a regex is a silent no-op |
| `list_first_returns_raw_value_not_option_2026-07-20` | `src/compiler_rust/compiler/src/interpreter_method/collections.rs` | List<T>.first returns a raw nilable value instead of Option<T> as documented |
| `mcp_interpreter_startup_12s_2026-09-14` | `src/app/mcp/main.spl` | MCP interpreter startup spends roughly 11-13 seconds in eager module loading |
| `mcp_stdio_interpreter_gate_exceeds_cpu_guard_2026-08-10` | `src/compiler/80.driver/driver_source_pipeline_loading.spl` | MCP stdio interpreter gate exceeds the CPU guard; rt_file_is_char_device unresolved |
| `mem_infra_parity_specs_cranelift_arm_demotes_to_interpreter_2026-08-09` | `test/01_unit/lib/mem_infra/guard_backend_parity_spec.spl` | guard/harden backend-parity specs cranelift arm silently demotes to interpreter so cranelift is never measured |
| `nested_fn_cannot_mutate_enclosing_it_block_var_2026-08-04` | `src/compiler_rust/compiler/src/interpreter/expr/control.rs` | Nested fn assigning an enclosing it-block var does not update it; compound assign says v |
| `os_namespace_uninitialized_array_module_var_not_found_2026-08-02` | `src/compiler_rust/compiler/src/interpreter/node_exec.rs` | Module-level uninitialized array var is unresolvable in the os.* namespace only |
| `prelude_builtins_rebindable_by_transitive_import_2026-08-10` | `src/compiler_rust/compiler/src/interpreter_call/mod.rs` | 50 prelude builtins beyond `exit` remain silently shadowable by a transitive top-level fn |
| `scram_sha1_examples_exceed_interpreter_10m_op_budget_2026-08-04` | `src/compiler_rust/compiler/src/interpreter_state.rs` | SCRAM-SHA-1 RFC 5802 spec exceeds the interpreter's 10M-operation budget once PBKDF2 runs |
| `seed_constructor_static_method_no_literal_coercion_2026-07-20` | `src/compiler_rust/compiler/src/interpreter_method/special/objects.rs` | Seed constructor dispatch needs an exact runtime type: an int literal will not coerce to a |
| `seed_hybrid_jit_spliced_u8_array_boxed_elements_2026_10_19` | `src/compiler_rust/runtime/src/value/utf8_kernels.rs` | Seed hybrid JIT returns [u8] through the interpreter splice with boxed elements; indexing and bulk rt_* calls  |
| `seed_interp_ecs_lower_and_freefn_closure_byref` | `src/os/services/devfs_service.spl` | Seed interpreter cannot lower ECS Entity/ComponentStore<T>; free-fn mutation lost inside |
| `seed_interpreter_zeroize_not_guaranteed_2026_10_31` | `doc/08_tracking/bug/seed_interpreter_zeroize_not_guaranteed_2026_10_31.md` | Seed interpreter cannot guarantee zeroization through a parameter |
| `seed_overload_score_option_bytes_misleading_unknown_static_2026-07-20` | `src/compiler_rust/compiler/src/interpreter_method/special/objects.rs` | Static-call overload scoring reports unknown static method object on class |
| `shim_init_keepalive_function_ptr_cast_breaks_interpreter_2026-08-06` | `src/os/kernel/abi/syscall_shim.spl` | shim_init calls _shim_keepalive whose fn-ptr-to-u64 casts fail: cannot cast function to... |
| `smf_standalone_interp_fallback_functions_unavailable_2026-06-14` | `slices)"` | BUG: standalone SMF cannot run interp-fallback functions (string interpolation |
| `source_fixture_spec_unescaped_interpolation_and_content_drift_2026-07-20` | `test/01_unit/compiler/hir/module_lowering_dict_keys_source_spec.spl` | Source-guard specs put {ident} in interpolating strings so they die with `variable |
| `stress_f03_manycall_sum_2026-07-17` | `src/compiler_rust/compiler/src/interpreter_call/mod.rs` | 300-call-chain sum diverges on the interpreter path only; compiled/JIT already correct |
| `string_interpolation_silently_evaluates_literal_braces_2026-07-28` | `src/compiler_rust/parser/src/lexer/strings.rs` | Interpolation evaluates literal brace content with no guard or diagnostic |
| `text_len_codepoint_switch_2026-11-03` | `src/compiler_rust/compiler/src/interpreter/expr/collections.rs` | Held until phase 3: switch text.len() from bytes to code points per ADR-005; byte_len()/char_count() explicit  |
| `web_backend_env_get_alias_unresolved_interpret_2026-07-07` | `doc/08_tracking/bug/web_backend_env_get_alias_unresolved_interpret_2026-07-07.md` | Interpreter: `env_get as web_backend_env_get` re-export alias unresolved — chromium WebRenderBackend facade  |
| `x25519mlkem768_jit_fallback_interpreted_execution_2026-08-05` | `src/os/crypto/x25519_mlkem768/execution_policy.spl` | All X25519MLKEM768 hot-path operations run interpreted; JIT lost on the entire hybrid-KEM |

### Seed

| Bug | File | Summary |
|---|---|---|
| `bug_add_seed_rename_path_stack_overflow_2026_10_19` | `src/lib/nogc_sync_mut/io_runtime.spl` | bug-add on the Rust seed overflows the stack in rename_path and saves nothing |
| `cargo_test_lib_129_failures_triage_2026-08-10` | `src/compiler_rust/compiler/src/lint/checker_core.rs` | cargo test -p simple-compiler --lib has 129 remaining unit-test failures after 6 were fixe |
| `coverage_tooling_does_not_instrument_spl_2026-08-07` | `src/compiler_rust/compiler/src/mir/lower/lowering_coverage.rs` | No branch probes from MIR lowering; no coverage artifact on the .spl runner path |
| `retained_manual_system_link_old_seed_abi_2026_10_25` | `doc/08_tracking/bug/p4_retained_manual_route_2026_10_25.md` | Retained runtime ABI blocks normal system link |
| `rust_seed_run_help_treated_as_source_filename_2026-09-09` | `src/compiler_rust/driver/src/main.rs` | Rust seed run --help is treated as a source filename instead of subcommand help |
| `seed_coalesce_stateful_operand_twice_2026_10_12` | `src/compiler/10.frontend/generated/ast_semantic_value.spl` | Seed coalesce evaluates a stateful optional operand twice in ast_semantic_hash_finish |
| `seed_main_entry_file_text_allocation_failed_2026-11-01` | `src/lib/nogc_sync_mut/io/file_text_session.spl` | Seed runtime: file reads inside an auto-invoked fn main fail with file text input allocation failed (silent em |
| `seed_module_name_shadows_match_binding_2026_10_31` | `doc/08_tracking/bug/seed_module_name_shadows_match_binding_2026_10_31.md` | Seed lets a module name shadow a match binding called value |
| `seed_value_match_no_arm_yields_nil_2026-11-02` | `doc/08_tracking/bug/seed_value_match_no_arm_yields_nil_2026-11-02.md` | Seed value match with no matching arm silently yields nil |
| `seed_windows_path_identity_errno_discovery_2026_10_06` | `src/lib/nogc_sync_mut/io/path_identity_abi.spl` | keep_nonwindows_errno_directives_out_of_windows_seed_discovery |
| `wildcard_import_c_backend_stubs_function_to_int_2026-07-30` | `src/compiler_rust/compiler/src/value_impl.rs` | use compiler.backend.backend.c_backend_stubs.* poisons the session with cannot convert |
| `wm_production_fullscreen_evidence_security_registry_any_field_infer_2026-08-09` | `src/compiler_rust/compiler/src/mir/lower/lowering_expr_control.rs` | check-wm-production-fullscreen-evidence.shs still fails; fix 7fa2d06aaa8 not in deployed |

### Tester

| Bug | File | Summary |
|---|---|---|
| `cover_gate_fails_every_system_test_without_running_one_2026-08-04` | `src/lib/nogc_sync_mut/test_runner/test_runner_files.spl` | # @cover gate marks 227 system tests FAILED without running one |
| `env_gated_spec_switches_are_inert_under_test_daemon_2026-08-09` | `src/app/test_runner_new/test_runner_client.spl` | Env vars set by the caller never reach the spec body under bin/simple test so gates fail open |
| `phase1_docstring_trim_start_dispatch_2026_10_12` | `src/lib/nogc_sync_mut/test_runner/doctest_runner.spl` | Phase1 source doctest inventory cannot dispatch str.trim_start |
| `simple_test_nested_runner_timeout_2026-06-28` | `src/app/test_runner_new/test_runner_client.spl` | A spec that shells out to a nested `bin/simple test` times out the outer test daemon |
| `system_cover_gate_reports_791_legacy_feature_specs_as_failures_2026-08-04` | `src/app/test_runner_new/test_runner_main.spl` | @cover gate marks 791 un-annotated test/03_system/feature specs as FAILURES not skips |
| `test_daemon_freezes_env_binary_override_dead_2026-08-02` | `so SIMPLE_* binary override is silently ignored"` | Long-lived light daemon freezes env |
| `test_invocation_fixed_setup_cost_caps_every_sweep_2026-08-17` | `src/app/test_daemon/light_daemon.spl` | bin/simple test per-invocation fixed setup cost (Windows measured ~7.8s; Linux daemon path unmeasured) |
| `test_runner_env_passthrough_2026-07-29` | `src/lib/nogc_sync_mut/test_runner/test_runner_args.spl` | Custom env vars set before bin/simple test are stale inside it bodies (daemon-frozen env) |

### Other (apps, tools)

| Bug | File | Summary |
|---|---|---|
| `acpi_spec_three_reads_return_zero_2026-09-19` | `and it is NOT the nested-fn capture defect it was attributed to"` | The acpi unit spec's three positive reads return 0 |
| `app_mcp_intensive_spec_is_84s_not_a_hang_eight_real_failures_2026-08-10` | `RED with 8 real failures"` | app_mcp_intensive_spec is not hung: 84s spec |
| `app_modules_referenced_by_specs_exist_nowhere_2026-08-04` | `src/app/cli/main.spl` | Spec-referenced app symbols missing: handle_os_inline / handle_os_build_inline |
| `artifact_manifest_signature_verification_no_trust_anchor_2026-08-07` | `src/os/kernel/loader/artifact_manifest.spl` | SimpleArtifactManifest.signature has no trust-anchor or key-distribution infra |
| `cache_v2_first_milestone_known_gaps_2026-08-10` | `lease` | Cache v2 interface-compat milestone ships with known unfixed gaps (GC admission |
| `capability_group_from_unsound_under_value_semantics_2026-08-09` | `so the group copies n"` | Capability-group .from() is unsound because classes are value types |
| `caret_closure_enum_payload_binding_collection_gaps_2026_11_03` | `local binding and collection method diagnostics (split from leaf provider gaps)"` | Caret closure enum payload |
| `check_costs_two_seconds_per_function_decl_2026-08-10` | `src/app/check/main.spl` | `simple check` costs ~2s per function declaration plus ~20s fixed per worker process |
| `code_quality_specs_import_modules_that_do_not_exist_2026-08-04` | `test/system/code_quality/deprecated_removed_spec.spl` | code_quality specs import std.common.set_utils/iterable and Set type that do not exist |
| `core_intensive_spec_tests_local_stubs_not_database_core_2026-08-04` | `not std.database.core"` | core_intensive_spec.spl is vacuous - tests local stubs |
| `cross_engine_value_semantics_harness_known_red_2026-08-10` | `test/03_system/language/value_semantics/cross_engine_value_semantics_spec.spl` | Cross-engine value-semantics differential harness landed KNOWN-RED |
| `devhub_email_contract_drift_2026_10_19` | `outlook provider mapping` | DevHub email: exit codes |
| `devhub_redaction_comma_secret_suffix_leak_2026_10_19` | `src/app/devhub/redaction.spl` | DevHub diagnostic redaction leaks the suffix of comma-containing quoted secrets and Cookie/Set-Cookie values |
| `di_test_tag_env_not_inherited_by_subprocess_2026-07-02` | `so the # @di_test tag cannot bypass the"` | Spawned test child never sees SIMPLE_DI_TEST=1 |
| `direct_arch_imports_outside_arch_2026-08-11` | `violating AC-3 portability"` | 7 modules outside arch/ import arch-family modules directly |
| `disk_image_builder_unbuildable_regression` | `src/os/port/disk_image.spl` | os.port.disk_image fails semantic cannot iterate over this type and llc l5 name |
| `doctest_surfaces_registered_but_not_executed_2026-09-19` | `doc/08_tracking/bug/doctest_surfaces_registered_but_not_executed_2026-09-19.md` | BUG: the markdown and comment doctest surfaces are wired but effectively execute nothing |
| `dot_question_returns_optional_but_25_sites_return_it_as_bool_2026-08-09` | `leaking T? payload; return type is"` | 24 of 25 -> bool functions return .? directly |
| `engine3d_ext_impl_blocks_never_imported_2026-07-02` | `leaving trait impls incomplete"` | engine3d *_ext.spl plain impl blocks are never imported |
| `fs_exec_ring3_fork_unreachable_spawnwait_2026-08-06` | `src/os/kernel/loader/x86_64_fs_exec_ring3.spl` | fork(57) is unreachable from ring-3 FS-exec because the process is never a scheduler Task |
| `gpu_scheduler_diag_counter_readback_type_infer_2026-07-06` | `i64>.get(k) ?? i64 infers the KEY type on first monomorphization and rejects"` | Dict<text |
| `guard_wiring_optout_false_exemptions_2026-08-06` | `hiding 8 RED and 2 fail-open"` | guard_wiring_optout.txt exempts 20+ gates on false reasons |
| `hosted_wm_glyph_oracle_uncalibratable_2026-08-01` | `scripts/check/check-linux-hosted-wm-live-window-evidence.shs` | check-linux-hosted-wm-live-window-evidence.shs:18 still hard-fails on |
| `image_builder_nvfs_rootfs_marker_preexisting_2026-06-28` | `src/os/installer/image_builder.spl` | image_builder nvfs rootfs backend marker assertion fails (pre-existing red) |
| `is_nil_is_not_a_language_builtin_2026-07-27` | `differently per engine"` | is_nil is not a language builtin and fails on every ordinary receiver |
| `js_engine_no_dom_bom_globals_2026-07-11` | `so real-page DOM JS silently no-ops"` | JS engine binds no DOM/BOM globals |
| `kv260_ps_bd_pl_clk0_unreachable_jtag_bringup_2026-07-24` | `scripts/fpga/build_k26_rv32.shs` | KV260 PS block-design pl_clk0/pl_resetn0 are unreachable in JTAG-only bring-up |
| `llm_caret_compiled_carrier_build_latency_2026-08-02` | `src/app/llm_caret/messaging/hook_worker.spl` | LLM Caret compiled carrier link fails on unresolved stdlib symbols (trim/starts_with/unwrap_err) |
| `llm_caret_index_of_optioni64_tagbox_2026-07-07` | `src/app/llm_caret/json_helpers.spl` | text.index_of returns nil for a present substring (Option<i64> tag-box mangled) |
| `llm_caret_unit_specs_rotted_2026_10_19` | `stray indent) and claude_cli_spec calls undefined _Q/_escape_json"` | llm_caret unit specs fail at source: 4 parse errors (unterminated docstring |
| `local_named_vec_makes_index_assignment_a_vec_literal_lvalue_2026-09-05` | `doc/08_tracking/bug/local_named_vec_makes_index_assignment_a_vec_literal_lvalue_2026-09-05.md` | A local array named `vec` turns `vec[i] = x` into a vector-literal lvalue |
| `lsp_mcp_server_process_leak_2026-07-05` | `src/app/simple_lsp_mcp/main.spl` | simple-lsp-mcp leaves orphaned server processes with no cleanup (48 observed) |
| `match_unqualified_imported_enum_variant_default_arms_2026-10-24` | `src/plugins/backend_vhdl/vhdl_backend.spl` | match bare payload variants lowered as binding default arms |
| `mission_critical_infra_hardening_v2_wave1_red_2026-08-11` | `draw_ir arena v3 and sosix certified_manifest specs"` | Mission-Critical Infra Hardening V2 Wave 1 is RED across compiler_admission |
| `ml_kem_postfix_to_equal_chained_call_not_found_2026-07-20` | `blocking ML-KEM algebraic assertions"` | Postfix .to_equal() matcher is unresolved when the receiver is a chained call |
| `mlkem_ntt_simd_public_interface_probe_crashes_not_pass_2026-08-05` | `so the reported PASS is unsupported"` | AC-4 SIMD byte-identity probe crashes on reproduction and the named .spl probe file was never created |
| `non_discriminating_spec_family_2026-08-08` | `scripts/check/check-vacuous-specs.shs` | Enumerated family of vacuous specs that pass regardless of implementation behavior |
| `nvme_rv32_firmware_build_timeout_2026-07-05` | `scripts/check/check-nvme-rv32-minimal-live.shs` | rv32 firmware wrapper times out before producing build/nvme_fw_rv32.elf |
| `orphaned_part_files_never_imported_2026-09-18` | `so nothing compiles them"` | Six part-files under `_<Name>/` split directories are never imported |
| `process_transfer_session_replay_identity_2026-08-12` | `which is not authentication"` | Transfer session identity uses FNV-1a over 31 PID bits |
| `provider_loader_path_digest_toctou_2026-08-16` | `so digest is not"` | provider_admit_dynamic_v1 hashes the declared path then reopens it |
| `rtl_mdsoc_phase5_modules_never_created_2026-08-04` | `simd` | vhdl_emit_{fp |
| `rtl_mdsoc_reorg_fpga_linux_split_never_executed_2026-08-04` | `94 examples red per tree"` | fpga_linux split never executed: orchestrator/data/manifest modules absent |
| `sci_launcher_policy_projection_owner_api_missing_2026-08-14` | `src/os/services/launcher/launcher_registry.spl` | SCI launcher rejects whole images: no owner API for path-scoped caps and file associations |
| `self_error_used_where_error_fatal_intended_family_2026-08-08` | `so builds exit rc=0 on"` | MirLowering.error() sites intended as fatal stay non-fatal |
| `shard_mem_clamp_ignores_enclosing_cgroup_memory_max_2026-10-19` | `so HIR fanout inside a cgroup-contained build is sized by host MemAvailable"` | Managed Linux worker filters SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB out of the compiler environment and shard_mem |
| `smf_writer_kernel_trailer_layout_skew` | `src/os/kernel/loader/smf.spl` | No compiler-emitted .smf is accepted as a role-2 library: writer and kernel trailer |
| `spec_imports_declared_nowhere_2026-08-04` | `only warned not"` | 1003 names imported by 294 spec files are declared nowhere in owned src/ |
| `specs_assert_against_nonexistent_product_paths_2026-08-10` | `scripts/check/check-spec-missing-path-vacuity.shs` | 835 specs read 949 absent product paths so their negative to_equal(false) legs pass |
| `ssa_write_count_quadratic_scan_2026_10_25` | `src/app/io/_CliCompile/compile_targets.spl` | ssa write count quadratic scan (workaround registered) |
| `stale_snapshot_rewind_gate_misses_small_rewinds_2026_11_03` | `scripts/check/check-no-stale-snapshot-rewind.shs` | no-stale-snapshot-rewind gate PASSed PR #6132 rewinding 2 files of its parent #6130 (below THRESHOLD=5) and is |
| `supervised_builder_unwired_and_no_peak_rss_2026-08-17` | `and peak RSS is always 0"` | Supervised builder: not yet wired to a front end |
| `tautology_guarded_skip_specs_false_green_family_2026-08-04` | `census inco"` | Tautology-guarded skip specs report green without executing; repo-wide family |
| `tcp_accept_timeout_nonblocking_stream_windows_2026-10-31` | `doc/08_tracking/bug/tcp_accept_timeout_nonblocking_stream_windows_2026-10-31.md` | TCP accept with timeout returns a non-blocking stream on Windows |
| `test_tree_divergence_982_diagnosis_2026-08-08` | `1 stale-baselined) against baselin"` | check-test-tree-divergence reports 982 diverged (1 new |
| `test_tree_divergence_preexisting_red_stepover_2026-08-17` | `doc/08_tracking/bug/test_tree_divergence_preexisting_red_stepover_2026-08-17.md` | Pre-existing test-tree divergence red — recorded step-over (2026-08-17) |
| `theme_ipc_k2_review_hard_stop_2026-07-27` | `K2 transport unimplemented"` | Theme IPC K2 stays fail-closed: no accepted design |
| `three_computedstyle_concepts_2026-08-10` | `browser_engine style` | three unrelated ComputedStyle types coexist (blink entity |
| `tls_signature_positive_verification_blockers_2026-06-06` | `test/03_system/os/os_tls_cert_chain_spec.spl` | TLS signature verification has no positive test: ed25519/RSA-PSS/cert-chain specs cannot |
| `trait_group_with_sugar_unwired_and_from_aot_if_val_2026-08-09` | `src/app/desugar/trait_desugar.spl` | trait-group `with` desugar is unreachable and its generated .from() capability check is |
| `treesitter_node_module_missing_and_spec_tautological_2026-08-04` | `so the red is"` | std.parser.treesitter_node does not exist and its spec asserts nothing |
| `unregistered_extern_backlog_enumeration_2026-08-01` | `so lanes silently drop them"` | Externs declared in .spl are absent from the extern registry |
| `vacuous_spec_corpus_census_and_inert_assertion_forms_2026-08-02` | `095 spec files contain inert assertion forms that pass without exercising anything"` | 5 |
| `w_mc_res_001_overfires_verb_only_heuristic_2026-08-07` | `cannot separate acquires from"` | W-MC-RES-001 verb-only heuristic over-fires ~208 findings |
| `wine_vm_module_family_destroyed_by_tree_wipe_2026-08-04` | `so contents are"` | wine_vm module family lost to a tree wipe and partly rebuilt by guess |
| `wm_action_applier_window_surface_session_and_web_window_request_2026-08-10` | `src/os/compositor/wm_action_applier.spl` | wm_action_applier_spec: 2 of 17 examples RED — window-surface session and |
| `wm_host_external_content_owner_2026-07-29` | `src/os/compositor/host_compositor_core.spl` | Remote application presentation still RED after content_owner scalar fix for external |

## P3

### Compiler

| Bug | File | Summary |
|---|---|---|
| `architecture_rule_audit_2026-08-11` | `src/compiler/35.semantics/gc_boundary_check.spl` | Architecture audit of 2026-08-10-11 window: 4 findings need a decision |
| `arrow_lambda_parser_half_reverted_by_snapshot_commit_2026-09-01` | `doc/08_tracking/bug/arrow_lambda_parser_half_reverted_by_snapshot_commit_2026-09-01.md` | Arrow-lambda parser work partially reverted by a ""snapshot"" commit |
| `backend_capability_spec_fictional_test_builder_api_2026-07-30` | `test/01_unit/compiler/backend/backend_capability_spec.spl` | backend_capability_spec: 34 commented tests target a never-built capability API |
| `compiler_semantic_cache_weakness_audit_2026-09-01` | `doc/08_tracking/bug/compiler_semantic_cache_weakness_audit_2026-09-01.md` | Compiler semantic cache weakness audit — 2026-09-01 |
| `const_generic_argument_rejected_in_constructor_call_2026-08-17` | `src/compiler/10.frontend/core/parser_expr.spl` | Const-generic argument rejected in constructor-call position (feature gap) |
| `credential_v1_records_have_no_upgrade_on_write_owner_2026-08-08` | `src/lib/nogc_sync_mut/terminal/credential/config_parser.spl` | v1 credential records never rewritten; no config writer owns the upgrade |
| `full_compiler_check_no_progress_over_five_minutes_2026-08-21` | `doc/08_tracking/bug/full_compiler_check_no_progress_over_five_minutes_2026-08-21.md` | Full compiler check shows no progress for more than five minutes |
| `generic_class_static_method_unresolved_under_test_2026-07-20` | `doc/08_tracking/bug/generic_class_static_method_unresolved_under_test_2026-07-20.md` | Bug: `GenericClass<T>.static_method()` unresolved under `simple test` (non-generic classes work fine) |
| `generic_map_semantic_lookup_fails_2026-09-16` | `V> methods fail semantic lookup on dict receivers"` | Generic Map<K |
| `glob_imported_private_fn_lowers_to_unmangled_extern_2026-09-13` | `doc/08_tracking/bug/glob_imported_private_fn_lowers_to_unmangled_extern_2026-09-13.md` | A glob-imported PRIVATE fn lowers to an unmangled extern instead of failing to resolve |
| `gui_content_renderer_parser_expected_pattern_found_use_2026-08-12` | `doc/08_tracking/bug/gui_content_renderer_parser_expected_pattern_found_use_2026-08-12.md` | GUI content renderer parser recovery failure — 2026-08-12 |
| `http_request_parser_missing_strict_header_validation_2026-09-16` | `doc/08_tracking/bug/http_request_parser_missing_strict_header_validation_2026-09-16.md` | HttpRequestParser: missing Host/field-name strictness (request validation hardening) |
| `lean_parser_bitwise_pipe_precedence_divergence_2026-06-11` | `src/compiler/10.frontend/core/parser_expr.spl` | Lean-exported parser gives bitwise-or and pipe operators divergent precedence vs parser_expr.spl |
| `lint_codeline_has_no_field_code_closure_dependent_2026-09-07` | `depending on the linted file's import closure"` | `simple lint` aborts with `class CodeLine has no field named code` |
| `lint_default_lane_segfault_from_worktree_bin_path_2026-09-13` | `doc/08_tracking/bug/lint_default_lane_segfault_from_worktree_bin_path_2026-09-13.md` | `simple lint` segfaults in the default (JIT-attempt) lane when the compiler binary is invoked from a path insi |
| `lint_linear_scan_in_loop_reads_nonexistent_codeline_field_2026-09-06` | `doc/08_tracking/bug/lint_linear_scan_in_loop_reads_nonexistent_codeline_field_2026-09-06.md` | `bin/simple lint` aborts: `class CodeLine has no field named code` |
| `lint_segv_on_dual_run_spec_files_2026-09-03` | `doc/08_tracking/bug/lint_segv_on_dual_run_spec_files_2026-09-03.md` | `simple lint` SEGVs on the dual-run spec files |
| `lint_timeout_hwir_zca_rows_2026-08-17` | `not a superlinear parser"` | Lint cost on src/compiler/50.mir/hwir/zca_rows.spl — dominant term is an interpreted frontend |
| `lsp_mcp_transport_mode_and_id_parser_2026-08-16` | `doc/08_tracking/bug/lsp_mcp_transport_mode_and_id_parser_2026-08-16.md` | LSP MCP transport mode and request-ID parser duplication |
| `module_global_fn_pointer_lowered_as_direct_call_2026-08-21` | `doc/08_tracking/bug/module_global_fn_pointer_lowered_as_direct_call_2026-08-21.md` | Module-global function-pointer slot lowers to a DIRECT call |
| `nll_mut_borrow_of_local_false_positive_at_return_2026-08-24` | `doc/08_tracking/bug/nll_mut_borrow_of_local_false_positive_at_return_2026-08-24.md` | NLL borrow check: `&mut` of a local is reported ""may still be active at return"" at every return (2026-08-24) |
| `no_general_spl_to_svmg_path_blocks_dap_gpu_attach_2026-08-09` | `src/compiler/70.backend/svmg_lowering.spl` | lower_svmg_program has no callers outside 70.backend so DAP GPU attach is routing-only |
| `parser_bare_reassignment_multiline_continuation_2026-07-25` | `while `val x =n expr` is accepted"` | Parser rejects multi-line continuation of a bare reassignment RHS (`x =n expr`) |
| `parser_block_if_expr_trailing_inline_else_2026-08-17` | `doc/08_tracking/bug/parser_block_if_expr_trailing_inline_else_2026-08-17.md` | Block-form `if` expression rejects a trailing inline `else:` on the branch body line |
| `parser_common_mistake_hint_spam_on_stdlib_2026-07-25` | `~5 s per run)"` | Parser emits ~11.5k false-positive `PythonSelf` hints on our own stdlib (150k log lines |
| `parser_or_pattern_line_continuation_2026-08-17` | `doc/08_tracking/bug/parser_or_pattern_line_continuation_2026-08-17.md` | Parser: a `/` or-pattern continued onto the next line does not parse |
| `parser_same_indent_leading_operator_continuation_2026-08-17` | `doc/08_tracking/bug/parser_same_indent_leading_operator_continuation_2026-08-17.md` | Leading-operator line continuation at the SAME indent does not parse |
| `parser_step_decorator_string_form_2026-07-02` | `found FString"""` | Parser: `@step ""label""` decorator form fails — ""expected Fn |
| `poll_unwrap_second_bind_site_lower_and_check_impl_2026-08-25` | `independent bind site"` | `Poll.unwrap` steals `.unwrap()` in `lower_and_check_impl` — a SECOND |
| `primitive_api_lint_ac_d1_and_ac_d2_are_contradictory_2026-08-04` | `src/compiler/90.tools/fix/rules/impl_/lint_primitive_api.spl` | primitive_api lint AC-D1 and AC-D2 demand opposite verdicts on the same signature shape |
| `query_lint_unused_nested_scope_2026-08-24` | `doc/08_tracking/bug/query_lint_unused_nested_scope_2026-08-24.md` | Query lint UNUSED001 nested-function scope |
| `raw_mode_disable_refcell_double_borrow_2026-07-04` | `doc/08_tracking/bug/raw_mode_disable_refcell_double_borrow_2026-07-04.md` | rt_terminal_disable_raw_mode panics ""RefCell already borrowed"" (SIGABRT on every raw-mode quit) |
| `robust_lint_lane_scan_latency_2026-08-21` | `doc/08_tracking/bug/robust_lint_lane_scan_latency_2026-08-21.md` | Robust lint lane scan exceeds bounded verification time |
| `rust_memory_provider_rustfmt_drift_blocks_scoped_sffi_lint_2026-08-26` | `doc/08_tracking/bug/rust_memory_provider_rustfmt_drift_blocks_scoped_sffi_lint_2026-08-26.md` | Rust memory provider formatting drift blocks scoped SFFI lint |
| `scv_distributed_textual_db_missing_production_boundaries_2026-09-13` | `doc/08_tracking/bug/scv_distributed_textual_db_missing_production_boundaries_2026-09-13.md` | SCV distributed textual DB production boundaries are missing |
| `scv_gzip_compress_dominates_pack_write_2026-08-26` | `doc/08_tracking/bug/scv_gzip_compress_dominates_pack_write_2026-08-26.md` | `gzip_compress` dominates every SCV pack write (110s for a 16 KB payload) |
| `scv_merge_commit_parents_separator_inconsistent_2026-08-26` | `doc/08_tracking/bug/scv_merge_commit_parents_separator_inconsistent_2026-08-26.md` | SCV: merge-commit `parents:` separator inconsistent across readers (2026-08-26) |
| `scv_structural_merge_drops_one_side_edit_conflict_data_2026-08-27` | `doc/08_tracking/bug/scv_structural_merge_drops_one_side_edit_conflict_data_2026-08-27.md` | scv structural 3-way merge falls back to conflict-data and drops one side's edit |
| `simple_lint_ast_rules_unwired_2026-07-19` | `doc/08_tracking/bug/simple_lint_ast_rules_unwired_2026-07-19.md` | Production `simple lint` omits semantic AST rules |
| `simple_web_textarea_overlay_review_hard_stop_2026-07-27_tldr` | `doc/08_tracking/bug/simple_web_textarea_overlay_review_hard_stop_2026-07-27_tldr.md` | Simple Web textarea overlay hard stop — TLDR |
| `svmg_d4_lowering_deferred_subset_2026-08-07` | `src/compiler/70.backend/svmg_lowering.spl` | SVM-G D4 lowering leaves 2 in-subset constructs unimplemented |
| `svmg_lowering_spec_unterminated_fstring_parse_failure_2026-09-13` | `doc/08_tracking/bug/svmg_lowering_spec_unterminated_fstring_parse_failure_2026-09-13.md` | `test/01_unit/compiler/backend/svmg_lowering_spec.spl` fails to parse: ""Unterminated f-string"" |
| `theme_snapshot_catalog_review_hard_stop_2026-07-27_tldr` | `doc/08_tracking/bug/theme_snapshot_catalog_review_hard_stop_2026-07-27_tldr.md` | Theme snapshot catalog hard stop — TLDR |
| `twelve_verification_assurance_specs_broken_not_flaky_2026-08-21` | `not flaky — and one is a parser defect"` | 12 verification/assurance specs are stably broken |
| `type_alias_swapped_winner_is_inert_2026-08-01` | `src/compiler/35.semantics/lint/semantic_api/alias_registry.spl` | a swapped duplicate-`type` alias winner is inert: the alias target is never stored |
| `unsafe_block_expression_binding_parser_gap_2026-08-21` | `doc/08_tracking/bug/unsafe_block_expression_binding_parser_gap_2026-08-21.md` | Unsafe block expression binding parser gap |
| `unwired_extractions_audit_2026-08-11` | `src/compiler/70.backend/linker/reloc_engine.spl` | Deduplication extractions were authored and announced Resolved but never wired to consu... |

### Lib / runtime

| Bug | File | Summary |
|---|---|---|
| `array_at_method_missing_dash_path_2026-07-20` | `not just its spec"` | `array.at(i)` method does not exist — breaks production `dash_path` code |
| `blake2s_std_crypto_module_missing_2026-07-20` | `doc/08_tracking/bug/blake2s_std_crypto_module_missing_2026-07-20.md` | `std.crypto.blake2s` module does not exist (only `os.crypto.blake2s`) |
| `browser_engine_text_metrics_api_drift_2026-07-20` | `src/lib/gc_async_mut/gpu/browser_engine/browser_renderer.spl` | browser_engine text-metrics spec: residual API gaps after content_x/y landed |
| `browser_renderer_linux_pre_exec_sandbox_gap_2026-07-28` | `src/runtime/runtime_process.c` | Source fixed; runtime evidence pending for browser renderer Linux pre-exec sandbox |
| `c_runtime_compile_gate_red_browser_renderer_selfcheck_2026-08-18` | `doc/08_tracking/bug/c_runtime_compile_gate_red_browser_renderer_selfcheck_2026-08-18.md` | C-runtime compile gate RED: rt_browser_renderer_namespace_selfcheck.c |
| `c_runtime_exclusion_analysis_2026-05-18` | `doc/08_tracking/bug/c_runtime_exclusion_analysis_2026-05-18.md` | C Runtime Exclusion Analysis |
| `c_runtime_string_concat_quadratic_2026-08-22` | `doc/08_tracking/bug/c_runtime_string_concat_quadratic_2026-08-22.md` | C runtime: `rt_string_concat` is a fresh malloc+memcpy per append (quadratic builder loops) |
| `context_pack_expands_input_blocks_required_check_2026-08-31` | `doc/08_tracking/bug/context_pack_expands_input_blocks_required_check_2026-08-31.md` | Context-pack tool expands its input; its guard is orphaned; the pair blocks every PR |
| `core_c_runtime_capsule_script_missing_runtime_contracts_2026-07-29` | `doc/08_tracking/bug/core_c_runtime_capsule_script_missing_runtime_contracts_2026-07-29.md` | `build-core-c-bootstrap-runtime-capsule.shs` fails: `simple_contract_check` provider moved |
| `cranelift_inline_len_heap_tag_space_collision_dict_closure_2026-09-06` | `doc/08_tracking/bug/cranelift_inline_len_heap_tag_space_collision_dict_closure_2026-09-06.md` | Cranelift `inline_runtime_len_value` conflates two heap-tag spaces: `.len()` on a closure returns a fabricated |
| `cross_module_collisions_debugconfig_and_pub_shell_entangled_2026-08-15` | `src/lib/nogc_sync_mut/io/process_ops.spl` | DebugConfig and public shell collisions too entangled to rename |
| `deployed_binary_reads_stdlib_from_its_build_worktree_2026-08-25` | `not the tree you are working in (2026-08-25)"` | The deployed binary reads `src/lib` from the worktree it was BUILT in |
| `deployed_simple_runtime_missing_blocks_mcdc_rt_hal_2026-08-25` | `doc/08_tracking/bug/deployed_simple_runtime_missing_blocks_mcdc_rt_hal_2026-08-25.md` | Deployed Simple Runtime Missing Blocks MC/DC/RT-HAL Implementation |
| `dict_struct_key_identity_keyed_copied_key_misses_2026-09-13` | `so a copied key silently misses"` | A Dict keyed by a struct is keyed by object identity |
| `directx_gpu_text_deferred_no_windows_host_2026-09-06` | `doc/08_tracking/bug/directx_gpu_text_deferred_no_windows_host_2026-09-06.md` | DirectX has no GPU text on either platform; deferred for want of a Windows D3D11 host |
| `draw_ir_runtime_queue_spec_unrelated_drift_2026-09-13` | `discovered while re-checking a different bug"` | `draw_ir_runtime_queue_spec.spl` has 2 unrelated failures |
| `dynamic_runtime_lane_dual_rt_definitions_2026-09-06` | `and an ABI seam shows"` | Dynamic-runtime lane links 509 rt_* twice (executable + .so) |
| `ed25519_sffi_argument_order_and_error_conflation_2026-08-21` | `doc/08_tracking/bug/ed25519_sffi_argument_order_and_error_conflation_2026-08-21.md` | Ed25519 SFFI argument order and error conflation |
| `file_io_spec_rt_check_file_path_unbacked_2026-09-01` | `doc/08_tracking/bug/file_io_spec_rt_check_file_path_unbacked_2026-09-01.md` | `file_io_spec.spl`: extern `rt_check_file_path` has no runtime backing |
| `formal_verification_2_0_execution_linkage_and_test_runtime` | `doc/08_tracking/bug/formal_verification_2_0_execution_linkage_and_test_runtime.md` | Formal Verification 2.0 execution-linkage and validation blockers |
| `global_sffi_ratchets_drift_and_expose_unhardened_families_2026-08-26` | `doc/08_tracking/bug/global_sffi_ratchets_drift_and_expose_unhardened_families_2026-08-26.md` | Global SFFI ratchets drift and expose unhardened families |
| `host_gpu_runtime_emit_payload_text_drops_hash_2026-07-08` | `doc/08_tracking/bug/host_gpu_runtime_emit_payload_text_drops_hash_2026-07-08.md` | Bug: `rt_host_gpu_queue_emit_payload_text` does not persist the emitted `payload_hash` (drain reads it back as |
| `hosted_wm_registry_text_field_boxing_2026-08-04` | `doc/08_tracking/bug/hosted_wm_registry_text_field_boxing_2026-08-04.md` | Hosted WM startup dies in browser-renderer teardown: text field read back as i64 (seed boxing) |
| `image_wrapper_close_needs_live_handle_fixture_2026-08-07` | `src/lib/nogc_sync_mut/io/image_sffi.spl` | Image/FileLock wrapper double-close on a genuinely-acquired handle has no test fixture |
| `io_runtime_file_write_resolves_to_retryless_twin_2026-09-06` | `doc/08_tracking/bug/io_runtime_file_write_resolves_to_retryless_twin_2026-09-06.md` | `std.io_runtime.file_write` resolves to a retryless twin — silent write failure into a missing directory |
| `layout_gpu_semantic_device_boundary_2026-07-31` | `src/lib/gc_async_mut/gpu/browser_engine/layout_paint.spl` | GPU layout semantic/device boundary only partially completed (bounded device slices) |
| `lib_nogc_sync_mut_behavioral_failures_2026-09-16` | `doc/08_tracking/bug/lib_nogc_sync_mut_behavioral_failures_2026-09-16.md` | lib nogc_sync_mut: behavioral/spec failures beyond trivial repair (22 specs RED) |
| `lib_nogc_sync_mut_missing_modules_2026-09-16` | `doc/08_tracking/bug/lib_nogc_sync_mut_missing_modules_2026-09-16.md` | lib nogc_sync_mut: specs reference modules/exports absent from src/lib (13 specs RED) |
| `lib_specs_import_133_modules_that_do_not_exist_2026-08-04` | `test/01_unit/lib/math/bignum/bignat_spec.spl` | 199 lib specs import 133 std.* modules that exist nowhere in the tree |
| `llvm_runtime_decls_duplicate_rt_eprintln_2026-09-13` | `doc/08_tracking/bug/llvm_runtime_decls_duplicate_rt_eprintln_2026-09-13.md` | LlvmBackend.compile_module() fails on any module: duplicate `rt_eprintln` declaration |
| `local_dict_list_push_silently_dropped_2026-08-31` | `doc/08_tracking/bug/local_dict_list_push_silently_dropped_2026-08-31.md` | Bare local dict-of-list `d[k].push(v)` silently drops the mutation (interpreter) |
| `map_for_each_missing_on_dict_2026-08-21` | `doc/08_tracking/bug/map_for_each_missing_on_dict_2026-08-21.md` | `Map.for_each` is not implemented on `dict` (array-only builtin) |
| `mcp_config_raw_source_launch_and_stale_startup_lib_2026-08-11` | `src/app/simple_lsp_mcp/main.spl` | MCP server family: obsolete source/SMF startup library deleted and guarded; POSIX T32 wrapper artifacts remain |
| `module_val_dict_export_unresolved_via_use_2026-09-01` | `doc/08_tracking/bug/module_val_dict_export_unresolved_via_use_2026-09-01.md` | Module-level `val` dict export is unresolved through `use module.{name}` / `use module.*` |
| `nested_array_element_bound_to_var_copies_2026-09-05` | `doc/08_tracking/bug/nested_array_element_bound_to_var_copies_2026-09-05.md` | Binding a nested-array element to a `var` copies it; writes through that binding are silently lost |
| `noalloc_collections_backed_by_growable_heap_array_2026-08-07` | `root cause stays open"` | `nogc_async_mut_noalloc/collections/*` claim ""no heap allocation"" but are backed by a real heap `[T]` array  |
| `persistent_vec_from_array_of_static_method_unresolved_2026-07-20` | `doc/08_tracking/bug/persistent_vec_from_array_of_static_method_unresolved_2026-07-20.md` | `PersistentVec.from_array` / `.of` unresolved as static methods (works for `.empty`/`.range`/`.repeat`) |
| `posix_gated_runtime_symbols_invisible_on_windows_2026-08-31` | `not `#if`"` | POSIX-gated runtime symbols ""invisible on Windows"" — the 90 is REFUTED; the real gap is file selection |
| `prevention_mock_deferred_arming_impossible_2026-08-07` | `src/lib/nogc_sync_mut/spec.spl` | std.spec prevent/prevent_at_most cannot defer arming; no module state across it examples |
| `production_gui_font_offload_runtime_readback_2026-06-23` | `doc/08_tracking/bug/production_gui_font_offload_runtime_readback_2026-06-23.md` | Bug: Production GUI font offload lacks runtime glyph readback |
| `pure_simple_ctype_perf_gap_2026-05-18` | `src/lib/common/ctype.spl` | Pure-Simple ctype predicates run 0.07x-0.46x of C under Cranelift with no inlining |
| `req_app_io_001_regex_sffi_migration_missing_2026-09-18` | `doc/08_tracking/bug/req_app_io_001_regex_sffi_migration_missing_2026-09-18.md` | REQ-APP-IO-001 regex safe-SFFI migration never landed (regex_sffi is a stub) |
| `return_type_result_mismatch_class_audit_2026-08-08` | `src/lib/common/validation.spl` | Non-Result declared return types whose bodies return Ok()/Err() remain in owned src after partial fix |
| `runtime_from_int_still_truncates_61bit_2026-08-17` | `was reverted` | `RuntimeValue::from_int` still truncates to 61 bits at HEAD — the fix landed |
| `rust_mmio_unit_test_blocked_by_runtime_export_drift_2026-08-26` | `doc/08_tracking/bug/rust_mmio_unit_test_blocked_by_runtime_export_drift_2026-08-26.md` | Rust MMIO unit test blocked by unrelated runtime export drift |
| `sffi_authority_census_ambient_call_gap_2026-08-24` | `doc/08_tracking/bug/sffi_authority_census_ambient_call_gap_2026-08-24.md` | SFFI authority census omits ambient raw calls |
| `sffi_contract_inventory_red_on_origin_main_2026-09-03` | `doc/08_tracking/bug/sffi_contract_inventory_red_on_origin_main_2026-09-03.md` | `push-sffi-v2-authority` is RED on unmodified `origin/main` (2026-09-03) |
| `sffi_ssh_aes256_gcm_decrypt_empty_failure_2026-08-27` | `doc/08_tracking/bug/sffi_ssh_aes256_gcm_decrypt_empty_failure_2026-08-27.md` | SSH AES-256-GCM SFFI decrypt collapses failure into an empty byte array |
| `sffi_torch_dynamic_facade_lexical_owner_gap_2026-08-27` | `doc/08_tracking/bug/sffi_torch_dynamic_facade_lexical_owner_gap_2026-08-27.md` | Dynamic Torch facade bypasses lexical raw-SFFI ownership |
| `sffi_u8_return_nil_and_cross_engine_len_2026-08-18` | `and `rt_bytes_alloc` length disagrees across engines"` | SFFI `-> [u8]` siblings: interpreter binds `nil` |
| `simple_frontend_profile_runtime_unavailable_2026-09-03` | `doc/08_tracking/bug/simple_frontend_profile_runtime_unavailable_2026-09-03.md` | Tiny frontend profiling unavailable in admitted release runtime |
| `simple_web_textarea_overlay_review_hard_stop_2026-07-27` | `doc/08_tracking/bug/simple_web_textarea_overlay_review_hard_stop_2026-07-27.md` | Simple Web textarea overlay review hard stop |
| `spec_run_fixed_cost_dominates_single_spec_runtime_2026-08-11` | `larger tax"` | Spec-run cost: daemon startup pays a full-tree lint pass; content-bound specs pay a separate |
| `spec_step_text_truncated_at_escaped_quote_2026-09-03` | `producing unparseable specs"` | Generated `step(""..."")` text is truncated at the first escaped quote |
| `spec_verdict_forgeable_from_example_name_2026-08-17` | `doc/08_tracking/bug/spec_verdict_forgeable_from_example_name_2026-08-17.md` | A spec file's pass/fail verdict is forgeable from an example's NAME |
| `spl_doctest_phase_emits_no_verdict_line_on_abort_2026-08-25` | `doc/08_tracking/bug/spl_doctest_phase_emits_no_verdict_line_on_abort_2026-08-25.md` | SPL-doctest phase exits non-zero with NO verdict line when a source file fails to compile |
| `sql_stmt_cache_dict_get_never_hits_2026-07-20` | `doc/08_tracking/bug/sql_stmt_cache_dict_get_never_hits_2026-07-20.md` | SQL `StatementCache.get_or_prepare` never hits cache — `Dict.get()` present-key landmine |
| `sqlite_sffi_execute_close_return_code_contract_mismatch_2026-08-08` | `doc/08_tracking/bug/sqlite_sffi_execute_close_return_code_contract_mismatch_2026-08-08.md` | sqlite_sffi return-code checks match the Rust seed but are inverted for the native C runtime |
| `std_collection_helpers_module_missing_2026-09-01` | `doc/08_tracking/bug/std_collection_helpers_module_missing_2026-09-01.md` | `std.collection_helpers` module does not exist — spec covers 33+ unimplemented functions |
| `std_crypto_sha1_missing_hex_upper_2026-07-20` | `doc/08_tracking/bug/std_crypto_sha1_missing_hex_upper_2026-07-20.md` | `std.crypto.sha1` (array-based) lacks `sha1_hex_upper` present in the sibling `std.common.crypto.sha1` (text-b |
| `std_spec_package_shadows_file_print_summary_2026-07-17` | `get_exit_code` | Bug: `use std.spec.{print_summary |
| `std_suite_failures_are_unbuilt_features_2026-09-20` | `plus one real concurrency defect"` | Triage: the 9 `test/01_unit/std` failures are unimplemented features |
| `stdlib_spl_edits_not_live_under_bin_simple_run_2026-08-08` | `doc/08_tracking/bug/stdlib_spl_edits_not_live_under_bin_simple_run_2026-08-08.md` | `bin/simple run` resolves `std.*`/`lib.*` to a stale bundled stdlib — on-disk edits are silently ignored |
| `string_char_code_at_o_index_fallback_on_non_ascii_text_2026-08-28` | `doc/08_tracking/bug/string_char_code_at_o_index_fallback_on_non_ascii_text_2026-08-28.md` | `text.char_code_at(i)` is O(i) on any string containing a non-ASCII byte at or before `i` |
| `sub_sup_line_box_strut_contradiction_2026-09-14` | `and the obvious strut fix contradicts Chrome (2026-09-14)"` | `<sub>`/`<sup>` line box is the inline's own height |
| `task_spawn_runtime_pool_spec_semantic_fail_2026-07-05` | `doc/08_tracking/bug/task_spawn_runtime_pool_spec_semantic_fail_2026-07-05.md` | task_spawn_runtime_pool_spec.spl: semantic error — cannot assign field on non-object value |
| `text_literal_brace_run_swallows_following_concatenation_2026-09-05` | `swallowing an enclosed `+` concatenation"` | A non-parseable `{...}` interpolation body silently falls back to literal text |
| `text_to_bytes_method_missing_on_text_receiver_2026-09-06` | `doc/08_tracking/bug/text_to_bytes_method_missing_on_text_receiver_2026-09-06.md` | `""lit"".to_bytes()` — method not found on `text` |
| `theme_snapshot_catalog_review_hard_stop_2026-07-27` | `src/lib/common/ui/theme_package_wire.spl` | theme snapshot catalog design fail-closed after three exhausted review cycles |
| `tierless_std_js_imports_resolve_to_root_lib_js_not_common_2026-08-01` | `never to the importer's own tier"` | Tier-less `use std.js.*` resolves to `src/lib/js/` |
| `todo_db_description_drift_false_positive_2026-09-12` | `defeating literal-text ""marker gone"" detection"` | `todo_db.sdn` rows can point at a real line whose comment was reworded to a different topic |
| `top_level_array_index_assign_in_loop_silently_dropped_2026-08-25` | `doc/08_tracking/bug/top_level_array_index_assign_in_loop_silently_dropped_2026-08-25.md` | Module-level `arr[i] = arr[i] + 1` inside a top-level loop is silently dropped (2026-08-25) |
| `u8_cast_push_yields_unpacked_byte_array_2026-09-06` | `doc/08_tracking/bug/u8_cast_push_yields_unpacked_byte_array_2026-09-06.md` | BUG: `push(x as u8)` grows a `[u8]` whose storage is not byte-packed |
| `web_css_package_authority_adapter_2026-07-27` | `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl` | generate_package_authoritative_css emitted literal n and dropped traffic-light ::before |
| `web_render_backend_api_spec_perf_2026-06-05` | `src/lib/gc_async_mut/ui/web_render_pixel_backend.spl` | Web render backend API spec exceeds the test runner's per-spec perf threshold |
| `web_ui_facade_lib_compile_error_node_types_2026-09-16` | `doc/08_tracking/bug/web_ui_facade_lib_compile_error_node_types_2026-09-16.md` | web_ui facade spec blocked: lib compile error in common/web/node_types.spl |
| `wm_scene_web_lane_layout_scrambled_2026-07-03` | `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl` | backdrop-filter blur unimplemented so WM glass shows sharp detail instead of frosted |
| `zstd_fse_compressed_block_deferred_2026-06-15` | `doc/08_tracking/bug/zstd_fse_compressed_block_deferred_2026-06-15.md` | zstd_fse_compressed_block_deferred_2026-06-15 |

### Interpreter / JIT

| Bug | File | Summary |
|---|---|---|
| `browser_session_js_lane_inert_under_test_interpreter_2026-08-15` | `doc/08_tracking/bug/browser_session_js_lane_inert_under_test_interpreter_2026-08-15.md` | BrowserSession JS script lane inert under the test interpreter (2026-08-15) |
| `coalesce_optional_accessor_sentinel_value_eaten_jit_2026-08-17` | `doc/08_tracking/bug/coalesce_optional_accessor_sentinel_value_eaten_jit_2026-08-17.md` | `xs.first() ?? d` returns `d` when the real element is 3 — JIT only |
| `compiler_interpreter_integration_real_gaps_found_2026-09-06` | `doc/08_tracking/bug/compiler_interpreter_integration_real_gaps_found_2026-09-06.md` | Five real compiler/interpreter contract gaps found while modernizing the integration scaffold |
| `damage_budget_slice_interpreter_timeout_2026-08-12` | `doc/08_tracking/bug/damage_budget_slice_interpreter_timeout_2026-08-12.md` | Progressive damage slicer interpreter timeout — 2026-08-12 |
| `engine2d_interpreter_span_kernel_marshalling_perf_gap_2026-08-14` | `doc/08_tracking/bug/engine2d_interpreter_span_kernel_marshalling_perf_gap_2026-08-14.md` | engine2d interpreter span kernels 180–300× slower than C due to per-element marshalling |
| `engine_specs_spec_runner_interpreter_divergence_2026-09-16` | `doc/08_tracking/bug/engine_specs_spec_runner_interpreter_divergence_2026-09-16.md` | Engine lib specs: spec-runner interpreter diverges from `run` (JIT) path |
| `gui_window_caller_frame_silent_interp_fallback_2026-08-06` | `doc/08_tracking/bug/gui_window_caller_frame_silent_interp_fallback_2026-08-06.md` | Silent interpreter fallback poisons entire callee tree when engine is called from gui_window frame |
| `interp_debug_session_remove_breakpoint_lies_and_set_state_frozen_2026-08-18` | `doc/08_tracking/bug/interp_debug_session_remove_breakpoint_lies_and_set_state_frozen_2026-08-18.md` | `SessionManager.remove_breakpoint` returns `true` while the breakpoint stays armed; `set_state` is frozen (int |
| `interp_dict_in_struct_copy_corruption_2026-07-03` | `doc/08_tracking/bug/interp_dict_in_struct_copy_corruption_2026-07-03.md` | Interpreter: Dict values corrupted inside struct under copy-return semantics |
| `interp_local_shadows_cross_module_global_arm_body_2026-08-24` | `doc/08_tracking/bug/interp_local_shadows_cross_module_global_arm_body_2026-08-24.md` | Interpreter: a function-local binding writes through to a same-named module-global in another module (2026-08- |
| `interp_mcp_taskinfo_lifecycle_mutations_all_lost_2026-08-18` | `doc/08_tracking/bug/interp_mcp_taskinfo_lifecycle_mutations_all_lost_2026-08-18.md` | MCP `TaskManager` lifecycle is a complete no-op in the interpreter — results and error text silently discard |
| `interp_module_val_struct_zeroed_as_call_arg_2026-09-01` | `doc/08_tracking/bug/interp_module_val_struct_zeroed_as_call_arg_2026-09-01.md` | A module-level `val` holding a struct is zero-initialized when passed as a call argument |
| `interp_optimizer_step_writes_lost_training_silently_produces_unchanged_weights_2026-08-18` | `doc/08_tracking/bug/interp_optimizer_step_writes_lost_training_silently_produces_unchanged_weights_2026-08-18.md` | Optimizer `step()` writes to `param.value` are lost in the interpreter — training silently produces UNCHANGE |
| `interp_option_dict_return_erased_2026-07-16` | `V>?` return erased to nil in live-interpreted compiler context"` | Seed interpreter: `-> Dict<K |
| `interp_optional_chain_on_method_result_collapses_to_none_2026-08-18` | `doc/08_tracking/bug/interp_optional_chain_on_method_result_collapses_to_none_2026-08-18.md` | `?.` chain on a successful optional collapses to None (interpreter) |
| `interp_result_question_operator_wrapper_unmatchable_2026-09-01` | `doc/08_tracking/bug/interp_result_question_operator_wrapper_unmatchable_2026-09-01.md` | `?` on a Result inside a one-line wrapper yields a value matching neither Ok nor Err (interpreter) |
| `interp_str_substring_nested_call_dispatch_2026-08-19` | `doc/08_tracking/bug/interp_str_substring_nested_call_dispatch_2026-08-19.md` | Interpreter: `substring` dispatch fails on chained str receiver with nested call argument |
| `interp_tiered_jit_hotfunction_compiled_and_call_count_lost_2026-08-18` | `recompilation is unbounded"` | `TieredJitManager` never tiers up in the interpreter — `compiled` and `call_count` writes are lost |
| `interp_trait_slot_receiver_reboxed_per_call_mutation_loss_2026-07-07` | `losing field mutations"` | Interpreter: `me` method called through a `Trait?`-typed module slot re-boxes the receiver per call |
| `interpreter_fd_ownership_private_module_globals_not_linked_2026-08-12` | `doc/08_tracking/bug/interpreter_fd_ownership_private_module_globals_not_linked_2026-08-12.md` | Interpreter does not link FD-ownership private module globals |
| `interpreter_ffi_bridge_legacy_syntax_blocks_source_check_2026-08-26` | `doc/08_tracking/bug/interpreter_ffi_bridge_legacy_syntax_blocks_source_check_2026-08-26.md` | Interpreter FFI bridge legacy syntax blocks source check |
| `interpreter_float_division_by_zero_raises_instead_of_nan_2026-08-18` | `doc/08_tracking/bug/interpreter_float_division_by_zero_raises_instead_of_nan_2026-08-18.md` | Interpreter float division `0.0 / 0.0` raises instead of producing NaN |
| `interpreter_i64_dict_tuple_compare_and_me_fn_mutation_2026-08-31` | `doc/08_tracking/bug/interpreter_i64_dict_tuple_compare_and_me_fn_mutation_2026-08-31.md` | Two interpreter defects found while building the textual BM25 side-index |
| `interpreter_import_shadows_module_own_function_2026-09-02` | `doc/08_tracking/bug/interpreter_import_shadows_module_own_function_2026-09-02.md` | Interpreter resolves a module's own function to an unrequested import |
| `interpreter_lane_raw_boundaries_abort_instead_of_failing_closed_2026-09-05` | `doc/08_tracking/bug/interpreter_lane_raw_boundaries_abort_instead_of_failing_closed_2026-09-05.md` | Interpreter lane: three raw SFFI boundaries abort (or fabricate) instead of returning their documented failure |
| `interpreter_missing_rt_volatile_externs_blocks_ivshmem_specs_2026-08-15` | `doc/08_tracking/bug/interpreter_missing_rt_volatile_externs_blocks_ivshmem_specs_2026-08-15.md` | Interpreter has no rt_volatile_read/write_* externs — every ivshmem lane untestable under `simple test` |
| `interpreter_owned_method_call_component_attribution_2026-09-13` | `950 ns of an interpreted class-method call actually goes"` | Where the 2 |
| `interpreter_per_call_cost_dominates_loop_bodies_2026-09-13` | `doc/08_tracking/bug/interpreter_per_call_cost_dominates_loop_bodies_2026-09-13.md` | Every loop-body shape above the generic floor is dominated by one call |
| `interpreter_raw_array_and_glob_import_gaps_2026-08-21` | `doc/08_tracking/bug/interpreter_raw_array_and_glob_import_gaps_2026-08-21.md` | Interpreter gaps behind the lib/native failing-spec cluster (2026-08-21) |
| `interpreter_struct_assignment_deep_copies_class_fields_2026-09-16` | `breaking shared state"` | Interpreter: struct assignment deep-copies class fields |
| `interpreter_unresolved_enum_import_fails_open_symbolic_match_2026-08-18` | `doc/08_tracking/bug/interpreter_unresolved_enum_import_fails_open_symbolic_match_2026-08-18.md` | Interpreter: unresolved enum import fails open — variant access and match work symbolically |
| `interpreter_val_bound_chained_method_call_e3009_2026-08-21` | `2).len()` fails with E3009 while the same chain inline succeeds"` | `val x = s.slice(0 |
| `interpreter_val_decl_in_loop_body_declines_every_matcher_2026-09-13` | `doc/08_tracking/bug/interpreter_val_decl_in_loop_body_declines_every_matcher_2026-09-13.md` | One `val` in a while-loop body declines every native matcher: 271x |
| `interpreter_vec16u8_extern_rejects_u8_fields_2026-09-02` | `doc/08_tracking/bug/interpreter_vec16u8_extern_rejects_u8_fields_2026-09-02.md` | Every `Vec16u8`-taking SIMD extern is uncallable from the interpreter |
| `is_dir_returns_false_for_every_path_in_interpreted_module_2026-09-02` | `doc/08_tracking/bug/is_dir_returns_false_for_every_path_in_interpreted_module_2026-09-02.md` | `is_dir` answers false for every real path inside an interpreter-fallback module (and for any backslash path e |
| `jit_array_text_builtin_dispatch_2026-07-28` | `doc/08_tracking/bug/jit_array_text_builtin_dispatch_2026-07-28.md` | JIT array/text builtin dispatch defects (2026-07-28) |
| `jit_co_compiled_definition_ambiguity_debt_2026-09-15` | `doc/08_tracking/bug/jit_co_compiled_definition_ambiguity_debt_2026-09-15.md` | JIT co-compiled definition ambiguity debt — native-build blocker chain |
| `jit_dispatch_worklist_2026-07-29` | `rt_string_reverse does not exist"` | JIT builtin-method dispatch worklist: text.reverse arm is a no-op |
| `jit_engine2d_static_create_silent_truncate_2026-09-02` | `doc/08_tracking/bug/jit_engine2d_static_create_silent_truncate_2026-09-02.md` | JIT: direct `Engine2D.create_with_backend_fast` from flat main silently truncates (trait dispatch) |
| `jit_inline_lambda_text_return_raw_handle_2026-09-13` | `doc/08_tracking/bug/jit_inline_lambda_text_return_raw_handle_2026-09-13.md` | Bug: JIT-compiled inline lambda returning `text` yields a raw handle integer |
| `jit_instantiator_spec_remaining_defect_cluster_2026-09-01` | `doc/08_tracking/bug/jit_instantiator_spec_remaining_defect_cluster_2026-09-01.md` | `jit_instantiator_spec.spl`: 7 remaining failures after `default()` fix — distinct interpreter/product defec |
| `jit_lowering_clamp_f_engine_color_2026-07-02` | `src/lib/common/engine/color.spl` | JIT lowering cannot resolve a nested fn inside an impl method (Unknown variable: clamp_f) |
| `jit_module_level_u8_array_index_push_corruption_2026-08-18` | `doc/08_tracking/bug/jit_module_level_u8_array_index_push_corruption_2026-08-18.md` | Codegen (JIT) lane: module-level `val [u8]` indexed then `.push()`-ed reads back corrupted |
| `jit_module_val_array_indexing_15x_slow_2026-08-18` | `doc/08_tracking/bug/jit_module_val_array_indexing_15x_slow_2026-08-18.md` | Arrays sourced from a module-level `val` index 15x slower in the JIT — hoisting does not help |
| `jit_optional_unwrap_sugar_boxed_some_not_unboxed_2026-08-17` | `doc/08_tracking/bug/jit_optional_unwrap_sugar_boxed_some_not_unboxed_2026-08-17.md` | JIT: `if val x = opt` sugar and `??` leak the raw boxed-Some representation |
| `jit_qualified_module_call_entry_local_unresolved_2026-08-18` | `doc/08_tracking/bug/jit_qualified_module_call_entry_local_unresolved_2026-08-18.md` | Qualified `use prov` + `prov.f()` in entry module still fails codegen (GlobalLoad 'prov') |
| `jit_test_suite_blind_spot_2026-07-30` | `so JIT-only divergences are structurally invisible to it"` | Spec suite runs only one engine |
| `jit_to_i32_returns_zero_and_leaks_mistagged_value_2026-08-26` | `doc/08_tracking/bug/jit_to_i32_returns_zero_and_leaks_mistagged_value_2026-08-26.md` | JIT `to_i32()` returns 0 for characters and leaks mis-tagged values for literals |
| `js_subset_interpreter_limitations_2026-06-30` | `src/lib/gc_async_mut/web/browser_session_modules.spl` | Browser-session JS subset interpreter gaps worked around in the ES-module transform instead of the engine |
| `lib_common_interpreter_typesystem_defect_cluster_2026-09-01` | `doc/08_tracking/bug/lib_common_interpreter_typesystem_defect_cluster_2026-09-01.md` | `test/01_unit/lib/common/` triage: interpreter type-system defect cluster |
| `lint_dejits_whole_program_span_struct_collision_2026-08-18` | `doc/08_tracking/bug/lint_dejits_whole_program_span_struct_collision_2026-08-18.md` | `simple lint` runs the entire pure-Simple linter in the tree-walking interpreter (two stacked de-JIT causes) |
| `lint_jit_abort_on_src_app_sj_2026-09-05` | `doc/08_tracking/bug/lint_jit_abort_on_src_app_sj_2026-09-05.md` | `bin/simple lint` aborts (SIGABRT) in cranelift `finalize_definitions` on `src/app/sj/*.spl` |
| `lint_jit_segv_discriminator_is_the_spec_filename_2026-09-13` | `doc/08_tracking/bug/lint_jit_segv_discriminator_is_the_spec_filename_2026-09-13.md` | `simple lint` SIGSEGVs in the JIT lane for any file whose basename ends `_spec` — content-independent |
| `local_skip_on_interpreter_shadow_discards_block_false_green_2026-08-17` | `doc/08_tracking/bug/local_skip_on_interpreter_shadow_discards_block_false_green_2026-08-17.md` | 19 spec files define a local `skip_on_interpreter` that DISCARDS its block and reports PASS |
| `mem_guard_owner_attribution_trap_report_missing_2026-08-05` | `src/compiler_rust/compiler/src/interpreter_extern/mem_guard.rs` | M2 guard-page SIGSEGV trap produces no owner-attribution report on either backend |
| `memory_retention_compiler_and_interpreter_2026-08-21` | `doc/08_tracking/bug/memory_retention_compiler_and_interpreter_2026-08-21.md` | Compiler / interpreter memory retention — measured survey |
| `parse_shard_warmup_pinned_to_one_worker_2026-10-19` | `serializing the parse cache warm-up (interpreter-mode OOM evidence predates the compiled parse shard route)"` | Product and transcribed lanes pin SIMPLE_PARSE_SHARD_MAX=1 on every host |
| `pem_decode_superlinear_and_jit_dropped_2026-08-05` | `and the whole module never JIT-compiles"` | PEM/base64 decode is superlinear |
| `secure_memory_interpreter_raw_pointer_aliasing_2026-08-24` | `doc/08_tracking/bug/secure_memory_interpreter_raw_pointer_aliasing_2026-08-24.md` | Secure-memory interpreter raw-pointer aliasing |
| `seed_interp_mut_out_param_writeback_and_u8_data_ptr_2026-08-31` | `doc/08_tracking/bug/seed_interp_mut_out_param_writeback_and_u8_data_ptr_2026-08-31.md` | Seed interpreter: `&mut` out-param writeback loss and `[u8].data_ptr()` pointing at boxed value cells |
| `seed_interpreter_segv_on_undefined_function_call_2026-09-12` | `doc/08_tracking/bug/seed_interpreter_segv_on_undefined_function_call_2026-09-12.md` | `simple run` SEGVs on a call to an undefined function (the `compile` lane diagnoses it) |
| `seed_jit_cannot_resolve_text_dot_from_char_code_2026-09-04` | `killing any `simple run` that calls slang's manifest parser"` | Seed JIT cannot resolve `text_dot_from_char_code` |
| `seed_jit_some_constructor_corrupts_value_2026-09-13` | `doc/08_tracking/bug/seed_jit_some_constructor_corrupts_value_2026-09-13.md` | Seed JIT: the explicit `Some(x)` optional constructor produces a corrupt value |
| `seed_jit_wide_literal_match_u64_misevaluates_2026-08-28` | `doc/08_tracking/bug/seed_jit_wide_literal_match_u64_misevaluates_2026-08-28.md` | Seed JIT: literal-arm `match` on u64 mis-evaluates in a stdlib module (2026-08-28) |
| `simple_mcp_windows_source_startup_blocked_by_transport_jit_and_shared_stderr_2026-09-09` | `doc/08_tracking/bug/simple_mcp_windows_source_startup_blocked_by_transport_jit_and_shared_stderr_2026-09-09.md` | Simple MCP Windows source startup is not concurrency-safe and cannot be verified |
| `spec_cross_module_eval_warnings_not_observed_2026-08-05` | `src/compiler/10.frontend/core/interpreter/eval.spl` | A spec importing eval_tables and eval separately reads eval_warnings back as 0 after a |

### Seed

| Bug | File | Summary |
|---|---|---|
| `coverage_probe_plan_skips_struct_method_decisions_2026-08-15` | `src/compiler_rust/compiler/src/mir/lower/lowering_coverage.rs` | Coverage probe plan skips struct-method decisions; SIMPLE_COVERAGE on run writes nothing |
| `deployed_seed_binary_missing_var_roots_cache_fix_2026-09-13` | `doc/08_tracking/bug/deployed_seed_binary_missing_var_roots_cache_fix_2026-09-13.md` | Deployed seed binary predates `VAR_ROOTS_CACHE`; `variants/__init__.spl` opened 76x per lint run |
| `deployed_seed_resolves_stdlib_from_foreign_worktree_2026-08-20` | `doc/08_tracking/bug/deployed_seed_resolves_stdlib_from_foreign_worktree_2026-08-20.md` | Deployed seed resolves `src/lib` stdlib from a FOREIGN worktree first |
| `generic_struct_field_untagged_payload_seed_2026-08-21` | `doc/08_tracking/bug/generic_struct_field_untagged_payload_seed_2026-08-21.md` | Generic fn returning scalar `T` yields untagged payload (value * 8) on the seed (2026-08-21) |
| `iterator_collect_generic_restoration_2026-07-17` | `src/compiler_rust/lib/std/src/core/list.spl` | Iterator.collect loses its generic type parameter and needs restoration across the three vec types |
| `lane_seed_unbuildable_duplicate_inline_int_bits_salvage_2026-08-18` | `doc/08_tracking/bug/lane_seed_unbuildable_duplicate_inline_int_bits_salvage_2026-08-18.md` | Lane-local Rust seed unbuildable: REBASE91 salvage re-introduced a stale `INLINE_INT_BITS` block |
| `lint_intermittent_segv_on_deployed_seed_2026-09-13` | `doc/08_tracking/bug/lint_intermittent_segv_on_deployed_seed_2026-09-13.md` | `simple lint <file>` intermittently SEGVs (rc 139) on the deployed seed |
| `llvm_sys_pinned_to_18x_blocks_newest_msvc_llvm_2026-08-09` | `src/compiler_rust/compiler/Cargo.toml` | llvm-sys pinned to 18.x prevents building against newer MSVC-built LLVM |
| `origin_main_seed_unbuildable_duplicate_heap_counter_symbols_2026-08-16` | `doc/08_tracking/bug/origin_main_seed_unbuildable_duplicate_heap_counter_symbols_2026-08-16.md` | `origin/main` seed is unbuildable — duplicate `rt_heap_*_bytes` symbols; `check-seed-builds-push.shs` cannot |
| `perf_spec_binary_resolution_falls_through_to_deployed_seed_2026-09-13` | `doc/08_tracking/bug/perf_spec_binary_resolution_falls_through_to_deployed_seed_2026-09-13.md` | A perf spec's binary resolution falls through to the deployed seed in directory mode |
| `phase_profile_flag_unusable_seed_missing_rt_heap_registry_count_2026-07-20` | `doc/08_tracking/bug/phase_profile_flag_unusable_seed_missing_rt_heap_registry_count_2026-07-20.md` | Phase-profile tracing breaks every rv32 firmware build: `rt_heap_registry_count` missing from the seed |
| `renderdoc_seed_sigbus_cross_module_call_2026-09-13` | `doc/08_tracking/bug/renderdoc_seed_sigbus_cross_module_call_2026-09-13.md` | Seed SIGBUS (rc 138) on a cross-module call in the renderdoc tooling — 2026-09-13 |
| `rt_browser_renderer_externs_missing_in_rust_seed_2026-08-19` | `doc/08_tracking/bug/rt_browser_renderer_externs_missing_in_rust_seed_2026-08-19.md` | `rt_browser_renderer_*` externs unimplemented in the Rust seed interpreter |
| `rt_str_hash_rust_seed_djb2_divergence_2026-09-01` | `not FNV-1a — third lane divergence"` | Rust seed's `rt_str_hash`/`rt_hash_text` is djb2 |
| `rust_seed_parser_behind_main_grammar_blocks_simple_test_2026-09-05` | `so `simple test` cannot run on this host"` | The Rust seed's parser is behind main's grammar |
| `seed_array_local_alias_cow_bypass_2026-07-17` | `doc/08_tracking/bug/seed_array_local_alias_cow_bypass_2026-07-17.md` | Seed (Rust interpreter): arrays alias on local-bind despite Arc/COW design |
| `seed_build_guard_checks_only_bin_target_no_link_2026-08-17` | `doc/08_tracking/bug/seed_build_guard_checks_only_bin_target_no_link_2026-08-17.md` | `check-seed-builds-push.shs` verifies only the `--bin simple` target and never links — the Rust test suite c |
| `seed_builds_guard_selftest_commits_into_real_repo_2026-08-19` | `doc/08_tracking/bug/seed_builds_guard_selftest_commits_into_real_repo_2026-08-19.md` | seed-builds guard selftest commits into the REAL repo and corrupts the index |
| `seed_builtin_option_name_heuristic_breaks_user_option_enum_2026-08-16` | `so a user-declared `enum Option` is misrouted"` | Seed HIR lowering: the builtin-`Option` exception is keyed on a NAME |
| `seed_enum_variant_arity_unchecked_2026-11-01` | `src/compiler_rust` | Rust seed accepts enum-variant construction with extra payloads (5 for a 4-field variant) instead of rejecting |
| `seed_helper_return_type_mistyped_as_tuple_2026-08-21` | `breaking every downstream field access"` | Seed mis-types a `-> [text]` helper's result |
| `seed_http_server_handle_connection_dispatch_2026-09-04` | `doc/08_tracking/bug/seed_http_server_handle_connection_dispatch_2026-09-04.md` | `SimpleHttpServer` accepts a connection and then dies: `handle_connection` not found on type `dict` |
| `seed_indexed_field_assign_complex_receiver_unisolated_2026-08-31` | `doc/08_tracking/bug/seed_indexed_field_assign_complex_receiver_unisolated_2026-08-31.md` | New occurrence of the OPEN indexed-field-assignment limitation: FAT32 `file_generations` (2026-08-31) |
| `seed_method_find_on_nested_substring_call_2026-08-25` | `doc/08_tracking/bug/seed_method_find_on_nested_substring_call_2026-08-25.md` | Seed: `.find()` on a nested `substring()` result fails to resolve — 2026-08-25 |
| `seed_optional_query_comparison_divergence_2026-08-16` | `not bool; module-private `val` imports resolve inconsistently"` | Seed interpreter: `.?` operator yields value-or-nil |
| `seed_parser_accepts_match_keyword_as_identifier_2026-07-27` | `doc/08_tracking/bug/seed_parser_accepts_match_keyword_as_identifier_2026-07-27.md` | Seed parser accepts `match` keyword as an identifier — divergence detonates at bootstrap Stage 4 |
| `seed_per_call_env_rebuild_o_globals_regression_2026-08-21` | `doc/08_tracking/bug/seed_per_call_env_rebuild_o_globals_regression_2026-08-21.md` | Seed interpreter rebuilds the whole callee env per call (O(module globals)) |
| `seed_rebuild_10_12_breaks_instance_method_dispatch_object_receiver_2026-08-18` | `doc/08_tracking/bug/seed_rebuild_10_12_breaks_instance_method_dispatch_object_receiver_2026-08-18.md` | Shared seed rebuilt 2026-08-18 10:12 breaks ALL instance-method dispatch — receiver types as `object` |
| `seed_result_err_shorthand_closure_segv_2026-09-12` | `doc/08_tracking/bug/seed_result_err_shorthand_closure_segv_2026-09-12.md` | Seed segfaults on `Result` Err + shorthand-closure projection (`.map(_.field)`) |
| `seed_return_bare_value_next_line_ambiguity_2026-07-31` | `src/compiler_rust/parser/src/stmt_parsing/jump.rs` | `return` with its value entirely on the next line fails with UnexpectedToken expected |
| `seed_segv_calling_newly_added_stdlib_function_2026-09-02` | `doc/08_tracking/bug/seed_segv_calling_newly_added_stdlib_function_2026-09-02.md` | Rust seed SEGVs when calling a NEWLY ADDED function in an existing stdlib module |
| `seed_static_method_default_param_value_wrong_2026-09-13` | `not the declared value"` | Seed interpreter: static-method default parameter fills the constant 3 |
| `seed_stdlib_resolves_build_time_repo_root_before_cwd_2026-08-24` | `doc/08_tracking/bug/seed_stdlib_resolves_build_time_repo_root_before_cwd_2026-08-24.md` | Seed resolves `use std.*` from its BUILD-TIME repo root before the process cwd |
| `spec_to_be_true_to_be_false_seed_intrinsic_gap_2026-07-02` | `doc/08_tracking/bug/spec_to_be_true_to_be_false_seed_intrinsic_gap_2026-07-02.md` | Bug: `expect(x).to_be_true()` / `.to_be_false()` fail with ""method not found on type bool"" |
| `windows_stripped_seed_binary_blinds_symbol_guards_2026-09-02` | `doc/08_tracking/bug/windows_stripped_seed_binary_blinds_symbol_guards_2026-09-02.md` | Windows: the stripped `bin/simple.exe` blinds every symbol-table guard |

### Tester

| Bug | File | Summary |
|---|---|---|
| `light_test_daemon_lane_slower_than_direct_after_shell_spawn_fix_2026-09-13` | `doc/08_tracking/bug/light_test_daemon_lane_slower_than_direct_after_shell_spawn_fix_2026-09-13.md` | Light test-daemon lane is slower than the direct lane even after removing all `/bin/sh` spawns from `daemon_lo |
| `light_test_daemon_serializes_concurrent_test_invocations_2026-08-21` | `doc/08_tracking/bug/light_test_daemon_serializes_concurrent_test_invocations_2026-08-21.md` | Light test daemon serializes all concurrent `bin/simple test` invocations |
| `lint_spipe005_rejects_assert_true_family_2026-07-27` | `doc/08_tracking/bug/lint_spipe005_rejects_assert_true_family_2026-07-27.md` | SPIPE005 does not recognize `assert_true`/`assert_false` as assertions — contradicts the testing rule |
| `seed_test_runner_unusable_on_windows_false_outer_bound_timeout_2026-09-13` | `doc/08_tracking/bug/seed_test_runner_unusable_on_windows_false_outer_bound_timeout_2026-09-13.md` | Seed `bin/simple test` cannot derive its own executable identity on Windows: `child-spawn-failure` unless `SIM |
| `spipe005_residual_assertion_free_examples_2026-08-01` | `src/compiler/90.tools/lint/_LintMain/traceability_and_assertions.spl` | SPIPE005 still fires 1790 times across 196 files for assertion-free SPipe examples |
| `spipe_lacks_context_mode_chunking_and_surfaces_2026-08-31` | `stemming and exec surfaces (2026-08-31)"` | SPipe knowledge provider lacks context-mode's chunking |
| `spipe_streaming_sha_interpreter_value_array_copy_timeout_2026-08-25` | `doc/08_tracking/bug/spipe_streaming_sha_interpreter_value_array_copy_timeout_2026-08-25.md` | SPipe streaming SHA interpreter verification exceeds budget |
| `sspec_hollow_expect_clobbers_failure_message_2026-08-19` | `doc/08_tracking/bug/sspec_hollow_expect_clobbers_failure_message_2026-08-19.md` | sspec: hollow-expect provisional text clobbers real failure message (2026-08-19) |
| `sspec_no_dir_wide_prevention_scope_2026-08-07` | `src/lib/nogc_sync_mut/spec.spl` | SSpec has no per-directory config hook so directory-wide prevention-mock scope is |
| `sspec_simple_check_describe_it_parser_2026-06-28` | `doc/08_tracking/bug/sspec_simple_check_describe_it_parser_2026-06-28.md` | Bug: `bin/simple check` rejects SSpec `describe`/`it` DSL files |
| `test_runner_exits_zero_on_failed_spec_2026-08-21` | `doc/08_tracking/bug/test_runner_exits_zero_on_failed_spec_2026-08-21.md` | `bin/simple test` exits 0 while its own verdict reports failed=1 |
| `test_runner_fixed_session_cost_2026-08-21` | `doc/08_tracking/bug/test_runner_fixed_session_cost_2026-08-21.md` | `simple test <dir>` pays ~400s of fixed cost before running any test |
| `test_runner_in_development_reporting_and_db_persist_2026-08-23` | `breaks total conservation` | In-development reporting mislabels neutralised specs |
| `test_runner_never_exits_after_summary_post_run_db_report_2026-08-18` | `doc/08_tracking/bug/test_runner_never_exits_after_summary_post_run_db_report_2026-08-18.md` | `simple test <dir>` prints its complete summary and then never exits (post-run DB/report phase) |
| `test_runner_peak_rss_needs_child_rusage_extern_2026-08-17` | `doc/08_tracking/bug/test_runner_peak_rss_needs_child_rusage_extern_2026-08-17.md` | Supervised test runner cannot report peak RSS — no child-rusage extern exists |
| `test_runner_reports_only_last_failure_per_example_2026-08-04` | `hiding earlier assertion failures"` | Runner reports only the LAST failure per example |
| `test_runner_spins_at_100pct_after_summary_2026-08-18` | `doc/08_tracking/bug/test_runner_spins_at_100pct_after_summary_2026-08-18.md` | `bin/simple test` keeps one thread at 100% CPU after printing its final summary |
| `test_runner_windows_child_binary_stale_fallback_2026-09-01` | `not the invoking binary"` | `simple test` on Windows silently runs specs on a STALE `bin/simple` |

### Other (apps, tools)

| Bug | File | Summary |
|---|---|---|
| `admit_is_a_hard_keyword_unusable_as_identifier_2026-08-21` | `doc/08_tracking/bug/admit_is_a_hard_keyword_unusable_as_identifier_2026-08-21.md` | `admit` is a hard keyword and cannot name a function |
| `aes128_gcm_verification_blocked_by_env_access_parse_2026-08-25` | `doc/08_tracking/bug/aes128_gcm_verification_blocked_by_env_access_parse_2026-08-25.md` | AES-128-GCM verification blocked by hosted environment parse |
| `aliased_use_import_does_not_bind_in_transitive_module_2026-08-10` | `doc/08_tracking/bug/aliased_use_import_does_not_bind_in_transitive_module_2026-08-10.md` | Aliased `use ... { x as y }` (and qualified `use m` + `m.f()`) do not bind in the CODEGEN lane |
| `allow_reserved_as_hard_keyword_2026-09-13` | `doc/08_tracking/bug/allow_reserved_as_hard_keyword_2026-09-13.md` | `allow` and `forbid` cannot be used as identifiers — hard keywords the lexer's own comment says are contextu |
| `architecture_rule_audit_2026-08-10` | `scripts/check/lib/portable-hardlink-lock.pl` | Two Perl scripts violate the 'ALL code in .spl/.shs' rule |
| `arity_census_reaudit_declaration_side_defects_2026-08-04` | `remainder filed"` | Arity census re-audit: declaration side is not ground truth |
| `arrow_match_arm_multi_field_pattern_parse_fail_2026-08-18` | `doc/08_tracking/bug/arrow_match_arm_multi_field_pattern_parse_fail_2026-08-18.md` | Arrow-form `match` arm fails to parse when the pattern binds 2+ fields |
| `asm_block_form_discards_operand_constraints_2026-09-01` | `doc/08_tracking/bug/asm_block_form_discards_operand_constraints_2026-09-01.md` | Block-form `asm:` silently discards its operand constraints |
| `aspect_weave_specs_timeout_vacuous_green_2026-08-18` | `and the runner reports it as a vacuous green"` | Aspect weave/join-point specs time out |
| `assignment_rhs_line_continuation_rejected_2026-08-21` | `doc/08_tracking/bug/assignment_rhs_line_continuation_rejected_2026-08-21.md` | Parser rejects an assignment whose RHS is on the next line |
| `async_handler_registry_removed_apis_2026-09-16` | `doc/08_tracking/bug/async_handler_registry_removed_apis_2026-09-16.md` | Async-handler registry APIs removed; contract specs still pin them |
| `async_host_missing_async_core_module_breaks_task_handle_cancel_2026-07-29` | `doc/08_tracking/bug/async_host_missing_async_core_module_breaks_task_handle_cancel_2026-07-29.md` | Bug: `std.async_core` module does not exist — the whole async_host task-handle/cancel family is unbuildable |
| `async_spec_taskstate_enum_fix_hangs_2026-09-01` | `doc/08_tracking/bug/async_spec_taskstate_enum_fix_hangs_2026-09-01.md` | async_spec.spl: TaskState declared as `class` instead of `enum` — fixing the declaration hangs the run |
| `auto_vectorize_pass_is_analysis_only_2026-09-13` | `doc/08_tracking/bug/auto_vectorize_pass_is_analysis_only_2026-09-13.md` | Auto-vectorization never runs in a production compile (`AnalysisOnly`) |
| `base64url_decode_accepts_invalid_alphabet_2026-08-18` | `doc/08_tracking/bug/base64url_decode_accepts_invalid_alphabet_2026-08-18.md` | `base64url_decode` silently accepts out-of-alphabet input (RFC 4648 §3.3) and diverges from the differential  |
| `be_dom_event_path_family_arity_and_style_serialize_2026-08-19` | `doc/08_tracking/bug/be_dom_event_path_family_arity_and_style_serialize_2026-08-19.md` | be_dom path-event family broken by ctor arity; serialize drops <style> text |
| `binding_module_shadow_census_2026-08-18` | `doc/08_tracking/bug/binding_module_shadow_census_2026-08-18.md` | Census: local binding shadowed by a module namespace (2026-08-18) |
| `bitfield_specs_vacuous_and_custom_primitive_bitfield_dead_2026-08-18` | `and `custom_primitive_bitfield.spl` is unreachable code"` | Bitfield ""coverage"" is vacuous |
| `block_scoped_use_no_op_symbol_resolution_2026-08-18` | `doc/08_tracking/bug/block_scoped_use_no_op_symbol_resolution_2026-08-18.md` | Function-body-scoped `use <path>.{name}` is a silent no-op for symbol resolution |
| `bm25_checked_rejects_valid_multiterm_and_shingle_aliasing_2026-08-31` | `doc/08_tracking/bug/bm25_checked_rejects_valid_multiterm_and_shingle_aliasing_2026-08-31.md` | Two real defects in the landed search primitives |
| `browser_composition_revision_counters_never_increment_2026-08-19` | `doc/08_tracking/bug/browser_composition_revision_counters_never_increment_2026-08-19.md` | Hosted browser render-session revision counters never increment |
| `browser_engine_missing_ua_defaults_2026-07-11` | `blockquote` | browser_engine: missing UA defaults (h4/h5/h6 |
| `browser_engine_table_row_horizontal_layout_2026-07-11` | `doc/08_tracking/bug/browser_engine_table_row_horizontal_layout_2026-07-11.md` | browser_engine: table rows lay cells vertically (no horizontal table layout) |
| `browser_renderer_surface_state_not_bound_to_engine2d_owner_2026-09-09` | `doc/08_tracking/bug/browser_renderer_surface_state_not_bound_to_engine2d_owner_2026-09-09.md` | BrowserRenderer surface state is not bound to the Engine2D owner |
| `browser_script_crossmodule_mutation_breaks_timer_event_2026-07-11` | `doc/08_tracking/bug/browser_script_crossmodule_mutation_breaks_timer_event_2026-07-11.md` | Cross-module class-arg mutation is lost under the seed interpreter — blocks setTimeout/addEventListener pers |
| `browser_session_fetch_body_not_disturbed_and_timer_rollback_2026-08-21` | `and a timer-rollback publication check fails"` | Browser session: fetch body is never ""disturbed" |
| `browser_session_input_path_inline_handler_title_writes_lost_2026-08-19` | `doc/08_tracking/bug/browser_session_input_path_inline_handler_title_writes_lost_2026-08-19.md` | BrowserSession: input-path inline handlers run but their document.title writes are lost |
| `browser_session_rendering_spec_residual_failures_2026-08-19` | `doc/08_tracking/bug/browser_session_rendering_spec_residual_failures_2026-08-19.md` | Residual failures in browser_session dom-input / script-css-animation specs (post interpreter-collision fixes) |
| `browser_webgpu_js_wasm_spec_perf_2026-06-14` | `test/03_system/app/browser/feature/webgpu_js_wasm_simple_spec.spl` | WebGPU JS/WASM system spec sits near its perf threshold |
| `builtin_type_name_shadowing_is_an_undecided_language_question_2026-08-22` | `doc/08_tracking/bug/builtin_type_name_shadowing_is_an_undecided_language_question_2026-08-22.md` | `struct text:` shadowing the built-in string — undecided language question |
| `bytebuffer_struct_param_mutation_not_persisted_2026-09-01` | `segfaults under `run`"` | ByteBuffer struct-parameter mutation lost across a foreign method call (test) |
| `callerless_vfs_executable_read_bypass_2026-08-11` | `doc/08_tracking/bug/callerless_vfs_executable_read_bypass_2026-08-11.md` | Callerless VFS executable-read bypass |
| `caret_external_receipt_semantic_authenticity_2026-08-25` | `doc/08_tracking/bug/caret_external_receipt_semantic_authenticity_2026-08-25.md` | Caret external receipt semantic authenticity gap |
| `caret_smux_multi_launch_adapter_missing_2026-08-21` | `doc/08_tracking/bug/caret_smux_multi_launch_adapter_missing_2026-08-21.md` | Caret smux multi-launch adapter missing |
| `catalog_service_named_capability_syscall_mismatch_2026-08-11` | `doc/08_tracking/bug/catalog_service_named_capability_syscall_mismatch_2026-08-11.md` | Catalogue service capabilities do not match live syscall requirements |
| `check_dangling_references_alias_reexport_false_positive_2026-07-28` | `doc/08_tracking/bug/check_dangling_references_alias_reexport_false_positive_2026-07-28.md` | `check-dangling-references.shs` reports false SYMBOL findings for alias re-exports |
| `check_gates_remaining_red_2026-09-02` | `doc/08_tracking/bug/check_gates_remaining_red_2026-09-02.md` | Remaining RED check gates after the 2026-09-02 sanity sweep |
| `check_guard_wiring_48_unwired_triage_2026-08-08` | `so their failures can never gate anything"` | 48 check-guard scripts are wired into no caller |
| `check_hook_installation_rejects_shared_worktree_launcher_2026-08-24` | `doc/08_tracking/bug/check_hook_installation_rejects_shared_worktree_launcher_2026-08-24.md` | check-hook-installation rejects the shared-worktree pre-push launcher |
| `check_script_wiring_orphans_2026-08-01` | `so their gates never run"` | 364 of 413 check scripts are invoked by nothing |
| `check_scripts_vacuity_census_2026-08-17` | `doc/08_tracking/bug/check_scripts_vacuity_census_2026-08-17.md` | scripts/check vacuity census — guards that pass by construction or exit mute |
| `class_instances_copy_on_bind_and_for_loop_drops_mutation_2026-08-04` | `and `for` loop mutation is discarded entirely"` | BUG: `class` instances copy on binding |
| `cli_dispatch_perf_spec_failure_2026-06-21` | `test/05_perf/cli_dispatch_perf_spec.spl` | test/05_perf/cli_dispatch_perf_spec.spl fails its dispatch latency budget |
| `cli_surface_registry_dispatch_table_drift_2026-09-05` | `blocking startup-perf C4"` | CLI surface drift fail-closes completion to `[]` |
| `clobber_4edef8fab8_458_files_unrepaired_2026-08-27` | `32` | 4edef8fab8 stale-snapshot clobber: 458 files still unrepaired |
| `co_compiled_duplicate_signature_dispatch_class_2026-08-31` | `doc/08_tracking/bug/co_compiled_duplicate_signature_dispatch_class_2026-08-31.md` | Co-compiled duplicate definitions with differing signatures — dispatch class |
| `code_idiom_gate_red_on_main_blocks_all_prs_2026-09-01` | `doc/08_tracking/bug/code_idiom_gate_red_on_main_blocks_all_prs_2026-09-01.md` | `Code Idiom & Structural Ratchet Gates` is RED on `main` — blocks every PR |
| `command_dispatch_migrated_app_paths_missing_2026-08-12` | `doc/08_tracking/bug/command_dispatch_migrated_app_paths_missing_2026-08-12.md` | command_dispatch: two migrated app dispatch targets missing on disk (2026-08-12) |
| `compat_loader_partial_exec_mapping_rollback_2026-08-25` | `doc/08_tracking/bug/compat_loader_partial_exec_mapping_rollback_2026-08-25.md` | Compatibility loader leaks partial executable mappings on load failure |
| `compatibility_aliases_retained_unreachable_targets_2026-07-19` | `Mach-O/COFF still pending"` | Alias _stubs.o section retention: ELF fixed |
| `compression_stored_only_encoders_lz4_2026-09-16` | `doc/08_tracking/bug/compression_stored_only_encoders_lz4_2026-09-16.md` | Compression encoders are stored-only: even lz4 never shrinks repetitive input |
| `concrete_receiver_unwrap_returns_receiver_word_2026-08-25` | `not the field"` | `.unwrap()` on a CONCRETELY-typed class receiver returns a pointer-shaped word |
| `constant_time_black_box_missing_2026-07-20` | `doc/08_tracking/bug/constant_time_black_box_missing_2026-07-20.md` | `std.crypto.constant_time` does not export `black_box` |
| `core_c_lane_cannot_host_browser_renderer_preinit_2026-08-22` | `doc/08_tracking/bug/core_c_lane_cannot_host_browser_renderer_preinit_2026-08-22.md` | core-C lane cannot host the browser renderer worker (preinit constructor compiled out) |
| `core_lexer_query_helpers_declared_fn_not_me_2026-09-06` | `not the `me` receiver the spec expects; a documenting comment is missing"` | CoreLexer query helpers declared `fn` |
| `core_worktree_config_disables_all_pre_push_guards_2026-08-08` | `doc/08_tracking/bug/core_worktree_config_disables_all_pre_push_guards_2026-08-08.md` | `core.worktree` in the shared `.git/config` silently disables ALL THREE pre-push guards |
| `coverage_wrapper_not_retained_keep_artifacts_2026-08-31` | `doc/08_tracking/bug/coverage_wrapper_not_retained_keep_artifacts_2026-08-31.md` | A failing coverage/MC-DC wrapper cannot be captured for inspection |
| `coverage_wrapper_undefined_identifier_clusters_2026-08-31` | `doc/08_tracking/bug/coverage_wrapper_undefined_identifier_clusters_2026-08-31.md` | Coverage-wrapper `Undefined(""undefined identifier: X"")` — root-cause grouping |
| `cpu_hotloop_gate_red_key_churn_and_prose_scoring_2026-08-01` | `not new debt"` | CPU hot-loop idiom gate red at new=158 from key churn |
| `cross_language_actual_execution_mode_receipt_missing_2026-08-12` | `src/app/cli/_CliMain/main_and_help.spl` | Cross-language source/SMF actual execution-mode receipt missing |
| `cross_module_class_name_collision_resolution_2026-08-17` | `doc/08_tracking/bug/cross_module_class_name_collision_resolution_2026-08-17.md` | Bug: cross-module class-name collision — type resolution can pick the OTHER module's class |
| `cross_module_public_symbol_collisions_2026-08-16` | `wrong-dispatch risk)"` | Cross-module public symbol collisions (bootstrap warnings |
| `cross_tree_file_sync_must_diff_whole_import_block_2026-08-17` | `not just the synced function"` | Cross-tree file sync must diff the whole import block |
| `db_request_port_evidence_authenticity_2026-08-25` | `doc/08_tracking/bug/db_request_port_evidence_authenticity_2026-08-25.md` | Database request-port evidence authenticity and owner gap |
| `db_server_tcp_transport_unbounded_line_read_2026-08-20` | `doc/08_tracking/bug/db_server_tcp_transport_unbounded_line_read_2026-08-20.md` | DB server TCP transport buffers an unbounded request line before the byte bound is checked |
| `dbfs_open_on_device_refuses_staged_volume_in_guest_2026-09-01` | `doc/08_tracking/bug/dbfs_open_on_device_refuses_staged_volume_in_guest_2026-09-01.md` | DBFS `open_on_device` refuses a valid staged volume in-guest (x86_64 freestanding) |
| `declare_globals_fallback_debug_print_ungated_2026-08-21` | `doc/08_tracking/bug/declare_globals_fallback_debug_print_ungated_2026-08-21.md` | `[DEBUG declare_globals fallback]` printed unconditionally on the cranelift codegen path |
| `declared_optional_local_loses_question_mark_expect_refused_2026-09-13` | `doc/08_tracking/bug/declared_optional_local_loses_question_mark_expect_refused_2026-09-13.md` | A declared `text?` local loses its `?` and `.expect()` is refused as `str.expect` (2026-09-13) |
| `deployed_bin_simple_lost_full_cli_2026-07-31` | `doc/08_tracking/bug/deployed_bin_simple_lost_full_cli_2026-07-31.md` | `bin/simple` deployed as a bootstrap-only binary — `test`/`run`/`lint` all gone (2026-07-31) |
| `deployed_binary_refuses_pure_simple_tools_2026-07-30` | `doc/08_tracking/bug/deployed_binary_refuses_pure_simple_tools_2026-07-30.md` | Deployed `bin/simple` refuses `test`/`lint`/`fmt` — all spec verification blocked |
| `direct_abi_syscall_enforcement_coverage_2026-08-11` | `doc/08_tracking/bug/direct_abi_syscall_enforcement_coverage_2026-08-11.md` | Incomplete direct ABI syscall enforcement coverage |
| `doc_coverage_command_broken_missing_load_sdoctest_blocks_2026-09-05` | `doc/08_tracking/bug/doc_coverage_command_broken_missing_load_sdoctest_blocks_2026-09-05.md` | `bin/simple doc-coverage` fails: two exported analysis functions are defined nowhere |
| `doc_coverage_sdoctest_functions_never_implemented_2026-09-02` | `which are defined nowhere"` | `doc-coverage` calls `load_sdoctest_blocks` and `compute_sdoctest_coverage` |
| `dotq_on_empty_collection_reads_present_2026-09-13` | `so `while coll.?:` never terminates"` | BUG: `.?` on an empty collection reads as PRESENT |
| `draw_ir_tiled_8k_software_timeout_2026-08-11` | `doc/08_tracking/bug/draw_ir_tiled_8k_software_timeout_2026-08-11.md` | DrawIR tiled 8K software evidence exceeds watchdog — 2026-08-11 |
| `duplicate_check_invalid_option_value_false_green_2026-07-19` | `doc/08_tracking/bug/duplicate_check_invalid_option_value_false_green_2026-07-19.md` | Duplicate-check invalid mode silently changed analysis |
| `effect_glass_screenshot_specs_exceed_solo_timeout_2026-08-19` | `doc/08_tracking/bug/effect_glass_screenshot_specs_exceed_solo_timeout_2026-08-19.md` | effect_engine_compare_spec / glass_pipeline_screenshot_spec exceed even a 1800s SOLO run |
| `effects_family_reroute_audit_2026-08-02` | `4 retained with the reroute proved"` | effects_* family: 4 of 8 modules deleted |
| `electron_simple_web_layout_gate_bypasses_render_lane_flag_2026-08-11` | `doc/08_tracking/bug/electron_simple_web_layout_gate_bypasses_render_lane_flag_2026-08-11.md` | Bug: bitmap-parity gate never exercises the blink render lane |
| `elif_val_pattern_in_if_expression_fails_to_bind_2026-08-19` | `doc/08_tracking/bug/elif_val_pattern_in_if_expression_fails_to_bind_2026-08-19.md` | `elif val Some(x) = ...` inside an if-EXPRESSION fails to bind the pattern var (interpreter) |
| `engine2d_six_showcase_fixture_painters_never_implemented_2026-09-06` | `doc/08_tracking/bug/engine2d_six_showcase_fixture_painters_never_implemented_2026-09-06.md` | Six engine2d showcase fixture painters were never implemented; their specs assert an unpainted surface |
| `engine_facade_spec_api_drift_common_types` | `doc/08_tracking/bug/engine_facade_spec_api_drift_common_types.md` | Engine Facade Specs: API Drift in std.common.engine Types |
| `engine_specs_stale_api_contracts_2026-09-16` | `units` | Engine lib specs red on stale API contracts (ids |
| `entry_closure_drops_facade_reexport_owner_modules_2026-09-03` | `doc/08_tracking/bug/entry_closure_drops_facade_reexport_owner_modules_2026-09-03.md` | Phase-1 entry closure never loads a facade's re-export OWNER modules |
| `enum_variant_payload_types_discarded_at_parse_2026-07-29` | `doc/08_tracking/bug/enum_variant_payload_types_discarded_at_parse_2026-07-29.md` | Enum payload capture is present; MC-API enum-payload lint remains open |
| `env_platform_process_owner_spec_red_platform_imports_absent_2026-09-13` | `doc/08_tracking/bug/env_platform_process_owner_spec_red_platform_imports_absent_2026-09-13.md` | env_platform_process_owner_spec is RED: env/platform.spl has none of the owner imports it asserts |
| `erlang_style_pipe_arrow_match_arms_unimplemented_2026-09-05` | `doc/08_tracking/bug/erlang_style_pipe_arrow_match_arms_unimplemented_2026-09-05.md` | Erlang-style `/ pattern -> expr` match arms are documented as preferred but parse nowhere |
| `examples_isolation_buffers_output_lost_on_timeout_2026-07-25` | `doc/08_tracking/bug/examples_isolation_buffers_output_lost_on_timeout_2026-07-25.md` | `examples/**` isolation wrapper buffers child output and discards it when the run is killed — any slow examp |
| `execution_lane_silently_demotes_green_result_is_not_evidence_2026-09-01` | `doc/08_tracking/bug/execution_lane_silently_demotes_green_result_is_not_evidence_2026-09-01.md` | An execution lane can report a clean result without ever having run |
| `expect_nil_not_equal_nil_boolean_coercion_2026-07-20` | `doc/08_tracking/bug/expect_nil_not_equal_nil_boolean_coercion_2026-07-20.md` | `expect(nil != nil)` yields nil instead of boolean false (only when both sides are nil) |
| `extern_unimplemented_links_weak_stub_fabricated_value_2026-08-18` | `doc/08_tracking/bug/extern_unimplemented_links_weak_stub_fabricated_value_2026-08-18.md` | extern fn with no implementation links a weak stub and fabricates a value |
| `fake_gate_audit_2026-08-11` | `doc/08_tracking/bug/fake_gate_audit_2026-08-11.md` | Fake-gate audit — specs that cannot detect a violation (2026-08-11) |
| `fat32_atomic_replace_lifecycle_fserror_corrupt_2026-09-13` | `doc/08_tracking/bug/fat32_atomic_replace_lifecycle_fserror_corrupt_2026-09-13.md` | FAT32 atomic-replace lifecycle test fails with `FsError::Corrupt` |
| `feature_block_not_a_bdd_keyword_2026-08-04` | `300 `it` blocks never run"` | `feature ""...""` is not a BDD block keyword — 10 spec files are dead entry points |
| `file_ops_mock_answers_for_nonexistent_paths_2026-09-06` | `reads return ""mock file content"""` | `std.nogc_sync_mut.file_system.file_ops` is a MOCK: `file_exists` is true for any path |
| `file_read_has_23_definitions_with_two_return_types_2026-08-16` | `doc/08_tracking/bug/file_read_has_23_definitions_with_two_return_types_2026-08-16.md` | `file_read` has 23 definitions across two incompatible return types |
| `fixedvec_splat_boxing_mismatch_breaks_simd_scan_2026-09-13` | `doc/08_tracking/bug/fixedvec_splat_boxing_mismatch_breaks_simd_scan_2026-09-13.md` | `fixedvec_splat` lanes never compare equal to `fixedvec_from_array` lanes |
| `for_in_143_diagnostic_span_cannot_localize_the_loop_2026-08-24` | `doc/08_tracking/bug/for_in_143_diagnostic_span_cannot_localize_the_loop_2026-08-24.md` | `#143` (and its neighbours) report spans that cannot localize the loop (2026-08-24) |
| `for_in_optional_initialized_local_loses_collection_type_2026-08-24` | `doc/08_tracking/bug/for_in_optional_initialized_local_loses_collection_type_2026-08-24.md` | `for-in` over a local initialized from an OPTIONAL-returning function loses its collection type (#143 residue) |
| `for_loop_var_shadowed_by_module_alias_2026-08-18` | `doc/08_tracking/bug/for_loop_var_shadowed_by_module_alias_2026-08-18.md` | `for` loop variable does not shadow a same-named module-namespace alias |
| `formula_regression_spec_orphan_it_2026-07-04` | `doc/08_tracking/bug/formula_regression_spec_orphan_it_2026-07-04.md` | formula_regression_spec.spl: TREND/GROWTH/PROB/RANDARRAY sections are orphaned `it`s that never ran |
| `frozen_branch_group_e_char_ptr_abi_mismatch_2026-08-31` | `doc/08_tracking/bug/frozen_branch_group_e_char_ptr_abi_mismatch_2026-08-31.md` | Frozen bootstrap branch carries char*-ABI Group E exports (tagged-value callers) |
| `fs_file_class_collision_wrong_static_method_2026-09-01` | `doc/08_tracking/bug/fs_file_class_collision_wrong_static_method_2026-09-01.md` | `std.fs` resolves ambiguously (file vs directory module) — two `File` classes collide |
| `full_cli_static_fast_path_link_closure_2026-09-03` | `doc/08_tracking/bug/full_cli_static_fast_path_link_closure_2026-09-03.md` | Full CLI static fast path retains the product link closure |
| `full_suite_aborts_mcdc_dynamic_probe_symbol_2026-08-26` | `doc/08_tracking/bug/full_suite_aborts_mcdc_dynamic_probe_symbol_2026-08-26.md` | A full-suite run aborts before executing anything: `variable mcdc_dynamic_probe_controller_load_builtin_curren |
| `function_argument_types_unchecked_2026-09-01` | `doc/08_tracking/bug/function_argument_types_unchecked_2026-09-01.md` | Function argument types are not checked — a `text` passed to an `i64` parameter runs |
| `gate_oracle_soundness_census_2026-08-11` | `so a silent no-op run reads as a"` | census of check scripts whose oracle is exit-code-only |
| `generator_intensive_spec_shadows_generatorstate_variants_2026-08-10` | `not"` | generator_intensive_spec declares its own GeneratorState so it tests a local model |
| `gpu_glyph_rasterization_gpu_deferred_no_device_2026-09-06` | `doc/08_tracking/bug/gpu_glyph_rasterization_gpu_deferred_no_device_2026-09-06.md` | GPU glyph rasterization is NOT-STARTED on Vulkan and Metal; deferred for want of a device |
| `gui_renderdoc_feature_coverage_spec_daemon_timeout_2026-06-28` | `test/03_system/check/gui_renderdoc_feature_coverage_status_spec.spl` | gui_renderdoc_feature_coverage_status_spec.spl times out under the SPipe test daemon |
| `gui_widget_renderdoc_goal_blockers_2026-06-23` | `doc/08_tracking/bug/gui_widget_renderdoc_goal_blockers_2026-06-23.md` | Bug: GUI widget RenderDoc goal blockers remain |
| `h2_request_authority_validation_missing_2026-09-16` | `doc/08_tracking/bug/h2_request_authority_validation_missing_2026-09-16.md` | h2_validate_request_headers: no authority-source ambiguity check |
| `host_equiv_transport_diverges_between_execution_lanes_2026-09-01` | `doc/08_tracking/bug/host_equiv_transport_diverges_between_execution_lanes_2026-09-01.md` | `host_equiv_transport_check` passes on the JIT lane and FAILS on the interpreter |
| `host_shared_cache_l2_gc_never_runs_and_cas_has_no_project_guard_2026-09-07` | `and cas_store has no project-namespace guard"` | Host-shared cache: bounded L2 GC never runs |
| `host_wm_cached_chrome_full_frame_blit_2026-07-06` | `src/os/compositor/host_compositor_entry.spl` | Host WM blits the entire cached desktop frame every repaint instead of dirty subrects |
| `html_css_rendering_inventory_lexical_false_pass_2026-09-05` | `doc/08_tracking/bug/html_css_rendering_inventory_lexical_false_pass_2026-09-05.md` | HTML/CSS rendering inventory lexical false pass |
| `if_chain_last_arm_returns_previous_value_2026-07-28` | `doc/08_tracking/bug/if_chain_last_arm_returns_previous_value_2026-07-28.md` | A statement-leading `-`/`+` at the same indent is silently glued to the previous line |
| `if_val_expression_form_binding_lost_2026-07-20` | `doc/08_tracking/bug/if_val_expression_form_binding_lost_2026-07-20.md` | `if val` expression form loses the bound pattern variable |
| `ifc_linebox_spec_imports_nonexistent_layout_inline_2026-09-14` | `doc/08_tracking/bug/ifc_linebox_spec_imports_nonexistent_layout_inline_2026-09-14.md` | `ifc_linebox_spec` is 0/10 — it imports a `layout_inline` that has never existed |
| `impl_to_free_fn_refactor_family_sweep_2026-08-07` | `doc/08_tracking/bug/impl_to_free_fn_refactor_family_sweep_2026-08-07.md` | `impl X:` -> free-function refactor wreckage: family sweep (2026-08-07) |
| `implicit_self_field_read_unresolved_in_plain_fn_method_2026-09-03` | `doc/08_tracking/bug/implicit_self_field_read_unresolved_in_plain_fn_method_2026-09-03.md` | Implicit `self` field READ inside a plain `fn` method is unresolved (JIT + HIR) |
| `import_triggered_cross_module_symbol_misdispatch_2026-08-18` | `doc/08_tracking/bug/import_triggered_cross_module_symbol_misdispatch_2026-08-18.md` | Import-triggered cross-module symbol misdispatch (interpreter lane) |
| `inline_arrow_match_arm_fails_when_followed_by_another_arm_2026-09-05` | `doc/08_tracking/bug/inline_arrow_match_arm_fails_when_followed_by_another_arm_2026-09-05.md` | Inline `/ pattern -> body` match arms parse only as the LAST arm |
| `ipc_wire_canonical_recv_abi_never_landed_2026-09-06` | `doc/08_tracking/bug/ipc_wire_canonical_recv_abi_never_landed_2026-09-06.md` | `ipc_wire.spl` is orphaned; the canonical syscall-21 dest-buffer recv ABI never landed |
| `java_new_hint_fires_after_named_arg_colon_2026-09-13` | `doc/08_tracking/bug/java_new_hint_fires_after_named_arg_colon_2026-09-13.md` | A `new` identifier after a named-argument `:` still raises the bogus ""Common mistake"" ERROR |
| `js_timer_queue_4096_entries_hang_2026-09-01` | `never completes) at 4096 entries"` | JS timer/animation-frame queue hangs (>150s |
| `jsonrpc_framing_divergence_2026-08-11` | `not 20 duplicates"` | JSON-RPC Content-Length framing: 4 behavioural families |
| `k1_composition_root_does_not_shadow_stub_2026-09-16` | `doc/08_tracking/bug/k1_composition_root_does_not_shadow_stub_2026-09-16.md` | K1 composition root does not shadow bootstrap_k1_selected stub — static K1 backend table is dormant |
| `kernel_closure_k0_to_p_static_residual_2026-09-07` | `doc/08_tracking/bug/kernel_closure_k0_to_p_static_residual_2026-09-07.md` | Kernel closure: 10 residual K0 -> P_STATIC imports (2026-09-07) |
| `kernel_launch_grammar_no_stream_slot_2026-08-25` | `doc/08_tracking/bug/kernel_launch_grammar_no_stream_slot_2026-08-25.md` | Kernel-launch grammar has no `stream:` / `shared:` slot — 2026-08-25 |
| `layout_core_incompatible_with_committed_belayoutbox_2026-08-15` | `doc/08_tracking/bug/layout_core_incompatible_with_committed_belayoutbox_2026-08-15.md` | layout_core still targets the pre-redesign BeLayoutBox (2026-08-15) |
| `layout_paint_paint_box_dead_code_wrong_belayoutbox_shape_2026-08-15` | `doc/08_tracking/bug/layout_paint_paint_box_dead_code_wrong_belayoutbox_shape_2026-08-15.md` | layout_paint.spl `_paint_box` is latent dead code built against the wrong BeLayoutBox shape |
| `lexer_drops_backslash_escape_in_string_literal_2026-09-02` | `doc/08_tracking/bug/lexer_drops_backslash_escape_in_string_literal_2026-09-02.md` | Lexer DROPS `` in a string literal instead of emitting one backslash |
| `lexer_position_unification_2026-07-29` | `one whole cluster found fully dead"` | Bug/audit: two lexer position states coexist; three live mixing sites fixed |
| `lexer_spec_list_iterable_symbol_collision_2026-09-01` | `doc/08_tracking/bug/lexer_spec_list_iterable_symbol_collision_2026-09-01.md` | `compiler/lexer_spec.spl`: co-compiled `List` symbol collision breaks `Iterable` trait check |
| `list_index_assignment_boxing_mechanism_2026-08-12` | `doc/08_tracking/bug/list_index_assignment_boxing_mechanism_2026-08-12.md` | `list[idx] = value` bracket-assignment boxing mechanism — differential findings |
| `llm_caret_codex_app_server_piped_stdio_2026-08-02` | `src/app/llm_caret/messaging/cli.spl` | codex app-server --listen stdio:// spawned via app.io piped façade dies before first response |
| `llm_caret_parity_matrix_target_paths_use_hyphens_2026-08-24` | `doc/08_tracking/bug/llm_caret_parity_matrix_target_paths_use_hyphens_2026-08-24.md` | LLM Caret parity matrices point at hyphenated `.spl` targets that repo convention forbids |
| `llm_strict_host_completion_blockers_2026-06-29` | `scripts/check/check-llm-strict-host-prereq-doctor.shs` | LLM strict-host prereq doctor and live-HTTP evidence gates remain incomplete |
| `llvm_backend_yield_silent_noop_2026-07-19` | `emitting no code for a yield"` | LLVM codegen matches MirInst::Yield to an empty arm |
| `lzma_full_range_model_deferred_2026-06-15` | `doc/08_tracking/bug/lzma_full_range_model_deferred_2026-06-15.md` | Bug / Deferral: lzma_full_range_model_deferred_2026-06-15 |
| `main_wtsync_reverted_read_trace_mod_2026-08-29` | `doc/08_tracking/bug/main_wtsync_reverted_read_trace_mod_2026-08-29.md` | main: chore(wtsync) commit reverted `pub mod read_trace;` — repo main unbuildable |
| `markers_module_unparseable_and_spec_drift_2026-07-28` | `src/os/kernel/log/markers.spl` | os.kernel.log.markers does not define NAMESPACE_BOOT that its spec imports |
| `match_arm_bound_value_method_call_returns_none_2026-08-24` | `doc/08_tracking/bug/match_arm_bound_value_method_call_returns_none_2026-08-24.md` | JIT: reading through a `case Some(x)` binding answers as if every key were absent |
| `mcdc_wrapped_copy_undefined_identifier_dir_only_2026-09-02` | `doc/08_tracking/bug/mcdc_wrapped_copy_undefined_identifier_dir_only_2026-09-02.md` | MC/DC-wrapped spec copy fails semantic analysis with `undefined identifier: fs` (directory targets only) |
| `method_call_on_result_returns_garbage_sentinel_2026-09-06` | `E>` compiles and returns a garbage sentinel instead of a type error"` | Method/field access on a `Result<T |
| `method_call_static_declared_default_metadata_gap_2026-08-12` | `doc/08_tracking/bug/method_call_static_declared_default_metadata_gap_2026-08-12.md` | MethodCallStatic declared-default metadata gap |
| `method_chain_poisons_receiver_type_2026-09-16` | `doc/08_tracking/bug/method_chain_poisons_receiver_type_2026-09-16.md` | Method chain poisons the receiver variable's inferred type |
| `method_field_not_found_on_object_2026-08-18` | `doc/08_tracking/bug/method_field_not_found_on_object_2026-08-18.md` | BUG: every `class` (reference-type) instance loses field and method resolution in the Rust-seed interpreter |
| `method_not_found_on_object_get_namespace_id_instance_2026-08-18` | `doc/08_tracking/bug/method_not_found_on_object_get_namespace_id_instance_2026-08-18.md` | `method get_namespace_id not found on type object` — instance of the general object-dispatch defect |
| `mixed_byte_and_codepoint_indexing_defect_class_2026-08-18` | `doc/08_tracking/bug/mixed_byte_and_codepoint_indexing_defect_class_2026-08-18.md` | Defect class: mixing byte-indexed and codepoint-indexed text APIs |
| `mixed_incremental_object_link_failure_2026-08-31` | `doc/08_tracking/bug/mixed_incremental_object_link_failure_2026-08-31.md` | Mixed incremental-object link failure blocks focused compiler tests |
| `mock_spec_i64_usize_cast_fails_only_in_spec_dsl_2026-09-01` | `doc/08_tracking/bug/mock_spec_i64_usize_cast_fails_only_in_spec_dsl_2026-09-01.md` | `mock_spec.spl`: `i64 as usize` cast fails inside a spec `it` block but works in compiled `fn main()` |
| `module_resolver_numbered_dir_probes_uncached_2026-08-31` | `doc/08_tracking/bug/module_resolver_numbered_dir_probes_uncached_2026-08-31.md` | Module resolver re-probes the numbered layer dirs on every import — 12-line fixture never finishes |
| `module_var_stale_in_it_closure_2026-08-16` | `doc/08_tracking/bug/module_var_stale_in_it_closure_2026-08-16.md` | A module-level `var` read directly inside an `it` block sees a stale value |
| `multiarch_boot_evidence_never_produced_2026-08-04` | `test/03_system/os/multiarch/six_arch_boot_spec.spl` | Multi-arch AC-4/AC-6 specs assert on QEMU boot evidence no lane produces; the --arch dispatch flag they call d |
| `named_target_action_executor_missing_2026-08-14` | `doc/08_tracking/bug/named_target_action_executor_missing_2026-08-14.md` | Named target execution lacks dependency inputs and authoritative receipts |
| `namespace_identifier_hard_rejected_2026-09-07` | `doc/08_tracking/bug/namespace_identifier_hard_rejected_2026-09-07.md` | `namespace` is hard-rejected as an identifier |
| `nandram_slot_map_undocumented_and_two_vacuous_slots_2026-09-01` | `doc/08_tracking/bug/nandram_slot_map_undocumented_and_two_vacuous_slots_2026-09-01.md` | `.nandram` slot map was undocumented; two slots are defective |
| `nested_use_in_it_block_cannot_resolve_transitive_enums_2026-09-05` | `doc/08_tracking/bug/nested_use_in_it_block_cannot_resolve_transitive_enums_2026-09-05.md` | `use` nested inside an `it` block cannot resolve transitively-reached enums |
| `network_coverage_illusion_and_spec_tree_duplication_2026-08-05` | `not sockets; spec tree duplicated 5` | Network e2e specs assert on source-text substrings |
| `networking_fragment_accumulator_quadratic_neighbors_2026-08-21` | `doc/08_tracking/bug/networking_fragment_accumulator_quadratic_neighbors_2026-08-21.md` | Quadratic fragment-accumulator neighbors in networking code |
| `newunit_unconstructible_from_source_2026-09-01` | `doc/08_tracking/bug/newunit_unconstructible_from_source_2026-09-01.md` | `newunit` declares a type that cannot be constructed from source; its spec never tries |
| `nogc_async_mut_missing_modules_2026-09-16` | `doc/08_tracking/bug/nogc_async_mut_missing_modules_2026-09-16.md` | nogc_async_mut: specs import modules absent from src/lib |
| `nogc_async_mut_unbacked_externs_and_missing_fns_2026-09-16` | `doc/08_tracking/bug/nogc_async_mut_unbacked_externs_and_missing_fns_2026-09-16.md` | nogc_async_mut specs pin lib functions that do not exist (or have no rt_ backing) |
| `nvme_emu_media_truncates_page_word0_to_one_byte_2026-09-01` | `doc/08_tracking/bug/nvme_emu_media_truncates_page_word0_to_one_byte_2026-09-01.md` | Emu (Vt-physics) media backend truncates page word 0 to 8 bits |
| `nvme_emu_typed_seam_has_no_read_disturb_injector_2026-09-01` | `so read-disturb recovery is untestable"` | The typed emu_* seam has no read-disturb injector |
| `nvme_gen_spec_exceeds_runner_budget_after_rescoring_2026-09-01` | `doc/08_tracking/bug/nvme_gen_spec_exceeds_runner_budget_after_rescoring_2026-09-01.md` | Three nvme_gen_* specs exceed the test-runner per-file budget |
| `office_plan_acceptance_spec_reads_wrong_evidence_root_2026-09-06` | `doc/08_tracking/bug/office_plan_acceptance_spec_reads_wrong_evidence_root_2026-09-06.md` | Office plan-acceptance spec reads an evidence root the gate never writes |
| `office_three_host_residual_render_divergence_2026-08-19` | `doc/08_tracking/bug/office_three_host_residual_render_divergence_2026-08-19.md` | Office three-host rendering: residual divergences after empty-block margin fix |
| `on_is_an_undocumented_reserved_word_2026-08-02` | `with an error that never nam"` | val on = ... fails to parse because 'on' is a hard keyword |
| `only_compiled_dead_tag_sweep_2026-07-03` | `doc/08_tracking/bug/only_compiled_dead_tag_sweep_2026-07-03.md` | BUG-TRACKING: Dead ""only-compiled"" spec tag — repo-wide sweep |
| `option_predicate_returns_payload_not_bool_2026-07-28` | `not bool — both engines"` | `.?` on Option returns the payload object |
| `optional_i64_return_payload_corruption_2026-08-31` | `doc/08_tracking/bug/optional_i64_return_payload_corruption_2026-08-31.md` | `i64?` return payload is silently corrupted (seed interpreter) |
| `optional_query_operator_identity_passthrough_2026-07-20` | `not a bool conversion"` | Interpreter: `.?` operator is an identity pass-through |
| `ora_batch_aa_pre_existing_red_specs_2026-08-26` | `doc/08_tracking/bug/ora_batch_aa_pre_existing_red_specs_2026-08-26.md` | ora_batch_aa specs RED at pre-edit baseline (sspec modernization batch) |
| `origin_main_not_test_runnable_env_access_host_parse_2026-08-25` | `doc/08_tracking/bug/origin_main_not_test_runnable_env_access_host_parse_2026-08-25.md` | `origin/main` is not test-runnable: `src/app/io/env_access_host.spl` fails to parse (2026-08-25) |
| `paren_tail_after_block_match_val_parsed_as_call_2026-08-18` | `doc/08_tracking/bug/paren_tail_after_block_match_val_parsed_as_call_2026-08-18.md` | Parenthesised tail expression after a block-`match` `val` is parsed as a call |
| `parent_commit_piped_reader_no_reassembly_2026-09-16` | `doc/08_tracking/bug/parent_commit_piped_reader_no_reassembly_2026-09-16.md` | parent_commit_piped_result_reader_v1 does not reassemble split stdout chunks |
| `path_based_fs_syscalls_fake_success_2026-08-06` | `doc/08_tracking/bug/path_based_fs_syscalls_fake_success_2026-08-06.md` | SimpleOS path-based POSIX syscalls: fake success replaced with honest ENOSYS; real FAT32 backend exists but is |
| `payload_widening_did_not_reach_emu_backend_2026-09-01` | `not the Vt-physics emulator"` | Payload widening (D1-D3) reached only the behavioural backend |
| `perf_wall_clock_ratio_unmeasurable_on_loaded_host_2026-09-13` | `doc/08_tracking/bug/perf_wall_clock_ratio_unmeasurable_on_loaded_host_2026-09-13.md` | Wall-clock perf ratios are not measurable on this host; use child CPU time |
| `pid1_target_service_manager_missing_2026-08-11` | `doc/08_tracking/bug/pid1_target_service_manager_missing_2026-08-11.md` | Missing target-native PID1 service manager |
| `placeholder_lambda_scoping_nested_ordinary_call_2026-08-31` | `doc/08_tracking/bug/placeholder_lambda_scoping_nested_ordinary_call_2026-08-31.md` | Placeholder-lambda (`_1`) scoping breaks for an ordinary call nested inside another call's argument |
| `platform_module_shadowing_and_unknown_import_segv_2026-09-01` | `doc/08_tracking/bug/platform_module_shadowing_and_unknown_import_segv_2026-09-01.md` | `platform.spl` shadowed by `platform/__init__.spl`; an unknown import SEGVs mute |
| `pre_push_hook_selftest_commits_fixtures_into_invoking_repo_2026-08-21` | `hijacking HEAD"` | Pre-push hook: a WIP guard's selftest commits fixtures into the invoking repo |
| `preexisting_main_gate_debt_blocking_all_prs_2026-08-31` | `doc/08_tracking/bug/preexisting_main_gate_debt_blocking_all_prs_2026-08-31.md` | Pre-existing main gate debt blocking every PR (recorded offender list) |
| `prepush_ratchet_guards_preexisting_red_blocks_unrelated_lanes_2026-08-16` | `blocking lanes that introduce nothing"` | Pre-push ratchet guards fail full-scan |
| `primitive_api_allow_annotation_unimplemented_2026-08-11` | `doc/08_tracking/bug/primitive_api_allow_annotation_unimplemented_2026-08-11.md` | `@allow(primitive_api)` / `#[allow(raw_unit)]` suppression is documented but never implemented |
| `provider_query_result_v2_wire_codec_missing_2026-09-13` | `doc/08_tracking/bug/provider_query_result_v2_wire_codec_missing_2026-09-13.md` | `SimpleProviderQueryResultV2` wire codec is missing; `os/smf/provider_query_wire.spl` imports nonexistent dige |
| `pure_backend_naked_fn_gaps_2026-08-28` | `doc/08_tracking/bug/pure_backend_naked_fn_gaps_2026-08-28.md` | Pure backend @naked gaps: alloca suppression + E-NAKED validation seed-only; ~{memory} default delta |
| `pure_simple_strict_mem_nil_init_ambiguity_2026-07-30` | `doc/08_tracking/bug/pure_simple_strict_mem_nil_init_ambiguity_2026-07-30.md` | Finding: pure-Simple interpreter strict-mem trap cannot distinguish ""no initializer"" from explicit `= nil` a |
| `pure_sql_reopen_checkpointed_file_stack_overflow_2026-08-25` | `doc/08_tracking/bug/pure_sql_reopen_checkpointed_file_stack_overflow_2026-08-25.md` | Pure-Simple SQL: re-opening an already-checkpointed file stack-overflows — 2026-08-25 |
| `quic_h3_transport_tls_blocker_2026-08-20` | `doc/08_tracking/bug/quic_h3_transport_tls_blocker_2026-08-20.md` | QUIC/HTTP-3 transport blocker (2026-08-20) |
| `readonly_struct_receiver_copy_registry_exhaustion_2026-08-12` | `doc/08_tracking/bug/readonly_struct_receiver_copy_registry_exhaustion_2026-08-12.md` | Read-only struct receiver copies exhaust the receiver registry |
| `recoverable_unwind_backend_abi_missing_2026-08-25` | `doc/08_tracking/bug/recoverable_unwind_backend_abi_missing_2026-08-25.md` | Recoverable unwind backend ABI is incomplete |
| `regex_engine_no_spl_candidate_verify_api_2026-06-15` | `doc/08_tracking/bug/regex_engine_no_spl_candidate_verify_api_2026-06-15.md` | Bug: regex engines expose no importable `.spl` candidate-verify API |
| `rel_health_rber_and_corrected_events_blind_to_ladder_recoveries_2026-09-01` | `doc/08_tracking/bug/rel_health_rber_and_corrected_events_blind_to_ladder_recoveries_2026-09-01.md` | rel_health RBER / corrected_events are blind to every read-retry-ladder recovery |
| `release_cli_dispatch_functions_missing_2026-09-07` | `doc/08_tracking/bug/release_cli_dispatch_functions_missing_2026-09-07.md` | `simple release` dispatch calls 20 functions that exist nowhere |
| `render_lane_specs_import_nonexistent_modules_2026-08-08` | `doc/08_tracking/bug/render_lane_specs_import_nonexistent_modules_2026-08-08.md` | Render-lane specs import modules that were never implemented (2026-08-08) |
| `renderdoc_electron_html_gate_spec_daemon_timeout_2026-06-28` | `test/03_system/check/renderdoc_electron_html_gate_spec.spl` | renderdoc_electron_html_gate_spec.spl times out under the SPipe test daemon though the |
| `resolve_methods_never_runs_on_real_compile_path_2026-09-01` | `doc/08_tracking/bug/resolve_methods_never_runs_on_real_compile_path_2026-09-01.md` | `resolve_methods` never runs on the real compile path |
| `rt_call_site_ratchet_regression_2026-09-05` | `doc/08_tracking/bug/rt_call_site_ratchet_regression_2026-09-05.md` | `rt_*` call-site ratchet regression in two stdlib domain trees |
| `rt_gate_never_existed_on_origin_hook_requires_it_2026-08-18` | `yet the push hook requires it"` | The rt_ gate has never existed on origin/main |
| `rt_heap_ref_wellformed_lost_in_stale_snapshot_clobber_2026-08-31` | `then lost to the 08-26 stale-snapshot clobber — docs survived` | `rt_heap_ref_wellformed` was landed |
| `rt_time_now_nanos_has_two_different_epochs_2026-08-09` | `doc/08_tracking/bug/rt_time_now_nanos_has_two_different_epochs_2026-08-09.md` | `rt_time_now_nanos` has two different epochs in two implementations |
| `runner_inprocess_spec_lexing_has_no_fault_boundary_2026-09-13` | `with no fault boundary"` | The test runner lexes spec sources in its OWN process |
| `rust_authority_fingerprint_overprunes_tracked_target_directories_2026-08-15` | `doc/08_tracking/bug/rust_authority_fingerprint_overprunes_tracked_target_directories_2026-08-15.md` | Rust authority fingerprint over-prunes tracked `target` directories |
| `safety_checker_case_some_never_matches_checks_skipped_2026-08-31` | `doc/08_tracking/bug/safety_checker_case_some_never_matches_checks_skipped_2026-08-31.md` | Safety checker's `case Some` arms never match — E1047 and transfer checks are silently skipped |
| `scripts_reorg_left_34_test_specs_on_pre_reorg_paths_2026-08-04` | `doc/08_tracking/bug/scripts_reorg_left_34_test_specs_on_pre_reorg_paths_2026-08-04.md` | The `scripts/` reorg updated product source but left 34 test specs on pre-reorg paths — and the specs that " |
| `sdoctest_use_accumulation_exceeds_5s_block_timeout_2026-08-18` | `doc/08_tracking/bug/sdoctest_use_accumulation_exceeds_5s_block_timeout_2026-08-18.md` | SDoctest block timeout: `use`-line accumulation makes late blocks in an import-heavy doc unrunnable |
| `set_literal_s_brace_unparsed_2026-09-06` | `self-hosted frontend has half"` | `s{...}` set literal is unparsed — seed has no production |
| `setup_shs_fails_on_dash_sh_2026-09-13` | ``bin/simple` never created)"` | scripts/setup/setup.shs fails on a dash /bin/sh host (rc=2 |
| `setup_shs_pipefail_dash_abort_before_windows_guard_2026-09-13` | `doc/08_tracking/bug/setup_shs_pipefail_dash_abort_before_windows_guard_2026-09-13.md` | `scripts/setup/setup.shs` aborts on Linux: `set -o pipefail` under dash fires before the Windows-only early-ex |
| `simd_lane_ops_reject_f32_cast_values_2026-08-25` | `doc/08_tracking/bug/simd_lane_ops_reject_f32_cast_values_2026-08-25.md` | `std.simd` lane ops reject values produced by `as f32` (2026-08-25) |
| `simple_check_segfaults_on_hello_world_2026-09-01` | `doc/08_tracking/bug/simple_check_segfaults_on_hello_world_2026-09-01.md` | `simple check` SEGVs on a two-line hello world |
| `simple_pipe_codebase_duplicate_scan_2026-08-24` | `doc/08_tracking/bug/simple_pipe_codebase_duplicate_scan_2026-08-24.md` | `simple_pipe` codebase duplicate scan and child startup |
| `simple_ring_async_base_open_evidence_2026-08-26` | `doc/08_tracking/bug/simple_ring_async_base_open_evidence_2026-08-26.md` | SimpleRing async-base open evidence |
| `simple_test_default_runner_silent_vacuous_pass_2026-09-06` | `and the Rust runner caches by spec mtime only"` | `bin/simple test <spec>` exits 0 with NO output at all |
| `simple_web_html_layout_renderer_layout_paint_coverage_gap_2026-08-07` | `a 50-point gap"` | Layout renderer line coverage measured 40% against a 90% target |
| `simple_web_layout_corpus_perf_2026-05-31` | `test/03_system/gui/wm_compare/famous_site_corpus_spec.spl` | famous_site_corpus_spec takes 86222ms and the runner flags it PERF BUG |
| `skia_raw_rgba_magic_constant_wrong_value_2026-09-06` | `doc/08_tracking/bug/skia_raw_rgba_magic_constant_wrong_value_2026-09-06.md` | `RAW_RGBA_MAGIC` constant value does not match its documented 'RBPA' byte pattern |
| `slice_index_range_form_unimplemented_and_misnamed_2026-08-25` | `and one misnamed diagnostic (2026-08-25)"` | `a[start:end]` vs `a[start..]`: two unimplemented slice features |
| `smf_enum_def_serializes_variant_names_only_2026-08-21` | `types` | SMF `EnumDef` serializes variant NAMES only — arity |
| `smf_gotrel32_applied_as_symbol_value_2026-09-18` | `doc/08_tracking/bug/smf_gotrel32_applied_as_symbol_value_2026-09-18.md` | SMF wire relocation 4 (`GotRel32`) is applied with S = symbol address in both live loaders |
| `smf_manifest_written_but_never_verified_2026-08-17` | `doc/08_tracking/bug/smf_manifest_written_but_never_verified_2026-08-17.md` | SmfManifest written but never verified on load |
| `smf_reader_memory_binding_decode_changes_exported_set_2026-09-19` | `doc/08_tracking/bug/smf_reader_memory_binding_decode_changes_exported_set_2026-09-19.md` | BUG: fixing `SmfReaderMemory.parse_binding` changes what `exported_symbols()` returns for a mixed-binding modu |
| `smf_reader_writer_externs_unimplemented_2026-07-31` | `doc/08_tracking/bug/smf_reader_writer_externs_unimplemented_2026-07-31.md` | SMF reader/writer externs are unimplemented scaffolding (2026-07-31) |
| `sosix_owned_ipc_v1_continuation_and_cross_arch_reachability_2026-08-11` | `doc/08_tracking/bug/sosix_owned_ipc_v1_continuation_and_cross_arch_reachability_2026-08-11.md` | SOSIX Owned IPC v1 Continuation and Cross-Architecture Reachability |
| `sosix_process_sharing_spec_pre_existing_red_2026-08-27` | `doc/08_tracking/bug/sosix_process_sharing_spec_pre_existing_red_2026-08-27.md` | sosix_process_sharing_spec pre-existing RED — `sosix_dataset_active` not found |
| `sosix_vfs_ipc_receive_abi_mismatch_2026-08-11` | `doc/08_tracking/bug/sosix_vfs_ipc_receive_abi_mismatch_2026-08-11.md` | SOSIX VFS IPC Receive ABI Mismatch |
| `spec_describe_in_main_leaks_exit_code_2026-08-30` | `doc/08_tracking/bug/spec_describe_in_main_leaks_exit_code_2026-08-30.md` | `describe` as the trailing expression of `fn main() -> ()` leaks a non-zero exit code |
| `spec_gen_flattens_output_and_silently_drops_specs_2026-08-18` | `doc/08_tracking/bug/spec_gen_flattens_output_and_silently_drops_specs_2026-08-18.md` | `simple spec-gen` flattens mirror paths and silently drops most specs |
| `spec_helper_block_if_imported_call_not_callable_2026-08-19` | `doc/08_tracking/bug/spec_helper_block_if_imported_call_not_callable_2026-08-19.md` | Spec-file helper with imported call inside block-if expression fails ""semantic: value is not callable"" under |
| `spec_pending_call_still_counts_it_block_as_pass_2026-07-25` | `doc/08_tracking/bug/spec_pending_call_still_counts_it_block_as_pass_2026-07-25.md` | `pending(...)` inside an `it` block is counted and reported as a PASS |
| `spec_step_bare_import_duplicates_file_rename_stack_overflow_2026-08-27` | `doc/08_tracking/bug/spec_step_bare_import_duplicates_file_rename_stack_overflow_2026-08-27.md` | `use std.spec.step` puts a duplicate `file_rename` in the unit; every atomic write self-recurses |
| `spec_test_loader_impl_method_dispatch_2026-08-27` | `doc/08_tracking/bug/spec_test_loader_impl_method_dispatch_2026-08-27.md` | Spec-test loader fails method dispatch and mangles names for locally-defined classes and helpers |
| `spec_toplevel_return_unit_diagnostic_lacks_file_line_2026-09-03` | `doc/08_tracking/bug/spec_toplevel_return_unit_diagnostic_lacks_file_line_2026-09-03.md` | `cannot convert tuple to int` from a spec has no file:line |
| `spirv_builder_emit_function_ignores_preallocated_entry_point_id_2026-08-11` | `doc/08_tracking/bug/spirv_builder_emit_function_ignores_preallocated_entry_point_id_2026-08-11.md` | `SpirvBuilder.emit_function()` cannot be paired with a pre-allocated entry-point id |
| `spkc_p3_authority_publication_atomic_journal_nonadmission_2026-08-26` | `doc/08_tracking/bug/spkc_p3_authority_publication_atomic_journal_nonadmission_2026-08-26.md` | SPKC P3 authority-publication atomic journal is non-admitted |
| `spl_doctest_composite_fails_wildcard_reexport_modes_2026-08-25` | `doc/08_tracking/bug/spl_doctest_composite_fails_wildcard_reexport_modes_2026-08-25.md` | SPL-doctest composite fails on a wildcard re-export that imports fine standalone |
| `spl_doctest_harness_aborts_unsafe_not_found_2026-08-25` | `doc/08_tracking/bug/spl_doctest_harness_aborts_unsafe_not_found_2026-08-25.md` | `--spl-doctest` aborts on every input at origin/main — `function `unsafe` not found` |
| `spl_doctest_variable_not_found_class_2026-08-24` | `doc/08_tracking/bug/spl_doctest_variable_not_found_class_2026-08-24.md` | SPL doctest class `semantic: variable X not found` — triage 2026-08-24 |
| `spl_thread_current_id_arity_mismatch_2026-09-16` | `doc/08_tracking/bug/spl_thread_current_id_arity_mismatch_2026-09-16.md` | spl_thread_current_id: 0-arg source call vs 1-arg runtime backing |
| `sqrt_f64_not_correctly_rounded_2026-09-01` | `doc/08_tracking/bug/sqrt_f64_not_correctly_rounded_2026-09-01.md` | `std.math.special.sqrt_f64` is not correctly rounded (diverges from `rt_math_sqrt`) |
| `squashed_snapshot_e274cd33719_gutted_81_files_2026-09-07` | `doc/08_tracking/bug/squashed_snapshot_e274cd33719_gutted_81_files_2026-09-07.md` | `e274cd33719` is a squashed stale snapshot that gutted 81 files repo-wide |
| `ssa_alloca_value_return_admission_spec_conflict_2026-08-21` | `two specs assert the opposite"` | SSA alloca lane rejects `Ret(Some(..))` — four reproducer specs RED |
| `sshd_password_verifier_zeroization_gap_2026-08-20` | `doc/08_tracking/bug/sshd_password_verifier_zeroization_gap_2026-08-20.md` | SSHD password verifier zeroization gap |
| `stale_snapshot_clobber_4edef8fab8e_2026-08-26` | `doc/08_tracking/bug/stale_snapshot_clobber_4edef8fab8e_2026-08-26.md` | Stale-snapshot clobber: `4edef8fab8e` (""feat: snapshot current development state"") |
| `stale_spec_cluster_premise_false_148_live_specs_2026-08-23` | `and deleting these specs would have destroyed live coverage"` | The ""148 stale specs"" cluster is NOT stale — the APIs exist |
| `standalone_smf_patternmatch_detector_len_on_i64_2026-08-31` | `doc/08_tracking/bug/standalone_smf_patternmatch_detector_len_on_i64_2026-08-31.md` | Standalone native-build of a match-bearing file crashes the unsupported-construct scan with `len` on i64 |
| `starfive_tigard_shifted_tap_ids_2026-08-20` | `doc/08_tracking/bug/starfive_tigard_shifted_tap_ids_2026-08-20.md` | StarFive Tigard scan intermittently returns shifted TAP IDs |
| `static_factory_method_chain_wrong_value_2026-08-16` | `doc/08_tracking/bug/static_factory_method_chain_wrong_value_2026-08-16.md` | Chaining a method off a static factory call fails to resolve the method |
| `stats_hangs_after_file_counts_2026-09-02` | `doc/08_tracking/bug/stats_hangs_after_file_counts_2026-09-02.md` | `simple stats` prints the file counts and then hangs indefinitely |
| `stitch_mcp_file_not_defined_and_missing_auth_2026-09-15` | `doc/08_tracking/bug/stitch_mcp_file_not_defined_and_missing_auth_2026-09-15.md` | Stitch MCP: import crash `File is not defined` in Kimi-spawned environments; auth keys absent on this host |
| `stray_vgate_probe_tag_2026-09-07` | `doc/08_tracking/bug/stray_vgate_probe_tag_2026-09-07.md` | `vgate-probe-004312` is a stray tag that nobody can delete |
| `string_template_multi_placeholder_slot_not_found_2026-07-30` | `doc/08_tracking/bug/string_template_multi_placeholder_slot_not_found_2026-07-30.md` | Two bare `_` placeholders in one string template: `variable __p1 not found` |
| `struct_param_mutation_semantics_2026-07-03` | `doc/08_tracking/bug/struct_param_mutation_semantics_2026-07-03.md` | Struct/class param mutation semantics — decision doc (task #35) |
| `struct_spread_paren_form_parses_as_range_2026-08-30` | `f: v)` parses as a RANGE` | Paren-form struct spread `T(..base |
| `target_instruction_optimization_32bit_spec_pre_existing_red_2026-08-27` | `doc/08_tracking/bug/target_instruction_optimization_32bit_spec_pre_existing_red_2026-08-27.md` | target_instruction_optimization_32bit_spec pre-existing RED — std.spec does not export 'SPipe' |
| `tcp_peer_probe_feature_missing_2026-09-16` | `doc/08_tracking/bug/tcp_peer_probe_feature_missing_2026-09-16.md` | Non-consuming TCP peer probe (TcpPeerProbe / rt_io_tcp_probe_peer) missing |
| `test_config_apply_value_missing_mut_param_2026-07-17` | `never the caller's TestConfig"` | test_config.spl: apply_test_config_value mutates its own stack frame only |
| `test_mode_filter_specs_are_vacuous_self_tests_2026-08-21` | `and the skip marker they assert on is corrupted"` | Test mode-filter specs are vacuous self-tests |
| `test_only_functions_family_census_2026-08-04` | `items unfiled"` | 197 test-only functions shipped in production modules; census is a floor |
| `test_tree_divergence_preexisting_2026-08-17` | `and the mirror the ed25519 fix missed"` | Pre-existing test-tree divergence |
| `test_tree_divergence_preexisting_red_2026-08-16` | `doc/08_tracking/bug/test_tree_divergence_preexisting_red_2026-08-16.md` | Pre-existing test-tree divergence red at `f6cadcc36af` — step-over record |
| `test_tree_divergence_preexisting_step_over_2026-08-16` | `doc/08_tracking/bug/test_tree_divergence_preexisting_step_over_2026-08-16.md` | Pre-existing test-tree divergence stepped over on 2026-08-16 |
| `three_layoutbox_variants_2026-08-10` | `doc/08_tracking/bug/three_layoutbox_variants_2026-08-10.md` | Four unrelated `LayoutBox` types across the layout lanes (2026-08-10) |
| `tiny_ui_web_wm_integration_blockers_2026-08-14` | `doc/08_tracking/bug/tiny_ui_web_wm_integration_blockers_2026-08-14.md` | Tiny UI/Web/WM integration blockers |
| `tls_no_fd_upgrade_blocks_starttls_2026-08-25` | `doc/08_tracking/bug/tls_no_fd_upgrade_blocks_starttls_2026-08-25.md` | TLS facade cannot upgrade an existing fd — STARTTLS (SMTP 587 / IMAP 143) is unimplementable |
| `to_equal_treats_nil_as_false_green_2026-09-01` | `doc/08_tracking/bug/to_equal_treats_nil_as_false_green_2026-09-01.md` | `expect(nil).to_equal(false)` passes — `to_equal` disagrees with `==` (2026-09-01) |
| `todo_scan_segfaults_after_db_write_and_renumbers_ids_2026-09-12` | `doc/08_tracking/bug/todo_scan_segfaults_after_db_write_and_renumbers_ids_2026-09-12.md` | `bin/simple todo-scan` segfaults after writing `todo_db.sdn` and renumbers every id on each run |
| `trait_group_with_sugar_status_f5_2026-08-09` | `wiring"` | trait-group `with` sugar status remeasured: parser-rejection claim superseded |
| `transport_profile_sdn_path_cwd_dependent_2026-09-01` | `doc/08_tracking/bug/transport_profile_sdn_path_cwd_dependent_2026-09-01.md` | Transport-profile checks fail silently-plausibly when run from any cwd but the repo root |
| `tree_size_guard_hangs_on_btrfs_metadata_exhaustion_2026-08-11` | `not the script"` | `check-tree-size-push.shs` scan phase stalls for 15-20+ min — root cause: btrfs metadata-chunk exhaustion |
| `u64_shift_signed_outside_typed_fn_2026-09-03` | `doc/08_tracking/bug/u64_shift_signed_outside_typed_fn_2026-09-03.md` | u64 shift/display go SIGNED outside a `-> u64` typed function |
| `ui_backend_isolation_gate_name_based_false_positives_2026-08-27` | `doc/08_tracking/bug/ui_backend_isolation_gate_name_based_false_positives_2026-08-27.md` | `check-ui-backend-isolation.shs` flags in-repo Simple functions whose NAME starts with `rt_` (2026-08-27) |
| `ui_web_ws_any_cast_fails_in_spawned_thread_2026-08-04` | `doc/08_tracking/bug/ui_web_ws_any_cast_fails_in_spawned_thread_2026-08-04.md` | Web server dies on first WebSocket upgrade: `as TcpStream` cast fails in spawned reader thread |
| `undefined_import_called_exits_zero_2026-08-17` | `called off the executed path` | An import that exists nowhere |
| `unit_spec_hangs_42_excluded_2026-08-27` | `doc/08_tracking/bug/unit_spec_hangs_42_excluded_2026-08-27.md` | 42 unit-spec exclusions: measured timeout classification and partial optimization (2026-08-27) |
| `unit_specs_that_never_parse_2026-09-13` | `doc/08_tracking/bug/unit_specs_that_never_parse_2026-09-13.md` | Unit specs that never parse — a whole file's examples vanish with one line of output |
| `unregistered_extern_silent_nil_2026-08-01` | `a silent 0` | An unregistered `@extern fn` is not a link error — it is a silent nil |
| `unsafe_block_expression_rhs_2026-08-22` | `doc/08_tracking/bug/unsafe_block_expression_rhs_2026-08-22.md` | Unsafe capability block cannot initialize a value |
| `unsafe_capabilities_block_unsupported_in_expression_position_2026-08-30` | `doc/08_tracking/bug/unsafe_capabilities_block_unsupported_in_expression_position_2026-08-30.md` | `unsafe(capabilities: [...])` is a STATEMENT-only form; in expression position it silently becomes a call and  |
| `unsafe_capability_block_syntax_not_parsed_2026-08-21` | `capabilities: [...]):` block syntax does not parse as an unsafe block"` | `unsafe(reason: ... |
| `untagged_specs_for_unbuilt_features_2026-09-20` | `doc/08_tracking/bug/untagged_specs_for_unbuilt_features_2026-09-20.md` | Untagged specs for functionality that was never built read as regressions |
| `unwrap_family_treats_flat_nil_as_present_2026-09-13` | `doc/08_tracking/bug/unwrap_family_treats_flat_nil_as_present_2026-09-13.md` | `unwrap_or` / `unwrap` treat a FLAT nil as a present value (2026-09-13) |
| `unwrap_still_rebinds_to_poll_unwrap_at_closure_scale_2026-09-13` | `doc/08_tracking/bug/unwrap_still_rebinds_to_poll_unwrap_at_closure_scale_2026-09-13.md` | `.unwrap()` still rebinds to `Poll.unwrap` at closure scale via a second route (2026-09-13) |
| `use_list_names_never_checked_2026-08-04` | `doc/08_tracking/bug/use_list_names_never_checked_2026-08-04.md` | The braced name list in a `use` declaration was never checked |
| `v_lane_suite_occlusion_spec_times_out_under_shared_wc_contention_2026-08-07` | `scripts/check/check-render-perf-v-lane-suite.shs` | compositor_occlusion_spec times out at the V-lane 600s floor under shared-WC contention |
| `value_spec_calls_undefined_value_kind_consumers_source_2026-09-06` | `so one `it` is permanently RED"` | `value_spec.spl` calls a helper that is defined nowhere |
| `verification_cache_invalidate_dependents_wildcard_symbol_2026-07-20` | `causing false-positive invalidation of unrelated proof units"` | Bug: `VerificationCache.invalidate_dependents` treats the file-level `""*""` symbol sentinel as a trackable de |
| `verification_layer_orphans_and_dangling_refs_2026-08-02` | `scripts/check/check-extern-registration.shs` | Guard scripts under scripts/check are unreachable from any root (orphaned) and refs dangle |
| `vfs_l5_fat32core_open_faults_on_new_file_write_2026-08-31` | `doc/08_tracking/bug/vfs_l5_fat32core_open_faults_on_new_file_write_2026-08-31.md` | L5 blocker: `Fat32Core.open` faults on the first write of a NEW file (2026-08-31) |
| `virtio_map_bar_capability_authority_2026-08-02` | `doc/08_tracking/bug/virtio_map_bar_capability_authority_2026-08-02.md` | Bug: VirtIO MapBar capability authority mismatch |
| `web_block_vertical_advance_12pct_2026-09-12` | `doc/08_tracking/bug/web_block_vertical_advance_12pct_2026-09-12.md` | Block vertical advance over-measured ~12 % — cause still NOT isolated (2026-09-12) |
| `web_geometry_differ_li_reparented_desyncs_nth_paths_2026-09-13` | `desyncing every later nth-path"` | Geometry differ: list items are reparented |
| `web_request_port_evidence_authenticity_2026-08-25` | `doc/08_tracking/bug/web_request_port_evidence_authenticity_2026-08-25.md` | Web request-port evidence authenticity gap |
| `web_showcase_4k_frame_time_unbudgeted_2026-09-13` | `and measured cost is not monotonic in pixel count"` | The 4K web showcase lane pins no frame-time budget |
| `web_showcase_dom_tab_bridge_gap_2026-09-05` | `doc/08_tracking/bug/web_showcase_dom_tab_bridge_gap_2026-09-05.md` | Native showcase DOM tab bridge gap |
| `web_style_cascade_apply_decls_reparses_per_node_2026-09-12` | `doc/08_tracking/bug/web_style_cascade_apply_decls_reparses_per_node_2026-09-12.md` | The style cascade re-parses declaration text per node: 86% of the cold document pipeline (2026-09-12) |
| `web_tab_bar_flex_item_widths_fractional_font_size_2026-09-14` | `not flex (2026-09-14)"` | tab-bar flex items are 1-2 px narrow — fractional UA font-size |
| `webfw_signing_wrong_digest_and_csrf_not_session_bound_2026-08-18` | `and CSRF tokens are NOT session-bound"` | web_framework signing: digest does not match HMAC-SHA256 |
| `widget_draw_ir_panel_title_not_rendered_2026-08-09` | `so titled panels look"` | Panel titles are never emitted by the pixel Draw-IR pipeline |
| `window_record_encode_declared_nowhere_2026-08-04` | `doc/08_tracking/bug/window_record_encode_declared_nowhere_2026-08-04.md` | `window_record_encode` is imported by the SPM client but defined nowhere; its spec only length-compares two se |
| `windows_rt_process_run_cannot_exec_shebang_script_fixtures_2026-09-02` | `so every `.shs` CLI fixture returns exit -1"` | Windows: `rt_process_run` cannot execute a shebang script |
| `wine_process_tls_dispatch_spec_pre_existing_red_2026-08-27` | `doc/08_tracking/bug/wine_process_tls_dispatch_spec_pre_existing_red_2026-08-27.md` | wine_process_tls_dispatch_spec pre-existing RED — missing VM write-readback evidence token |
| `wine_seh_frame_module_missing_2026-07-20` | `doc/08_tracking/bug/wine_seh_frame_module_missing_2026-07-20.md` | wine_seh_frame_spec.spl: `common.wine_seh_frame` module does not exist anywhere in src |
| `wine_thread_adapter_missing_impl_2026-07-20` | `doc/08_tracking/bug/wine_thread_adapter_missing_impl_2026-07-20.md` | Missing implementation: common.wine_thread_adapter module |
| `wine_vm_write_readback_token_renamed_specs_red_2026-08-26` | `doc/08_tracking/bug/wine_vm_write_readback_token_renamed_specs_red_2026-08-26.md` | Wine VM write-readback evidence token renamed; specs asserting the old token are RED |
| `wire_to_bytes_high_byte_utf8_roundtrip_corruption_2026-09-05` | `doc/08_tracking/bug/wire_to_bytes_high_byte_utf8_roundtrip_corruption_2026-09-05.md` | `bytes_to_wire`/`wire_to_bytes` corrupt round trips for byte values >= 0x80 |
| `wm_lane_boundary_7_new_violations_2026-08-08` | `scripts/check/check-wm-lane-boundary.shs` | check-wm-lane-boundary.shs reports 7 NEW portable-lane violations; nothing runs this gate |
| `wm_lifecycle_restore_action_does_not_restore_geometry_2026-08-08` | `doc/08_tracking/bug/wm_lifecycle_restore_action_does_not_restore_geometry_2026-08-08.md` | `apply_wm_action_to_lifecycle_windows` ""restore"" action does not restore window geometry |
| `wm_scene_css_render_perf` | `src/os/compositor/wm_scene.spl` | WM scene CSS pixel render too slow above 10000 px; path capped by |
| `wm_taskbar_pin_persistence_transaction_2026-07-29` | `src/os/compositor/compositor.spl` | Taskbar pin rollback fix has no live native persistence evidence; blocked by VFS global |
| `wm_web_standards_showcase_child_frame_timeout_2026-08-06` | `not a hang"` | wm_web_standards_showcase_gui host gets a real verdict — and it is FAIL (child-frame-timeout) |
| `world_units_engine_and_generators_modules_missing_2026-08-21` | `doc/08_tracking/bug/world_units_engine_and_generators_modules_missing_2026-08-21.md` | `std.common.units.engine` and `std.common.units.generators` do not exist — two specs cannot load |
| `wp18_taclebench_import_blocked_by_network_fetch_2026-08-07` | `doc/08_tracking/bug/wp18_taclebench_import_blocked_by_network_fetch_2026-08-07.md` | WP-18 TACLeBench import blocked: network fetch (`curl`/`wget`) is hard-blocked in this environment |
