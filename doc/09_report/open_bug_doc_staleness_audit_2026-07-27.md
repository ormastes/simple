# Open Bug Doc Staleness Audit — 2026-07-27

Read-only audit of every `doc/08_tracking/bug/*.md` doc carrying
`**Status:** open` as of 2026-07-27. Scope note: the task briefing estimated
"~56" open docs; the actual count on disk is **135**. All 135 were
investigated (6 parallel read-only research passes: doc text vs. `git log`
vs. current source), not sampled.

This report makes **no edits** to any bug doc, `src/**`, or `scripts/**`. It
is a recommendation list for a human or follow-up agent to apply in one pass.

## Count summary

| Classification | Count | Meaning |
|---|---:|---|
| **STILL-OPEN** | 89 | Defect reproduced by reading current code / genuinely unaddressed — real work remains |
| **LIKELY-FIXED** | 22 | Current code no longer has the described shape; cite evidence below |
| **UNVERIFIABLE** | 21 | Needs a build, test run, or hardware/QEMU access this audit didn't have |
| **SUPERSEDED** | 3 | Another doc now covers the same defect more accurately |
| **Total** | **135** | |

**Sanity check on the two docs named in the task briefing as recently
corrected:** both already carry accurate non-"open" status lines, so neither
appears in the 135-row audit below and neither needs a change:
- `hir_stub_module_nil_dict_get_phantom_some_2026-07-27.md` → `**Status:** superseded — see CORRECTION` (already correct)
- `native_struct_field_map_copy_nilfills_nested_dicts_2026-07-27.md` → `**Status:** invalid — not reproducible; see CORRECTION` (already correct)

**Status-line drift found independently** (doc's top `Status:` line
contradicts its own body text, a distinct defect class from "stale open"):
`interp_brace_literal_collides_with_string_interpolation_2026-07-03.md`,
`native_build_parser_100cps_regression_2026-07-26.md`,
`native_lambda_capture_scan_excludes_interpolated_strings_2026-07-17.md`,
`seed_parser_accepts_match_keyword_as_identifier_2026-07-27.md` (see rows
below).

---

## STILL-OPEN (89) — real work remains, prioritize these

| Doc filename | Date | Recommended Status | Evidence | Confidence |
|---|---|---|---|---|
| array_at_method_missing_dash_path_2026-07-20.md | 2026-07-20 | STILL-OPEN | No `fn at(` exists for array anywhere in stdlib; interpreter maps `"at"` only for strings (`interpreter_method/string.rs:335`); `src/lib/skia/feature/stroke/dash.spl:52,62,107,112` still calls `.at(i)`. | high |
| async_spec_promise_future_anon_tuple_state_inconsistency_2026-07-20.md | 2026-07-20 | STILL-OPEN | `test/01_unit/lib/std/async_spec.spl:41-84` still has the local-double `Future`/`Promise` classes sharing `state: AsyncState` via anon-tuple return. | medium |
| bare_hardware_namespace_import_unresolved_2026-07-20.md | 2026-07-20 | STILL-OPEN | 114 files under `test/01_unit/hardware/` still use bare `use hardware.X`; resolver still emits plain "Cannot resolve module" (`error_factory/resolve.rs:14`), no std-prefix fallback. | high |
| bootstrap_blocked_unknown_extern_rt_transient_array_scope_begin_2026-07-27.md | 2026-07-27 | STILL-OPEN | `runtime_symbols.rs:130` registers the symbol but `strings` on deployed `bin/release/.../simple` still returns 0 matches even after apparent rebuild. | high |
| bootstrap_stage4_optional_arg_and_mixed_tail_miscompile_2026-07-23.md | 2026-07-23 | STILL-OPEN | `src/compiler/70.backend/backend/cranelift_codegen_adapter.spl:928` `cl_translate_operand` still carries the documented inline-extraction workaround comment, unchanged. | high |
| browser_engine_text_metrics_api_drift_2026-07-20.md | 2026-07-20 | STILL-OPEN (partial) | `warnings` field still absent from `BeRenderResult` (`browser_renderer.spl:19-29`); `content_x` shape ambiguous between two `BeLayoutBox` classes — needs build to fully resolve. | medium |
| common_encoding_yaml_broken_cross_submodule_import_2026-07-20.md | 2026-07-20 | STILL-OPEN | `src/lib/common/encoding/yaml.spl:34` still has the broken `use std.common.yaml.{...}` import; no barrel module under `src/lib/common/yaml/`. | high |
| contract_expr_forall_ge_call_member_not_found_2026-07-20.md | 2026-07-20 | STILL-OPEN | `contracts.spl` unchanged at cited lines; no commit touches external qualified-name resolution paths. | medium |
| disk_image_builder_unbuildable_regression.md | (undated, filename only) | STILL-OPEN (native path only) | Doc's own 2026-07-17 update narrows to native-build `is_ok`/`upper` MIR-lowering errors; interp path self-documented fixed. Distinct from `disk_image_fat32_builder_defects.md`. | medium |
| doctest_parser_spec_api_mismatch_2026-07-20.md | 2026-07-20 | STILL-OPEN | `parser.spl:41` `DoctestItem` still lacks `code`/`setup`/`teardown`; `extract_docstrings`/`parse_expected` not found anywhere in `src/`. | high |
| enum_impl_static_fn_method_call_path_skips_impl_methods_2026-07-20.md | 2026-07-20 | STILL-OPEN | `interpreter_method/mod.rs:999-1006` `Value::EnumType` arm still only checks `enum_def.methods`, no `impl_methods` lookup. | high |
| freestanding_u64_cross_fn_range_compare_miscompile.md | 2026-07-08 (body) | STILL-OPEN | `src/os/kernel/loader/x86_64_fs_exec_ring3.spl:405-409` comment still warns against `.to_u64()` on literals, citing this bug. | high |
| gc_async_mut_missing_facade_wrapper_modules_2026-07-20.md | 2026-07-20 | STILL-OPEN | `src/lib/gc_async_mut/` still has no `compression/` or `database/` dirs (only unrelated `compress/`). | high |
| generic_class_static_method_unresolved_under_test_2026-07-20.md | 2026-07-20 | STILL-OPEN | Same dispatch-path class as `enum_impl_static_fn_method_call_path_skips_impl_methods_2026-07-20.md`, also still open; no dispatch fix found. | medium |
| gui_web_2d_retained_metal_simd_wm_perf_evidence_gap_2026-07-06.md | 2026-07-06 | STILL-OPEN | No `scripts/check/*` retained WM Web2D perf-evidence script combining metal+simd+p50/p95 found. | medium |
| host_toolchain_seed_pinned_lint_fmt_doccov_unrunnable_2026-07-17.md | 2026-07-17 | STILL-OPEN | Live check today: `bin/simple --version` still prints "this Rust-built Simple binary is a bootstrap seed only". | high |
| interp_array_param_indexing_2026-07-03.md | 2026-07-03 | STILL-OPEN | `src/app/office/sheets/formula.spl:8124-8129` comment still cites both interpreter limitations for the flat-array workaround. | high |
| interp_brace_literal_collides_with_string_interpolation_2026-07-03.md | 2026-07-03 | STILL-OPEN (remaining sub-case; **status-line drift**: top line says "open" but body says "partially resolved 2026-07-17") | 2 of 3 root causes fixed; a narrower nested-whitespace-only-brace sub-case is explicitly marked "open sub-case, not yet root-caused" in the doc body (~line 129). | high |
| interp_dict_in_struct_copy_corruption_2026-07-03.md | 2026-07-03 | STILL-OPEN | `src/app/office/sheets/cell_format.spl:11-15` parallel-arrays workaround comment still present, unfixed. | high |
| interp_lazy_import_global_first_use_unmaterialized_2026-07-15.md | 2026-07-15 | STILL-OPEN | `src/compiler/10.frontend/core/interpreter/module_loader_core.spl:107-121` `force_deferred_module` still delegates to `load_module` with no post-init owner. | high |
| interp_to_int_split_result_nil_coalesce_garbage_2026-07-17.md | 2026-07-17 | STILL-OPEN | `src/lib/common/json/path_ops.spl:53` still calls `part.to_int()` on a `.split()`-derived string in `json_path_get`. | high |
| interp_use_as_alias_not_visible_in_function_body_2026-07-20.md | 2026-07-20 | STILL-OPEN | `checker.spl:8/130` and `toolchain.spl:8/30` still reference module-scope `use...as` alias from inside a function body, unchanged. | high |
| jit_hir_struct_field_type_infer_2026-07-18.md | 2026-07-18 | STILL-OPEN | "cannot infer field type" message still present verbatim at `src/compiler_rust/compiler/src/hir/lower/expr/access.rs:402`. | high |
| jit_struct_field_compound_assign_loads_zero_2026-07-27.md | 2026-07-27 | STILL-OPEN (retitle warranted — no live repro remains) | `.spipe/compound_assign_audit/state.md` confirms compiler-level defect real (locals too), but zero live-executable instances remain in audited `src/` (one hit was inside a docstring). | high |
| jit_unresolved_static_ctor_symbol_xlenconfig_2026-07-27.md | 2026-07-27 | STILL-OPEN | `XlenConfig.rv32()/rv64()` static ctors present (`src/lib/hardware/riscv_common/xlen.spl:36,46`); JIT still declines whole module (`src/compiler_rust/compiler/src/codegen/jit.rs:103`), message matches verbatim. | high |
| lean_regen_memory_capabilities_missing_conversion_theorem_2026-07-20.md | 2026-07-20 | STILL-OPEN | No `"conversion_is_safe"` string anywhere in `memory_capabilities.spl`; still only in the failing test assertion. | high |
| lint_coll006_concat_loop_false_positive_negative_2026-07-27.md | 2026-07-27 | STILL-OPEN | `src/compiler/35.semantics/lint/collection_patterns.spl:377-391` `is_string_concat_assign_expr` still matches any `x=x+y`/`x+=y` by identifier reuse, no text-type check. | high |
| lint_coll006_false_positive_integer_accumulator_2026-07-27.md | 2026-07-27 | STILL-OPEN | `collection_patterns.spl:368-393` `is_string_concat_assign_expr` still has no type check; same root as sibling above. | high |
| lint_spipe005_rejects_assert_true_family_2026-07-27.md | 2026-07-27 | STILL-OPEN | `traceability_and_assertions.spl:382` `assertion_like` still only lists `expect(`/`to_equal(`, no `assert_true`/`assert_false`/`assert_equal`. | high |
| list_first_returns_raw_value_not_option_2026-07-20.md | 2026-07-20 | STILL-OPEN | `interpreter_method/collections.rs:57` unchanged: `"first" => arr.first().cloned().unwrap_or(Value::Nil)`, no Option tag. | high |
| llvm_backend_yield_silent_noop_2026-07-19.md | 2026-07-19 | STILL-OPEN | `codegen/llvm/functions.rs:1533` `ActorSend/ActorReply/Yield => {}` still a silent empty block. | high |
| native_build_nil_receiver_crash_2026-07-25.md | 2026-07-25 | STILL-OPEN | `_MirToLlvm/class_def.spl:111-112` `ty.kind` still has no nil guard; `redeploy_gate.shs:105` only exercises `--backend=cranelift`, LLVM lane unchecked. | medium |
| native_build_parser_100cps_regression_2026-07-26.md | 2026-07-26 | STILL-OPEN (**status-line drift**: summary clause says "root cause not yet isolated" but body later has "Root cause CONFIRMED") | `runtime_native.c` `rt_core_is_registered_enum`/`rt_core_as_closure` still linear-scan growing registries, no fix applied. | high |
| native_cli_run_std_hardware_brace_import_unresolved_2026-07-24.md | 2026-07-24 | STILL-OPEN | `src/app/io/cli_ops.spl` delegation still a layered fallback, not a single predictable rule; underlying HIR brace-import defect not independently confirmed without running. | low |
| native_dict_get_struct_value_corrupt_option_2026-07-27.md | 2026-07-27 | STILL-OPEN | `method_calls_literals.spl:1301-1319` `.get()` lowering still single-layer, no post-decode `struct_value_syms` registration; only the downstream crash site was worked around. | high |
| native_dict_len_returns_minus_one_2026-07-27.md | 2026-07-27 | STILL-OPEN | `method_calls_literals.spl:1344+` `.len()` still routes through generic fallback, not a dedicated dict-aware `rt_dict_len` check. | medium-high |
| option_pattern_accepted_on_non_option_scrutinee_2026-07-27.md | 2026-07-27 | STILL-OPEN | `eval_methods.spl:107` Option handling still gated on `kind == VAL_STRUCT`; `method_calls_literals.spl:388-396` still emits `rt_unwrap_or_self`. | high |
| openocd_bscan_tunnel_incompatible_with_v1_bridge_2026-07-24.md | 2026-07-24 | STILL-OPEN | Doc's own board-proven workaround (Vivado `hw_jtag` raw mode) stands in for a real fix; OpenOCD-tunnel-compat VHDL port still deferred. | high |
| parse_claude_json_response_name_collision_2026-07-20.md | 2026-07-20 | STILL-OPEN | Both `src/app/llm_caret/claude_cli.spl:246` and `src/lib/nogc_async_mut/llm/claude_cli.spl:103` still define `parse_claude_json_response`. | medium |
| parser_bare_trailing_neg_literal_folds_prev_line_2026-07-27.md | 2026-07-27 | STILL-OPEN | `src/compiler_rust/parser/src/expressions/binary.rs:68-91` still peeks through Newline/Indent for a leading binary op with no statement-boundary check. | high |
| placeholder_lambda_as_fn_param_callback_unevaluated_2026-07-20.md | 2026-07-20 | STILL-OPEN | `parser/src/expressions/postfix.rs:9-24` still skips placeholder→lambda transform when `call_arg_depth > 0`. | high |
| proton_wine_fixture_api_redesign_2026-07-20.md | 2026-07-20 | STILL-OPEN | `src/lib/common/proton_runtime_subsystems.spl:18,30` still lacks `proton_non_wine_runtime_evidence_new`; `wine_hello_exe_probe` still absent. | high |
| range_builtin_missing_step_argument_2026-07-20.md | 2026-07-20 | STILL-OPEN | `interpreter_call/builtins.rs:82-141` still treats 3rd `range()` arg as `inclusive` bool, not a step. | high |
| rawhandle_generational_id_api_drift_2026-07-20.md | 2026-07-20 | STILL-OPEN | `src/lib/common/engine/ids.spl:58-66` `RawHandle` still a single `value: i64` wrapper with no `.new()`. | high |
| riscv_gate_evidence_seed_attributed_bin_release_clobbered_2026-07-27.md | 2026-07-27 | STILL-OPEN | `readlink -f bin/simple` still resolves to the seed binary, which still prints "bootstrap seed only". | high |
| riscv_sidecar_contract_antiseed_guard_ineffective_2026-07-27.md | 2026-07-27 | STILL-OPEN | `check-riscv-fpga-sidecar-contract.shs:9-14` `is_rust_seed_simple()` still only path-matches, doesn't probe `--version`; still misses currently-clobbered binary. | high |
| rv64_compliance_spec_missing_core_ext_pkg_modules_2026-07-20.md | 2026-07-20 | STILL-OPEN | `src/lib/hardware/rv64gc/` still has no `core/`, `ext/`, or `pkg/` subdirs; spec still imports them. | high |
| rv64_dtb_overlay_not_materialized_in_soc_address_map_2026-07-27.md | 2026-07-27 | STILL-OPEN | `test/01_unit/lib/hardware/soc_rtl/addr4g_probe.spl:95` calls `soc_top_64_init` directly, skipping DTB preload that sibling specs use. | high |
| rv64_memory_ops_spec_missing_rv64ram_2026-07-20.md | 2026-07-20 | STILL-OPEN | `grep -rln "class Rv64Ram" src/` still zero hits; spec still imports it. | high |
| seed_emit_object_superlinear_hang_large_module_2026-07-20.md | 2026-07-20 | STILL-OPEN — blocks rv32 NVMe firmware QEMU gate | Doc's own last section: O(N²) fix (6e20fe04e80) landed but "does NOT cure the hang", dominant cost still unidentified. | high |
| seed_interpreter_parse_probe_memory_accumulation_2026-07-03.md | 2026-07-03 | STILL-OPEN | 2026-07-17 update addresses a different codebase (native Stage4), not the Rust seed's `parse_module` retention; chunking workaround still the mitigation. | medium |
| seed_interpreter_to_int_wrong_dispatch_2026-07-03.md | 2026-07-03 | STILL-OPEN | `src/compiler/10.frontend/core/lexer.spl:348-422` workaround (comment: "Seed-interpreter bug") still present; underlying `.to_int()` dispatch never fixed. | medium |
| seed_jit_wide_i64_literal_miscompile_2026-07-27.md | 2026-07-27 | STILL-OPEN | Sibling root-cause doc `seed_jit_boxed_int_61bit_drops_high_bits_2026-07-22.md` still "OPEN — fix is a core value-representation change (awaiting go-ahead)". | medium |
| seed_overload_score_option_bytes_misleading_unknown_static_2026-07-20.md | 2026-07-20 | STILL-OPEN | `constructor_value_matches_type` still has no `Value::Some(_)` unwrap branch; only a `.spl` call-site workaround exists. | high |
| seed_parser_accepts_match_keyword_as_identifier_2026-07-27.md | 2026-07-27 | STILL-OPEN (body drift: claims "fixed by renaming" but code still broken) | `src/lib/nogc_sync_mut/compression/gzip/lz77.spl:104` still has `val match = ...`; `check-keyword-identifier-bindings.shs` still FAILs on it today. | high |
| selfhost_cross_module_result_ok_err_unresolved_2026-07-27.md | 2026-07-27 | STILL-OPEN | `vfs.spl` still has 0 `Result.Ok/Err` and 61 bare `Ok(`/`Err(` (documented workaround); no resolver fix found. | high |
| self_hosted_fat32_lfn_interpreter_segv_2026-07-14.md | 2026-07-14 | STILL-OPEN | Referenced worktree/binary no longer exist and no runner-segfault fix commit found; needs rerun to fully confirm. | medium |
| selfhost_parser_no_explicit_enum_values_2026-07-27.md | 2026-07-27 | STILL-OPEN | `src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl:128-134` still has no `= <int>` arm in the variant loop. | high |
| selfhost_two_hop_field_method_mutation_lost_2026-07-27.md | 2026-07-27 | STILL-OPEN | Doc's root-cause citation (`node_exec.rs:944` depth guard applies only to assignment, not method-call receivers) still matches current interpreter shape. | high |
| simple_check_diagnostics_contract_raw_parser_error_not_stable_format_2026-07-20.md | 2026-07-20 | STILL-OPEN | `src/app/cli/check.spl:271-284` `_check_path` still prints raw `parser_get_errors()` strings, not the `error[Exxxx]`/help format. | high |
| simpleos_riscv64_inguest_simple_payload_corec_gap_2026-07-25.md | 2026-07-25 | STILL-OPEN | The 6 named `rt_*` functions remain absent from `src/runtime/simple_core/`, still only in `runtime_native.c`. | high |
| simple_web_textarea_overlay_review_hard_stop_2026-07-27.md | 2026-07-27 | STILL-OPEN / fail-closed | Referenced commits and files (e.g. `simple_web_html_draw_ir_painter.spl`) don't exist in tree — nothing was integrated, matching doc's own claim. | high |
| spipe_docgen_stale_syntax_detection_2026-07-19.md | 2026-07-19 | STILL-OPEN | `src/app/spipe_docgen/spipe_docgen/parser.spl:364` still `starts_with("it \"")`; `:93` still only matches standalone `"""`. | high |
| sql_stmt_cache_dict_get_never_hits_2026-07-20.md | 2026-07-20 | STILL-OPEN | `src/lib/nogc_sync_mut/database/sql/stmt_cache.spl:32-45` `get_or_prepare` unchanged, still `match self.entries.get(sql): Some/nil`. | high |
| sspec_extern_array_arg_marshaling_empty_result_2026-07-20.md | 2026-07-20 | STILL-OPEN | No fix commits touching `rt_core_as_array`/marshaling found; doc's own instrumentation step never completed. | medium |
| sspec_runner_suppresses_child_failure_diagnostic_2026-07-26.md | 2026-07-26 | STILL-OPEN | No commit forwarding child diagnostics found in test_runner history since filing. | medium |
| stage4_focused_subbuild_star_import_unresolved_2026-07-27.md | 2026-07-27 | STILL-OPEN | `fixed_by: 67024e9c0a51` only partially fixed it — body documents remaining `me`/module-key blockers keeping deploy blocked. | high |
| stage4_link_undefined_peer_symbols_2026-07-28.md | 2026-07-28 | STILL-OPEN | `src/app/ui.web/html_css.spl` now imports `theme_package_fingerprint` (partial fix), but `run_test_api_server_with_inject` mangler bug unfixed. | high |
| stage4_selfhost_log_modes_lexer_state_corruption_2026-07-24.md | 2026-07-24 | STILL-OPEN | Doc already accounts for commit 01b5080f00 as "incomplete"; no newer multi-file lexer-state fix found. | medium |
| std_crypto_sha1_missing_hex_upper_2026-07-20.md | 2026-07-20 | STILL-OPEN | `sha1_hex_upper` still absent from `src/lib/crypto/sha1.spl`. | high |
| string_literal_brace_breaks_concat_2026-06-29.md | 2026-06-29 | STILL-OPEN (regression: fix landed then was lost) | Fix commit ca58e1f69b5 added an `!is_triple` guard, but current `strings.rs:318-329` blames the pre-fix commit — guard likely lost in the jjconflict-tree revert (37cda4befdc). | high |
| string_literal_double_brace_collapse_2026-06-16.md | 2026-06-16 | STILL-OPEN | `src/compiler_rust/parser/src/lexer/strings.rs:210-217,417-420` still collapse `{{`/`}}` to one brace unconditionally. | high |
| struct_shorthand_arg_order_binds_wrong_field_2026-07-20.md | 2026-07-20 | STILL-OPEN | Only commit touching "shorthand" is the filing commit itself; no interpreter fix found. | medium |
| table_lib_missing_set_import_and_method_gaps_2026-07-20.md | 2026-07-20 | STILL-OPEN | `src/lib/nogc_sync_mut/src/table.spl:12` still lacks a `Set` import while line 186 calls `Set.new()`. | high |
| target_arch_enum_enum_collision_option_2026-07-18.md | 2026-07-18 | STILL-OPEN | Both `enum TargetArch` declarations still exist unchanged (`src/lib/common/target.spl:1`, `backend_selector.spl:26`). | high |
| theme_ipc_k2_review_hard_stop_2026-07-27.md | 2026-07-27 | STILL-OPEN / fail-closed | K2 commits `235ef0250b`/`41eedf1bf5`/`d9554f91af` are not ancestors of HEAD — all 5 P1 gaps stand. | high |
| theme_package_transaction_sync_owner_blocker_2026-07-27.md | 2026-07-27 | STILL-OPEN | Candidate `4f84131c55` not in main; only wire codec `b1d0b3e27ff8` landed, prerequisites 1-5 unmet. | high |
| theme_snapshot_catalog_review_hard_stop_2026-07-27.md | 2026-07-27 | STILL-OPEN / fail-closed | `9f9a921689`/`d404042bc4`/`7ed0ae0a1a` all non-ancestors of HEAD; two P1 authority gaps unresolved. | high |
| try_operator_bare_nil_option_none_mismatch_2026-07-20.md | 2026-07-20 | STILL-OPEN | `interpreter/expr.rs:450-459` still has the catch-all emitting the exact message, no `Value::Nil`→None arm. | high |
| unit_composite_to_conversion_and_power_operator_2026-07-20.md | 2026-07-20 | STILL-OPEN | `interpreter_method/special/types.rs:43-55` has no bare `to` arm; falls through to BDD matcher returning `Value::Bool`. | high |
| unit_type_si_prefix_and_suffix_bugs_2026-07-20.md | 2026-07-20 | STILL-OPEN | `interpreter_unit.rs:49-72` `decompose_si_prefix` unchanged; `types.rs:46` still returns stored suffix. | medium |
| unwrap_or_return_default_value_dropped_2026-07-20.md | 2026-07-20 | STILL-OPEN | `parser/src/expressions/postfix.rs:558-561` still `Expr::UnwrapOrReturn(Box::new(expr))` with no default parsed. | high |
| verification_cache_invalidate_dependents_wildcard_symbol_2026-07-20.md | 2026-07-20 | STILL-OPEN | `verification/cache.spl:182,195-196` still fold bare `source_symbol` (incl. `"*"`) into `changed_keys` with no sentinel guard. | high |
| verification_lean_init_missing_use_before_export_2026-07-20.md | 2026-07-20 | STILL-OPEN | `verification/lean/__init__.spl` still lists bare `export LeanCodegenOptions, ...` with no preceding `use`/`export use`. | high |
| vhdl_backend_branch_local_and_aggregate_codegen_gaps_2026-07-20.md | 2026-07-20 | STILL-OPEN | `vhdl_expr.spl:142-330` aggregate paths and all 9 named spec examples unchanged since filing. | medium |
| with_statement_exit_self_field_mutation_lost_2026-07-20.md | 2026-07-20 | STILL-OPEN | `interpreter_control.rs:3076-3131` `exec_with` calls `__exit__` via `exec_method_body`, which clones `env` and never writes back mutated `self` fields. | high |
| wm_glass_qemu_evidence_contract_p1_2026-07-27.md | 2026-07-27 | STILL-OPEN / fail-closed | Newest commit `ba1fecd1301` still records unresolved BRR2 hard stops with no integrated fix. | high |
| x64_freestanding_module_level_val_u32_desktop_gui_2026-07-12.md | 2026-07-12 | STILL-OPEN | `gui_entry_desktop.spl:282-283` still carries local-literal workaround, no module-level `val DESKTOP_FB_WIDTH_4K`. | high |
| zstd_sequence_rle_normal_offset_mismatch_2026-07-20.md | 2026-07-20 | STILL-OPEN | `test/unit/lib/common/zstd_sequence_rle_spec.spl:53-64` byte-identical to doc's repro, unchanged since filing. | high |

---

## LIKELY-FIXED (22)

| Doc filename | Date | Evidence | Confidence |
|---|---|---|---|
| browser_engine_css_float_layout_unimplemented_2026-07-20.md | 2026-07-20 | `src/lib/gc_async_mut/gpu/browser_engine/layout_float.spl` (185 lines: FloatContext/float_place/float_clear_y) fully wired into `layout_core.spl:107-213`; `dom.spl:298` parses `float:`/`clear:`. | high |
| browser_engine_css_size_quadratic_pixel_render_2026-07-04.md | 2026-07-04 | Doc's own final section: "RESOLVED (2026-07-05) first frame 16s→6.6s"; the `decl_get2`/`parse_decl_pairs` fix confirmed present. Status line stale. | medium |
| codegen_large_match_dispatch_body_2026-07-27.md | 2026-07-27 | Commit `eb8e64320a9` (2026-07-27) split `_dispatch_function` from 2497 lines into a 37-line dispatcher delegating to sub-dispatchers — the doc's proposed fix. | high |
| css_bytes_helpers_dead_code_2026-07-07.md | 2026-07-07 | Doc's own last section: "Resolution (2026-07-17): FIXED... deleted (44 lines)"; zero matches for the named functions in current renderer. Status line stale. | high |
| decorator_aop_interpreter_fallback_noop_2026-07-20.md | 2026-07-20 | LIKELY-FIXED for decorators only | `interpreter_eval.rs:585-674` performs real decorator application (commit `37cda4befdc`, 2026-07-25, after filing); AOP `pc{}` weaving still explicitly compile-time-only. Reclassify doc scope to AOP-only, or split. | medium |
| disk_image_fat32_builder_defects.md | (undated) | Commit `2138b3d9fca6` (2026-07-11) fixes all 4 named defects: `nested_payloads` default, `_to_8_3_name()`, dynamic FAT sizing, `rt_file_truncate` type match. | high |
| expect_nil_not_equal_nil_boolean_coercion_2026-07-20.md | 2026-07-20 | `interpreter/expr/ops.rs:934-936` `BinOp::NotEq` explicitly special-cases nil-vs-nil to return `Value::Bool(false)`, contradicting the claimed defect. | medium-high |
| formula_regression_spec_orphan_it_2026-07-04.md | 2026-07-04 | `formula_regression_spec.spl` now wraps TREND/GROWTH/PROB/RANDARRAY in `describe:` blocks. | high |
| gui_winit_window_not_registered_window_server_2026-07-06.md | 2026-07-06 | Commit `056fa88adfd` (2026-07-06) added `NSApplicationActivationPolicy::Regular` + `activate` in `spl_winit/src/lib.rs:361,444`. | medium |
| js_engine_es2015_parser_gaps_2026-07-05.md | 2026-07-05 | `es2015_conformance_spec.spl` now imports `JsParser`, which implements let/const, destructuring, spread, classes, for-of/for-in, template literals. | medium |
| local_var_kernel_shadowed_by_module_2026-07-06.md | 2026-07-06 | `parser/src/parser_patterns.rs:185` now lowercases identifier patterns, landed in `116187d85d5`. | medium |
| lsp_code_action_edit_emit_parse_mismatch_2026-06-16.md | 2026-06-16 | `lsp_handlers.spl:727-746` `_parse_code_action` now parses nested `edit.changes` via `_extract_emitted_range`, matching doc's proposed fix. | medium |
| map_insert_if_absent_missing_and_map_new_resolves_to_dict_2026-07-20.md | 2026-07-20 | `src/lib/nogc_sync_mut/src/map.spl:325` now defines `insert_if_absent`; Map.new()/dict-collision half not independently re-verified. | medium |
| native_lambda_capture_scan_excludes_interpolated_strings_2026-07-17.md | 2026-07-17 | Status-line drift: top says "open", body has "Resolution (2026-07-17): FIXED". `switch_operators_calls.spl:2541-2545` `StringLit` case now recurses via `string_interps_capture_scan_supported`. | high |
| office_md_block_named_field_on_unlabeled_tuple_2026-07-20.md | 2026-07-20 | `src/app/office/file_formats.spl:189` `_md_block` now returns `MdBlockResult(block:, comments:)`, a named struct. | high |
| rv64_smoke_tb_dangling_soc_top_rv64_entity_2026-07-21.md | 2026-07-21 | `soc_top_rv64.vhd:26` now defines `entity soc_top_rv64`, added by commit `c35ef5b7807` (2026-07-24, after doc's date). | high |
| sspec_expect_eq_to_equal_false_silently_wrong_2026-07-17.md | 2026-07-17 | Commit `dfec06170ae` (2026-07-20): SSpec `expect(a==b)` no longer hard-fails past a chained matcher; `bdd.rs:833-928` now evaluates correctly. | high |
| test_config_apply_value_missing_mut_param_2026-07-17.md | 2026-07-17 | Commit `002863a059c` deleted `apply_test_config_value` entirely, replaced with `std.config_core`; `test_config.spl:6-13` comment cites this bug by name. | high |
| test_level_filters_never_match_numbered_trees_2026-07-27.md | 2026-07-27 | `test_runner_files.spl`/`test_manifest_scanner.spl` now delegate to new `test_level_detect.spl` which strips numbered prefixes — but that file is **untracked/uncommitted**, not yet landed. Recheck before closing. | medium |
| vhdl_entryfile_crossmodule_enum_resolve_2026-07-18.md | 2026-07-18 | `driver.spl:491-590` now transitively loads `use`-imported modules; `vhdl_compile_entry.spl` (commit `3d67dc87eb6`) sets `SIMPLE_NATIVE_BUILD_ENTRY` for `--backend=vhdl`. | medium |
| while_val_pattern_binding_not_visible_in_body_2026-07-20.md | 2026-07-20 | `interpreter_control.rs:352-373` inserts pattern bindings into `env` before `exec_block`; commit `a4ca4ee3d08` (2026-07-18) fixed the HIR-lowering gap — 07-20 repro likely hit a stale seed. | medium |
| x64_sshd_version_exchange_freestanding.md | 2026-07-08 | Commit `19e2f81e55f4` fixed the BYTE_PACKED `[u8]` C↔Simple ABI mismatch; gate log states version exchange passes and reaches KEX. | medium |

---

## SUPERSEDED (3)

| Doc filename | Date | Recommended Status | Evidence | Confidence |
|---|---|---|---|---|
| browser_layout_large_simd_fill_facade_unsafe_2026-07-09.md | 2026-07-09 | SUPERSEDED by cpu_simd_external_cairo_8k_perf_gap_2026-07-09.md | `browser_layout_framebuffer_filled` still the sole containment boundary, unchanged; sibling doc carries newer dated sections and is the more current tracking doc. | medium |
| llm_caret_index_of_optioni64_tagbox_2026-07-07.md | 2026-07-07 | SUPERSEDED by to_int_optional_lies_and_some_i64_payload_shift_2026-07-27.md | Newer doc isolates the same hypothesis to a precise Some(i64) tag-shift + `to_int()`/`.?` defect. | medium |
| persistent_vec_from_array_of_static_method_unresolved_2026-07-20.md | 2026-07-20 | SUPERSEDED by jit_fallback_drops_second_static_method_registration_2026-07-20.md | Same defect class root-caused/pinned by regression test in the newer doc; `PersistentVec.{of,from_array}` is the same class. | medium |

---

## UNVERIFIABLE (21) — needs build/test/hardware

| Doc filename | Date | What's needed | Confidence |
|---|---|---|---|
| browser_network_policy_check_blocker_2026-07-26.md | 2026-07-26 | An actual pure-Simple `check` run; the one static claim (`cors.spl:62`) is present but identical patterns exist elsewhere unflagged. | medium |
| browser_session_animation_target_build_blockers_2026-07-26.md | 2026-07-26 | Full pure-Simple build+run of the fixture; the one verifiable parser claim is present in source. | medium |
| cpu_simd_external_cairo_8k_perf_gap_2026-07-09.md | 2026-07-09 | Fresh benchmark run; referenced blocker doc is now marked RESOLVED but no fresh 8K/Cairo ratio captured since. | medium |
| dot_question_truthy_op_returns_payload_as_call_arg_2026-07-20.md | 2026-07-20 | Build+repro; `.?` operator's interpreter evaluation path could not be located via static grep, doc itself flags this unconfirmed. | low |
| interp_module_var_array_get_method_2026-07-04.md | 2026-07-04 | Actually running the interpreter repro for `.get(i)` on module-level array vars. | low |
| interp_parse_module_arena_visibility_crash_2026-06-16.md | 2026-06-16 | `bin/simple run` repro; the two named functions now exist/export correctly in source, but interpreted-path resolution isn't statically confirmable. | low |
| kv260_rv32_fabric_uart_not_routed_golden_is_sim_2026-07-25.md | 2026-07-25 | Physical KV260 board access to wire an external USB-UART to PMOD J2; XDC pins unchanged. | high |
| lint_class_receiver_get_str_traceability_2026-07-27.md | 2026-07-27 | Actually running `bin/simple lint` on a class-bearing file; current file has zero `.get(` call sites, unlike the doc's implied lines. | low |
| math_block_implicit_mul_chain_and_matmul_2026-07-20.md | 2026-07-20 | `bin/simple test` run; doc names no specific source location for the fold logic. | high |
| mut_param_annotation_no_reference_propagation_2026-07-20.md | 2026-07-20 | Running `parser_type_annotations_spec.spl`; doc itself flags this may be intended semantics not a bug. | high |
| nested_fn_closure_mutation_not_propagated_2026-07-20.md | 2026-07-20 | Re-running the interpreter repro; doc's root cause is an unconfirmed hypothesis about closure env capture. | high |
| optional_query_operator_identity_passthrough_2026-07-20.md | 2026-07-20 | Running the doc's repro; `DotQuestion` token defined but no consumer found by static grep. | medium |
| processing_ir_cuda_vulkan_fill64_parity_2026-07-26.md | 2026-07-26 | Full bootstrap + live CUDA/Vulkan hardware probes; doc ends mid-repair with explicit unresolved item. | medium |
| redeploy_gate_struct_copy_time_flip_2026-07-25.md | 2026-07-25 | Re-running the gate live on macOS across time; doc itself says "not yet isolated" (environment-sensitive JIT-vs-interpreter mode flip). | medium |
| security_event_enum_variant_construct_unresolved_under_test_2026-07-20.md | 2026-07-20 | Running `bin/simple test` on the seed to confirm test-vs-run dispatch divergence; source unchanged. | medium |
| seed_constructor_static_method_no_literal_coercion_2026-07-20.md | 2026-07-20 | Live test execution; doc's own final update revises root cause to a resolution gap. | medium |
| test_runner_expect_failure_swallowed_u8_bytes_2026-07-03.md | 2026-07-03 | An admitted fresh Stage 4 bootstrap smoke run; doc's 2026-07-19 section already claims the fix landed. | high |
| test_runner_post_spec_lint_gate_empty_file_arg_2026-07-20.md | 2026-07-20 | Running `bin/simple test test/01_unit/tools/cat_spec.spl`; no `simple_lint` invocation locatable statically (companion sub-bug already fixed). | medium |
| x64_freestanding_layout_sensitive_dup_displaced_stores.md | 2026-07-12 | Native-build A/B bisection with `rt_dump_phys16` byte dumps; layout-sensitive, no minimal repro exists. | high |
| x64_freestanding_mmio_read_u8_address_dependent_zero.md | 2026-07-11 | Freestanding rebuild landing the buffer at the specific address under QEMU; `runtime_minimal.c:110` unchanged trivial read. | high |
| x64_freestanding_module_vs_entry_ring3_handoff.md | 2026-07-11 | QEMU boot with full syscall logging before SIGABRT; no root cause or fix recorded in doc. | high |

---

## Methodology note

Six parallel read-only sub-audits each covered ~22-23 docs: read the doc,
extract the core claim and named source files, run `git log --oneline -5 --
<path>` per named file, and read current source to compare shape. No builds,
tests, or hardware were exercised — that's exactly the UNVERIFIABLE bucket
above. Confidence reflects how directly the current source could be read
against the doc's specific claim (high = exact line/message match or
non-match; low = claim requires runtime behavior not visible from source).
