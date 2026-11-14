# private_call_gate_skips_import_bound_and_entry_calls_2026-11-14

- **Severity:** P3. **Status:** fixed (seed interpreter lane).
- **Found by:** `test_private_access_closure_attribution_2026-11-14` fixture matrix.
- **Fixed in:** `work/private-gate-gap2-20261114`. Model: Opus (Fable unavailable).

## Symptom

Product code could call another directory's private fn with rc 0 and no
diagnostic:

- a src function calling a private fn reached through a glob import;
- a src function calling one through an `export use` / `pub use` facade or a
  qualified `m.f()`;
- a product entry file doing any of the above (top level or `fn main`);
- any product code taking the private fn as a VALUE (`run_cb(secret)`,
  `val f = secret`, `val f = m.secret`), by UFCS (`x.secret()`) or by
  pipeline (`x |> secret`).

Test callers are exempt by design and must stay allowed.

## Root cause

`check_private_call_visibility` (`interpreter_module/module_loader.rs`) was only
reached from the flat `functions.get` dispatch. Other sites ran or produced a
private fn without it:

1. the import-bound candidate path in `interpreter_call/mod.rs`. A
   single-definition fn also has more than one `FUNCTION_OVERLOADS` entry, so
   almost every glob-imported call took this path;
2. the module-Dict paths for `m.f()` (`interpreter_call/mod.rs`
   `Expr::FieldAccess`, `interpreter_method/mod.rs`) and the bare-module
   fallback that serves `m.f()` inside `fn main`;
3. fn-value reads (`interpreter/expr/literals.rs` identifier,
   `interpreter/expr/calls.rs` module field), the two UFCS fallbacks
   (`interpreter_method/mod.rs`) and the two pipeline sites
   (`interpreter/expr/ops.rs`).

The caller identity was `<entry>` for every entry-file call, and the rule
exempts `<entry>`.

## Fix

- `gate_private_call` is applied at every site above, keyed by the definition's
  own name (an `as` alias cannot dodge the registry lookup).
- The caller is `private_call_caller()`: a caller override (`TOP_LEVEL_MODULE`),
  else `CURRENT_EXEC_MODULE`, else the entry file's own owner key. An entry file
  is now a real caller, with the same same-directory and test exemptions as any
  module.
- The override names the module whose top level is running
  (`enter_module_top_level`), or the module that WROTE the closure body now
  running: `CowEnv::closure_caller` is stamped at creation
  (`stamp_closure_origin`) and installed by `ClosureOriginGuard::enter_closure`;
  an owned fn run as a decorator value uses `enter_owned(owner)`; AOP advice
  records its declaring caller and applies it to the pinned definition only. A
  named frame (`enter(None)`) clears the override, so a writer never leaks into
  the fns its closure calls. Without the stamp, a library lambda calling its
  own module's private helper was refused when an entry invoked it (review
  P1, fixture rows `lamentry`/`lamfn`/`lamcb`/`decoentry`).
- `Class__static` dispatch is deliberately not gated (a bare-name collision
  would mis-attribute it).

## Product offenders made `pub`

The gate turns every existing cross-directory private call red, so each real
caller's target fn was made `pub` (wave-3 style, `fn` -> `pub fn` only): 675
(module, fn) pairs in four evidence waves (list below).

- **Wave A (356):** union of the Appendix B rule-2 static scan
  (`private_import_visibility_sweep_2026-11-13.md`; 506 rows / 345 pairs) and a
  dynamic warn-only census (gate in log-only mode over 88 specs exercising
  those callers; 184 sites / 157 pairs, 0 test callers; 146 in the static set).
  The 11 dynamic-only pairs were re-checked on a pre-`pub` checkout with the
  corrected closure attribution: all 11 still fire, so none was a closure
  mis-attribution.
- **Wave B (16):** `_EvalOps/*` part files called by `eval.spl` through the
  `eval_ops` glob facade. Observed as strict refusals in `core_array_cow_spec`
  (19 refusals; that spec times out on base and after the fix, so the warn-only
  census had recorded nothing for it).
- **Wave C (213):** exact braced-facade tier. A file-level port of the seed
  resolver's module keys (`NN.x` answers to `x` or is skipped), a `pub use` /
  `export use M.{n}` re-export of a private top-level `n`, and a product file in
  another directory importing `n` from that facade by braced name AND calling
  `n(` with no own `fn n`. Calibrated on the pre-`pub` tree: it rediscovers the
  observed `source_file_authored_path` refusal (`driver_api_heavy_path_spec`).
- **Wave D (90):** the glob-facade tier (glob import of a facade that glob
  re-exports the definer, plus a call), with the same exact resolution and call
  check. Calibration showed this tier finds real offenders (it rediscovers the
  `_EvalOps` pairs), and after the merge with `release/1.0.0` a further observed
  refusal (`mir_provider_session_content_key_v1`, `_MirLowering/module_lowering.spl`
  called by `80.driver/driver_pipeline_lowering.spl`) sat in no tier, so
  untested paths were shown to carry offenders; this tier plus that pair was
  applied rather than shipped as known-likely breakage.
- **Not complete:** the 8 editor pairs reached through `src/app/editor/*`
  (wave A dynamic-only) are found by no facade tier, so an untested path can
  still meet a new refusal. That is the intended fail-closed outcome: the
  error names the fn and module, and the fix is a `pub`.
- **Needle check:** no spec pins any of these names with a line-anchored
  `fn NAME` source assertion. Every hit is a substring `contains("fn NAME(...")`,
  which `pub fn NAME(` still satisfies, or inline fixture text.
  `unimported_env_get_call_origin_spec` uses `starts_with` but also accepts
  `pub fn env_get(`.
- **Clash check:** 19 wave-A names became `pub` in two files. 17 are the
  `gc_async_mut` / `nogc_async_mut` `lsp_json.spl` mirrors, which no module
  imports together. `_append_bytes` and `_u8_at` in `os/tls13/handshake13.spl`
  and `record13.spl` are both glob-imported by four `_Tls13/*` modules. The
  twins compute the same value, so overload choice cannot change behaviour.
  Waves B, C and D add no duplicate names; none is pinned by an anchored needle.

## Still open (not this fix)

- `jit_main_lane_skips_private_import_visibility_2026-11-13`: `fn main` on the
  default (JIT) lane is not gated.
- `private_fn_registry_late_for_importer_top_level_2026-11-14`: a module loaded
  only through another module's glob import is not yet in
  `PRIVATE_FNS_BY_OWNER` when its importer's top-level initializers run.

## Evidence

Seeds (release builds of this branch; `sha256` prefix): base gap-1
`seed-g1c` `73ffacb5d2cb`; final `seed-g2n` `136aa212f518` (merged with
`release/1.0.0`). Lanes: default + `SIMPLE_EXECUTION_MODE=interpret`.

- `test_private_access_matrix_spec`: 24/36 on `seed-g1c`; 31/36 on the
  pre-review gate (lambda/decorator writer rows and value/UFCS/pipeline rows
  red); 36/37 on `seed-g2m` (`entrydeco` red: an entry-defined decorator ran
  with the exempt `<entry>` caller, review 2 P1); 37/37 on `seed-g2n`.
- Seed unit tests `private_call_visibility_tests`: 9/9.
- `private_import_visibility_fail_closed_spec` 2/2,
  `private_import_test_importer_parity_spec` 2/2,
  `private_fn_call_visibility_spec` 3/3: identical before and after.
- 110-spec sweep (the 34 #9039 specs and neighbours, plus specs for every
  caller module): identical rc and counts on `seed-g1c` and the strict gate
  except the hidden product private calls reported here
  (`core_array_cow_spec`: 19 `_EvalOps` refusals, wave B;
  `driver_api_heavy_path_spec`: `source_file_authored_path` (wave C) and
  `mir_provider_session_content_key_v1` (wave D)). After the `pub` waves both
  heavy-path copies are back to their base counts and `core_array_cow_spec`
  times out on base and after, as before.
- Warn-only census on the `pub` tree: 0 lines over the 110 specs.
- Hot path (300k iterations, interpret lane, median of 3, `seed-g1c` ->
  gated seed): glob call 0.01 -> 0.01 s, qualified `m.f()` 0.77 -> 0.82 s,
  lambda create+call 0.63 -> 0.66 s, private fn passed as a value 1.37 ->
  1.52 s; max RSS flat (~34 MB).
- Baseline `check-private-import-baseline.shs --prune`: 144 stale entries
  pruned (names now `pub`), 0 added.

Review follow-ups not fixed here (no regression; recorded):
- an `as`-aliased import read as a VALUE (`use m.{secret as s}`;
  `run_cb(s)`) is not gated (the value gate keys on the name read);
- lambdas run by collection helpers (`.map`/`.filter`, builtins, thread spawn)
  do not install the writer stamp, so they keep the invoker as caller (the
  pre-existing behaviour).

## Pair list

### Wave A: Appendix B static scan + dynamic census (356)

- `src/app/llm_caret/multimodal_types.spl` (4): `image_value_status_name_v1`, `text_part_v1`, `validate_extraction_document_v1`, `validate_multimodal_request_v1`
- `src/app/svllm_pack/core.spl` (1): `run`
- `src/compiler/00.common/config.spl` (1): `env_get`
- `src/compiler/10.frontend/core/_AstExpr/accessors.spl` (5): `expr_get_asm_clobbers`, `expr_get_asm_kinds`, `expr_get_asm_locations`, `expr_get_asm_outputs`, `expr_get_float`
- `src/compiler/10.frontend/core/ast_stmt.spl` (1): `stmt_is_if_val_decl`
- `src/compiler/10.frontend/core/interpreter/env.spl` (5): `env_assign`, `env_has_frame`, `env_lookup`, `env_pop_scope`, `env_push_scope`
- `src/compiler/10.frontend/core/interpreter/_EvalOps/access_literal_assign_eval.spl` (2): `eval_assign_expr`, `eval_field_access`
- `src/compiler/10.frontend/core/interpreter/_EvalOps/call_method_eval.spl` (1): `eval_method_call`
- `src/compiler/10.frontend/core/interpreter/jit.spl` (3): `jit_is_compiled`, `jit_record_call`, `jit_try_execute`
- `src/compiler/10.frontend/core/interpreter/mod.spl` (1): `core_jit_interpret`
- `src/compiler/10.frontend/core/interpreter/ops.spl` (2): `ops_get_error`, `val_compound_op`
- `src/compiler/10.frontend/core/interpreter/resolve.spl` (2): `resolve_cached_local_count`, `resolve_is_slot_shadowed`
- `src/compiler/10.frontend/core/interpreter/value.spl` (33): `val_array_at`, `val_array_clear`, `val_array_len`, `val_array_pop`, `val_array_push`, `val_array_read_lease`, `val_array_set`, `val_equals`, `val_free`, `val_get_func_decl`, `val_is_array`, `val_is_function`, `val_is_int`, `val_is_nil`, `val_is_struct`, `val_is_text`, `val_is_truthy`, `val_iterable_array`, `val_kind_name`, `val_make_array`, `val_make_bool`, `val_make_float`, `val_make_function`, `val_make_nil`, `val_make_struct`, `val_make_text`, `val_struct_check_field_idx`, `val_struct_find_field_idx`, `val_struct_get_field`, `val_struct_get_field_idx`, `val_struct_set_field_idx`, `val_struct_upsert_field`, `val_to_text`
- `src/compiler/10.frontend/core/lexer.spl` (1): `current_core_source_get`
- `src/compiler/10.frontend/parser_types_expr.spl` (13): `parser_type_kind_array_element`, `parser_type_kind_function_params`, `parser_type_kind_function_return`, `parser_type_kind_is_function`, `parser_type_kind_is_pointer`, `parser_type_kind_is_reference`, `parser_type_kind_is_shared`, `parser_type_kind_is_unique`, `parser_type_kind_is_weak`, `parser_type_kind_optional_inner`, `parser_type_kind_ownership_inner`, `parser_type_kind_tuple_elements`, `parser_type_kind_union_members`
- `src/compiler/10.frontend/parser_types.spl` (2): `parser_function_header`, `parser_module_new`
- `src/compiler/20.hir/hir_definitions.spl` (1): `hir_attribute_from_raw`
- `src/compiler/20.hir/hir_types.spl` (1): `hir_type_kind_ownership_name`
- `src/compiler/20.hir/return_type_interface_v1.spl` (1): `rti_term_canonical_text`
- `src/compiler/30.types/dim_constraints.spl` (1): `format_shape`
- `src/compiler/35.semantics/narrowing.spl` (3): `analyze_condition`, `definitely_terminates`, `negate_facts`
- `src/compiler/50.mir/hir_declaration_summary_v1.spl` (1): `mir_hir_module_declarations_valid_v1`
- `src/compiler/50.mir/hir_expression_artifact_v1.spl` (1): `mir_hir_expression_load_in_owned_scope_v1`
- `src/compiler/50.mir/mir_data.spl` (2): `bootstrap_fn_ret_ok_shape_lookup`, `bootstrap_fn_ret_opt_shape_lookup`
- `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` (1): `hir_type_is_plain_scalar`
- `src/compiler/50.mir/native_trait_metadata.spl` (2): `native_trait_slot_index`, `native_trait_sorted_method_names`
- `src/compiler/55.borrow/borrow_check/mod.spl` (1): `check_mir_module`
- `src/compiler/70.backend/linker/crt_discovery.spl` (1): `path_dirname`
- `src/compiler/90.tools/fix/rules/helpers.spl` (1): `replace_interpolation_identifier`
- `src/compiler/95.interp/interpreter/llvm/tools.spl` (5): `find_llvm_as`, `find_opt`, `find_wasi_sysroot`, `find_wasm_ld`, `find_wasm_opt`
- `src/compiler/99.loader/loader/compiler_sffi.spl` (1): `serialize_type_json`
- `src/lib/common/contracts/distributed_control_codec_v2.spl` (2): `distributed_encode_grant_v2`, `distributed_grant_wire_validate_v2`
- `src/lib/common/contracts/distributed_control_v2.spl` (1): `distributed_environment_match_v2`
- `src/lib/common/engine/audio/simple_audio_q15.spl` (3): `simple_audio_q15_convolve_reference`, `simple_audio_q15_max_error_millionths`, `simple_audio_q15_work_status`
- `src/lib/common/gpu/render_surface_contract.spl` (5): `gpu_capture_receipt_admitted`, `gpu_frame_ring_capacity_valid`, `gpu_frame_slot_matches_surface`, `gpu_frame_slot_reusable`, `gpu_submission_token_device_proven`
- `src/lib/common/mission_critical/draw_ir_packed_generation_store_v3.spl` (1): `draw_ir_packed_hash_v3`
- `src/lib/editor/00.common/keybindings.spl` (1): `default_keybindings`
- `src/lib/editor/00.common/types.spl` (2): `editor_mode_command`, `editor_mode_insert`
- `src/lib/editor/buffer/buffer.spl` (2): `edit_fail`, `edit_ok`
- `src/lib/editor/core/launch.spl` (5): `editor_launch_clean_log_args`, `editor_launch_file_count`, `editor_launch_first_unknown_option`, `editor_launch_has_unknown_option`, `editor_launch_mode`
- `src/lib/editor/core/path_text.spl` (12): `editor_clean_relative_dir`, `editor_digit_value`, `editor_dirname`, `editor_find_text`, `editor_join_path`, `editor_last_dot`, `editor_parse_i64`, `editor_payload_csv`, `editor_payload_part`, `editor_split_path_list`, `editor_text_list_contains`, `editor_text_list_without_first`
- `src/lib/editor/extensions/host.spl` (3): `extension_debug_adapter_id`, `extension_debug_adapter_program`, `extension_host_with_builtins`
- `src/lib/editor/render/md_renderer.spl` (1): `md_render_blocks_for_tui_with_wiki`
- `src/lib/editor/services/debug_session_dap_protocol.spl` (9): `editor_debug_dap_event_name`, `editor_debug_dap_event_status`, `editor_debug_dap_event_summary`, `editor_debug_dap_message_type`, `editor_debug_dap_response_success`, `editor_debug_evaluate_result_from_dap_response`, `editor_debug_scopes_from_dap_response`, `editor_debug_stack_frames_from_dap_response`, `editor_debug_variables_from_dap_response`
- `src/lib/editor/services/debug_session_dap.spl` (13): `editor_debug_dap_client_continue_thread`, `editor_debug_dap_client_disconnect`, `editor_debug_dap_client_pause_thread`, `editor_debug_dap_client_poll_messages`, `editor_debug_dap_client_restart`, `editor_debug_dap_client_scopes`, `editor_debug_dap_client_set_breakpoints`, `editor_debug_dap_client_set_exception_breakpoints`, `editor_debug_dap_client_stack_trace`, `editor_debug_dap_client_step_thread`, `editor_debug_dap_client_variables`, `editor_debug_dap_stop_process_pid`, `editor_debug_launch_config_dap_arguments`
- `src/lib/editor/services/debug_session_registry.spl` (33): `editor_debug_add_breakpoint`, `editor_debug_add_watch`, `editor_debug_breakpoint_path`, `editor_debug_compound_as_launch_config`, `editor_debug_compound_configs_from_json`, `editor_debug_console_append`, `editor_debug_continue`, `editor_debug_dap_inbound_message_type`, `editor_debug_dap_inbound_raw_json`, `editor_debug_evaluate`, `editor_debug_evaluate_result`, `editor_debug_launch_config_default`, `editor_debug_launch_config_detail`, `editor_debug_launch_config_is_compound`, `editor_debug_launch_config_matches_type`, `editor_debug_launch_config_program`, `editor_debug_launch_configs_from_json`, `editor_debug_launch_config_with_program`, `editor_debug_pause`, `editor_debug_registry_new`, `editor_debug_registry_restart`, `editor_debug_registry_start_fresh`, `editor_debug_registry_terminate`, `editor_debug_resolve_launch_config`, `editor_debug_select_launch_config`, `editor_debug_session_at`, `editor_debug_session_breakpoints`, `editor_debug_session_config`, `editor_debug_session_count`, `editor_debug_session_wiki_panel`, `editor_debug_set_exception_filters`, `editor_debug_set_status`, `editor_debug_step`
- `src/lib/editor/services/diagnostics.spl` (1): `diagnostics_gutter_icon`
- `src/lib/editor/services/lsp_transport.spl` (7): `lsp_build_did_change_params`, `lsp_build_did_open_params`, `lsp_build_initialize_params`, `lsp_build_position_params`, `lsp_is_response`, `lsp_parse_response_id`, `lsp_parse_response_result`
- `src/lib/editor/services/md_diagnostics.spl` (2): `md_check_frontmatter_property_schema`, `md_property_schema_rule`
- `src/lib/editor/services/md_document_decor.spl` (3): `md_document_body_without_decor`, `md_document_decor_parse`, `md_document_render_office_html`
- `src/lib/editor/services/md_lsp_config.spl` (5): `md_lsp_notify_watched_file`, `md_lsp_notify_workspace_folder`, `md_lsp_poll_all_notifications`, `md_lsp_poll_all_responses`, `md_lsp_state_new`
- `src/lib/editor/services/md_search.spl` (9): `md_vault_search_index_apply_file_change`, `md_vault_search_index_load`, `md_vault_search_index_matches_documents`, `md_vault_search_index_new`, `md_vault_search_index_refresh`, `md_vault_search_index_save`, `md_vault_search_index_search`, `md_vault_search_query_replace_kind_filter`, `md_vault_search_query_replace_path_filter`
- `src/lib/editor/services/md_wiki_index.spl` (13): `md_wiki_backlinks`, `md_wiki_daily_note_config_with_title`, `md_wiki_daily_note_content`, `md_wiki_daily_note_path`, `md_wiki_graph_edges`, `md_wiki_index_documents`, `md_wiki_is_attachment_target`, `md_wiki_parse_link_target`, `md_wiki_properties_for_path`, `md_wiki_quick_switch`, `md_wiki_tags`, `md_wiki_tasks_filtered`, `md_wiki_transclusion_content`
- `src/lib/editor/services/simple_lsp_config.spl` (6): `simple_lsp_change_active`, `simple_lsp_notify_watched_file`, `simple_lsp_notify_workspace_folder`, `simple_lsp_poll_all_notifications`, `simple_lsp_poll_all_responses`, `simple_lsp_state_new`
- `src/lib/editor/view/diagnostics_panel.spl` (10): `diagnostics_panel_from_store`, `diagnostics_panel_from_store_filtered`, `diagnostics_panel_from_store_grouped`, `diagnostics_panel_from_store_sorted`, `diagnostics_panel_new`, `diagnostics_panel_render`, `diagnostics_panel_select`, `diagnostics_panel_target_col`, `diagnostics_panel_target_line`, `diagnostics_panel_target_path`
- `src/lib/editor/view/layout.spl` (4): `editor_layout_active_group_index`, `editor_layout_group_at`, `editor_layout_group_count_raw`, `layout_new`
- `src/lib/editor/view/lsp_popup.spl` (3): `lsp_hover_popup_from_panel`, `lsp_hover_popup_show`, `lsp_signature_popup_from_panel`
- `src/lib/editor/view/lsp_result_panel.spl` (12): `lsp_result_panel_from_response`, `lsp_result_panel_pending`, `lsp_result_panel_render`, `lsp_result_panel_target_col`, `lsp_result_panel_target_command`, `lsp_result_panel_target_command_payload`, `lsp_result_panel_target_line`, `lsp_result_panel_target_path`, `lsp_result_panel_toggle_expanded`, `lsp_result_panel_with_call_children`, `lsp_result_panel_workspace_edit_preview`, `lsp_result_title`
- `src/lib/editor/view/md_editing.spl` (8): `md_apply_result`, `md_assist_on_tab`, `md_command_result_state`, `md_editor_state_outline_visible`, `md_editor_state_preview_visible`, `md_tasks_set_checked`, `md_vim_open_link_under_cursor`, `md_vim_toggle_fold_heading`
- `src/lib/editor/view/outline_panel.spl` (1): `outline_panel_target_line`
- `src/lib/editor/view/split_tree.spl` (2): `split_tree_leaf`, `split_tree_split`
- `src/lib/editor/view/wiki_panel.spl` (13): `wiki_panel_from_backlinks`, `wiki_panel_from_documents`, `wiki_panel_from_graph_edges_with_index`, `wiki_panel_from_properties`, `wiki_panel_from_tags`, `wiki_panel_from_tasks`, `wiki_panel_from_vault_search`, `wiki_panel_new`, `wiki_panel_render`, `wiki_panel_render_row`, `wiki_panel_target_line`, `wiki_panel_target_path`, `wiki_property_form_fields`
- `src/lib/editor/view/wincmd.spl` (4): `wincmd_dispatch`, `wincmd_result_handled`, `wincmd_result_message`, `wincmd_result_quit`
- `src/lib/gc_async_mut/lsp/lsp_json.spl` (17): `ERROR_INTERNAL_ERROR`, `extract_field`, `extract_id`, `extract_nested`, `extract_nested_raw`, `jo1`, `jo2`, `jo3`, `jp`, `js`, `LB`, `make_error`, `make_json_result`, `Q`, `RB`, `SB_L`, `SB_R`
- `src/lib/nogc_async_mut/lsp/lsp_json.spl` (17): `ERROR_INTERNAL_ERROR`, `extract_field`, `extract_id`, `extract_nested`, `extract_nested_raw`, `jo1`, `jo2`, `jo3`, `jp`, `js`, `LB`, `make_error`, `make_json_result`, `Q`, `RB`, `SB_L`, `SB_R`
- `src/lib/nogc_sync_mut/sffi/codegen.spl` (1): `cranelift_declare_global_data_with_metadata`
- `src/lib/nogc_sync_mut/ui/html_gui_sffi.spl` (4): `html_gui_begin_session`, `html_gui_end_session`, `html_gui_poll_event`, `html_gui_present`
- `src/os/desktop/shell.spl` (4): `_app_uses_remote_window`, `simpleos_runtime_scene_revision`, `simpleos_runtime_taskbar_revision`, `_sync_launcher_registry_with_manifests`
- `src/os/lib/audio_offload/ivshmem_protocol.spl` (5): `simple_audio_ivshmem_completion_status`, `simple_audio_ivshmem_initialize`, `simple_audio_ivshmem_poll`, `simple_audio_ivshmem_publish_q15`, `simple_audio_ivshmem_release`
- `src/os/services/netstack/tcp_connection.spl` (1): `tcp_trace`
- `src/os/tls13/handshake13.spl` (6): `_append_bytes`, `_byte_buf`, `parse_certificate_body`, `parse_server_hello`, `_push_byte`, `_u8_at`
- `src/os/tls13/record13.spl` (4): `_append_bytes`, `_copy_range`, `record13_decrypt_fd`, `_u8_at`
- `src/os/tls13/tls13_connect_hrr_p256.spl` (1): `_hrr_p256_connect`

### Wave B: `_EvalOps` part files called by `eval.spl` through the `eval_ops` glob facade (16, observed strict refusal)

- `src/compiler/10.frontend/core/interpreter/_EvalOps/access_literal_assign_eval.spl` (13): `eval_index_expr`, `eval_slice_expr`, `eval_array_lit`, `eval_tuple_lit`, `eval_struct_lit`, `eval_dict_lit`, `eval_compound_assign_expr`, `eval_return_expr`, `eval_interpolated_string`, `eval_null_coalesce`, `eval_lambda`, `eval_list_comp`, `eval_dict_comp`
- `src/compiler/10.frontend/core/interpreter/_EvalOps/call_method_eval.spl` (3): `parse_float_text`, `eval_call`, `eval_function_call`

### Wave C: exact braced-facade tier (213)

- `src/app/browser/render_adapter.spl` (1): `render_browser_html`
- `src/app/interpreter/core/execution_guard.spl` (2): `check_loop_safety`, `push_call_depth`
- `src/app/io/_CliCommands/handler_commands.spl` (1): `cli_handle_web`
- `src/app/io/_CliCommands/run_commands.spl` (3): `cli_run_code`, `cli_run_fix`, `cli_run_fmt`
- `src/app/io/_CliCompile/compile_opt_and_driver.spl` (1): `cli_compile`
- `src/app/io/_CliCompile/compile_targets.spl` (1): `cli_native_build`
- `src/app/io/mod.spl` (1): `random_randint`
- `src/app/mcp/assistant/_SessionStore/store_operations.spl` (1): `assistant_store_list_sessions`
- `src/app/spipe_docgen/spipe_docgen/common.spl` (1): `spec_kw_line`
- `src/app/terminal/render_adapter.spl` (1): `render_terminal_html`
- `src/app/ui.render/html_widgets.spl` (1): `render_html_tree`
- `src/app/ui.render/_TuiWidgets/extended_widgets.spl` (1): `render_tui_tree`
- `src/app/ui.web/_HostTaskbarRuntime/host_taskbar_runtime.spl` (30): `host_taskbar_runtime_close`, `host_taskbar_runtime_enable`, `host_taskbar_runtime_focus`, `host_taskbar_runtime_hides_desktop`, `host_taskbar_runtime_hides_taskbar`, `host_taskbar_runtime_is_enabled`, `host_taskbar_runtime_launch`, `host_taskbar_runtime_maximize`, `host_taskbar_runtime_minimize`, `host_taskbar_runtime_mode_name`, `host_taskbar_runtime_move`, `host_taskbar_runtime_native_window_html`, `host_taskbar_runtime_resize`, `host_taskbar_runtime_restore`, `host_taskbar_runtime_set_title`, `host_taskbar_runtime_sync_close`, `host_taskbar_runtime_sync_focus`, `host_taskbar_runtime_sync_maximize`, `host_taskbar_runtime_sync_minimize`, `host_taskbar_runtime_sync_move`, `host_taskbar_runtime_sync_resize`, `host_taskbar_runtime_sync_restore`, `host_taskbar_runtime_sync_set_title`, `host_taskbar_runtime_sync_unmaximize`, `host_taskbar_runtime_take_client_frames`, `host_taskbar_runtime_taskbar_frame`, `host_taskbar_runtime_taskbar_model`, `host_taskbar_runtime_try_pin_app`, `host_taskbar_runtime_try_unpin_app`, `host_taskbar_runtime_unmaximize`
- `src/app/ui.web/html.spl` (1): `generate_css`
- `src/compiler/00.common/_Attributes/decl_attrs.spl` (10): `is_known_asm_clobber`, `is_valid_asm_symbol_name`, `is_volatile`, `parse_driver_manifest_attrs`, `parse_export_attrs`, `parse_function_attrs`, `parse_vhdl_hardware_attrs`, `raw_asm_rejected_directive`, `vhdl_hardware_metadata_default`, `vhdl_hardware_metadata_flat_row_is_valid`
- `src/compiler/00.common/driver_compile_options.spl` (3): `compileoptions_effective_mir_opt_level`, `compileoptions_normalize_mir_optimization`, `driver_core_compile_options_default`
- `src/compiler/00.common/driver_compile_result.spl` (2): `compile_result_errors`, `compile_result_is_success`
- `src/compiler/00.common/driver_core_modes.spl` (6): `driver_output_format_both`, `driver_output_format_is_both`, `driver_output_format_is_self_contained`, `driver_output_format_is_smf`, `driver_output_format_native`, `driver_output_format_smf`
- `src/compiler/00.common/driver_source_file.spl` (1): `source_file_authored_path`
- `src/compiler/00.common/runtime_value_v1.spl` (12): `backend_value_array_v1`, `backend_value_bool_v1`, `backend_value_closure_v1`, `backend_value_dict_v1`, `backend_value_float_v1`, `backend_value_function_v1`, `backend_value_int_v1`, `backend_value_object_v1`, `backend_value_runtime_value_v1`, `backend_value_string_v1`, `backend_value_struct_v1`, `backend_value_tuple_v1`
- `src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl` (9): `parse_module_body`, `parser_class_attributes_for`, `parser_enum_attributes_for`, `parser_enum_open_regions_for`, `parser_is_class_decl_v1`, `parser_parse_member_attribute`, `parser_unsafe_annotation_caps`, `parser_unsafe_annotation_present`, `parser_unsafe_annotation_reason`
- `src/compiler/10.frontend/core/_ParserDecls/extend_decls.spl` (7): `parser_extend_closures`, `parser_extend_ctor_counts`, `parser_extend_ctor_names`, `parser_extend_ctor_providers`, `parser_extend_ctor_type_counts`, `parser_extend_ctor_type_ids`, `parser_extend_targets`
- `src/compiler/10.frontend/core/_ParserDecls/fn_struct_decls.spl` (3): `parser_generic_constraints_reset`, `parser_skip_mut_if_present`, `parse_type_params`
- `src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl` (1): `parse_primary_expr`
- `src/compiler/10.frontend/frontend.spl` (1): `parse_full_frontend`
- `src/compiler/50.mir/mir_instruction_support.spl` (1): `mir_operand_copy`
- `src/compiler/60.mir_opt/_OptimizationPasses/io_passes.spl` (3): `optimize_read_ahead_hoist`, `optimize_syscall_batch`, `optimize_write_coalesce`
- `src/compiler/90.tools/duplicate_check/_Detector/interner_and_logging.spl` (2): `find_duplicates_in_file`, `new_token_interner`
- `src/compiler/90.tools/duplicate_check/_Detector/similarity_grouping.spl` (3): `collect_files`, `find_duplicates`, `find_duplicates_with_options`
- `src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl` (2): `run_lint_file`, `run_lint_source_with_linter_policy`
- `src/compiler/99.loader/module_loader_compat.spl` (1): `moduleloader_execute_smf`
- `src/lib/common/json/serializer.spl` (1): `json_escape_string`
- `src/lib/common/ui/access_query.spl` (5): `ui_access_ensure_result`, `ui_access_find_nodes_filtered`, `ui_access_query_result`, `ui_access_query_to_json`, `ui_access_snapshot_to_json`
- `src/lib/common/ui/access_snapshot.spl` (2): `ui_access_recent_events`, `ui_access_snapshot_from_state`
- `src/lib/common/ui/access_types.spl` (1): `ui_access_canonical_id`
- `src/lib/common/ui/window_scene_draw_ir.spl` (3): `wm_taskbar_dock_width`, `wm_taskbar_item_width`, `wm_taskbar_item_x`
- `src/lib/nogc_sync_mut/database/vector/types.spl` (1): `default_vector_config`
- `src/os/compositor/diff_export.spl` (1): `export_comparison_ppm`
- `src/os/compositor/electron_capture.spl` (3): `capture_electron`, `capture_electron_scene`, `capture_error`
- `src/os/compositor/perceptual_compare.spl` (1): `compare_perceptual`
- `src/os/compositor/qemu_capture.spl` (1): `capture_qemu_vm`
- `src/os/compositor/screenshot_compare.spl` (4): `compare_exact`, `compare_pixel_buffers`, `find_diff_regions`, `generate_diff_image`
- `src/os/compositor/tolerance_profile.spl` (3): `profile_strict`, `profile_text_tolerant`, `profile_wm_default`
- `src/os/desktop/taskbar_shell.spl` (1): `build_taskbar_shell_tree`
- `src/os/kernel/arch/user_entry_bridge.spl` (2): `dispatch_enter_user_blocking`, `dispatch_fs_exec_user_handoff`
- `src/os/kernel/fd_io.spl` (4): `posix_close`, `posix_dup`, `posix_dup2`, `posix_read`
- `src/os/kernel/fd_table.spl` (3): `fd_poll_notification`, `fd_poll_ready`, `fd_table_init`
- `src/os/kernel/memory/vmm_device_mapping.spl` (1): `vmm_map_device_result`
- `src/os/kernel/pipe_compat.spl` (1): `posix_pipe`
- `src/os/kernel/process_compat.spl` (2): `posix_kill`, `posix_spawn_with_args`
- `src/os/port/_SimpleosMultiplatformBuild/platform_target_accessors.spl` (33): `simpleos_machine_target_known`, `simpleos_machine_target_projection`, `simpleos_platform_arch_name`, `simpleos_platform_artifact_slug`, `simpleos_platform_asm_flags`, `simpleos_platform_board_lane_direct`, `simpleos_platform_boot_asm_sources`, `simpleos_platform_boot_c_sources`, `simpleos_platform_boot_impl_kind`, `simpleos_platform_c_flags`, `simpleos_platform_clang_target`, `simpleos_platform_disk_image_output`, `simpleos_platform_float_abi`, `simpleos_platform_grandfathered_native_sources`, `simpleos_platform_has_board_lane`, `simpleos_platform_has_qemu_lane`, `simpleos_platform_isa`, `simpleos_platform_kernel_output`, `simpleos_platform_needs_soft_float_runtime`, `simpleos_platform_qemu_acceptance_lane`, `simpleos_platform_qemu_cpu`, `simpleos_platform_qemu_lane`, `simpleos_platform_qemu_lane_or_smoke`, `simpleos_platform_qemu_lane_required_markers`, `simpleos_platform_qemu_lane_timeout_ms`, `simpleos_platform_qemu_machine`, `simpleos_platform_qemu_smoke_lane`, `simpleos_platform_runtime_impl_kind`, `simpleos_platform_standalone_asm_policy`, `simpleos_platform_target_names`, `simpleos_platform_userland_abi`, `simpleos_platform_userland_firmware_contract`, `simpleos_platform_userland_target`
- `src/os/_QemuRunner/os_build_run.spl` (8): `arch_display_name`, `arch_from_name`, `build_os`, `build_os_with_backend`, `build_qemu_command`, `get_all_targets`, `run_os`, `run_os_debug_gui`
- `src/os/_QemuRunner/runner_targets.spl` (5): `get_desktop_browser_target`, `get_qemu_target`, `get_target`, `get_wm_simple_web_check_target`, `qemu_default_arch`
- `src/os/_QemuRunner/scenario_catalog.spl` (4): `scenario_by_name_direct`, `scenario_exists`, `test_all_architectures`, `test_os`
- `src/os/_QemuRunner/scenario_disks.spl` (5): `_catalog_has_lane_for_scenario`, `_catalog_platform_name_for_scenario`, `ensure_desktop_disk_image`, `scenario_target`, `_x64_nvme_disk_args`
- `src/os/_QemuRunner/scenario_exec.spl` (5): `build_scenario`, `ensure_scenario_media`, `run_scenario`, `scenario_test_timeout_ms`, `test_scenario`

### Wave D: glob-facade tier (89) + observed `mir_provider_session_content_key_v1` (90)

A cross-dir product file glob-imports a facade that glob re-exports the definer, and calls the name.

- `src/app/svim/_SvimCore/text_ops.spl` (2): `svim_parse_normal_command`, `svim_snapshot_text`
- `src/compiler/10.frontend/core/_Ast/decl_nodes.spl` (18): `decl_body_stmts_at`, `decl_field_defaults_at`, `decl_field_names_at`, `decl_field_types_at`, `decl_get_impl_trait`, `decl_get_impl_with_trait`, `decl_get_type_param_constraints`, `decl_imports_at`, `decl_is_async_at`, `decl_is_lazy_at`, `decl_name_at`, `decl_param_names_at`, `decl_param_types_at`, `decl_ret_type_at`, `decl_set_param_muts`, `decl_tag_at`, `decl_visibility_at`, `decl_visibility_len`
- `src/compiler/10.frontend/core/_AstExpr/accessors.spl` (10): `expr_get_arg_names`, `expr_get_args`, `expr_get_call_type_args`, `expr_get_extra`, `expr_get_int`, `expr_get_left`, `expr_get_right`, `expr_get_stmts`, `expr_get_str`, `expr_get_tag`
- `src/compiler/10.frontend/core/_AstExpr/nodes.spl` (26): `asm_arm_owner_abi`, `asm_arm_owner_archs`, `asm_arm_owner_asm_text`, `asm_arm_owner_backend`, `asm_arm_owner_error_msg`, `asm_arm_owner_is_compile_error`, `asm_arm_owner_is_wildcard`, `asm_arm_owner_os`, `asm_arm_owner_ver_ops`, `asm_arm_owner_ver_vals`, `ast_generation_bump`, `expr_count`, `expr_ident`, `expr_owner_args`, `expr_owner_extra`, `expr_owner_float`, `expr_owner_int`, `expr_owner_left`, `expr_owner_len`, `expr_owner_right`, `expr_owner_span`, `expr_owner_stmts`, `expr_owner_str`, `expr_owner_tag`, `expr_reset`, `expr_set_call_type_args`
- `src/compiler/10.frontend/core/_Ast/module_state.spl` (4): `ast_reset_seq_get`, `module_add_decl`, `module_decl_at`, `module_decl_count_get`
- `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl` (1): `flat_bootstrap_function_count`
- `src/compiler/20.hir/hir_lowering/_Expressions/expression_support.spl` (3): `bootstrap_builtin_return_type`, `hir_expr_kind_disc`, `_hir_expr_symbol_or_invalid`
- `src/compiler/35.semantics/perf/collection_plan_explain.spl` (1): `collection_plan_explain`
- `src/compiler/35.semantics/perf/collection_plan_selection.spl` (1): `collection_plan_select`
- `src/compiler/50.mir/mir_instruction_support.spl` (2): `mir_operand_const_int`, `mir_operand_move`
- `src/compiler/50.mir/_MirLowering/bootstrap_globals.spl` (3): `bootstrap_lower_hir_globals_to_mir_module_for_target`, `bootstrap_mir_static_alignment_at`, `bootstrap_mir_static_visibility_at`
- `src/compiler/50.mir/_MirLowering/module_lowering.spl` (1): `mir_provider_session_content_key_v1`
- `src/compiler/70.backend/linker/_LinkerWrapper/shared_linking.spl` (1): `link_to_shared`
- `src/compiler/90.tools/lint/_LintMain/name_lints.spl` (1): `lint_accessor_and_parent_names`
- `src/os/_QemuRunner/runner_targets.spl` (12): `_now_ms`, `_os_build_backend_for_target`, `_os_build_log_mode`, `_os_build_timeout_ms`, `_print_native_build_failure_hint`, `_qemu_command_binary`, `qemu_run_options_debug_gui`, `qemu_run_options_default`, `qemu_run_options_headless`, `_tail_lines`, `_write_bootstrap_result`, `_write_native_build_failure_log`
- `src/os/tls13/_CertVerify/signature_verify.spl` (4): `extract_ed25519_pubkey_from_cert`, `extract_rsa_pubkey_spki_from_cert`, `verify_cert_chain`, `verify_certificate_verify_msg_scheme`
