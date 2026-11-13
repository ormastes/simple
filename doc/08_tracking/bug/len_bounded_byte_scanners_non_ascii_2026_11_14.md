# len()-bounded byte scanners truncate non-ASCII text (2026-11-14)

Status: open (caller migration). Severity: P2. Owner area: lib/app/compiler callers.

## Finding
The seed is NOT inconsistent with pure Simple here. The owner decision of
2026-11-07 (doc/05_design/language/text/text_len_counts_characters_2026-11-07.md,
quick reference "Length and slicing units") fixes the units: `len()`, `s[i]`,
`s[a:b]` = code points; `byte_len`, `byte_at`, `substring`, `slice`,
`index_of`, `char_code_at` = UTF-8 byte offsets. Seed interpreter
(interpreter_method/string.rs), JIT/runtime (db56bd08e19) and pure-Simple MIR
(4183b795175) follow it. The defect class is CALLERS that bound a byte scan
with `len()` (PR #9034 llm_caret json_helpers/redact; this PR: lsp_json x3).

## Gate gap
scripts/check/check-text-len-unit-mix.shs flags `byte_len()` + `s[...]` mixes and
`X.len()` widths reaching byte calls, but NOT a function that never calls
`byte_len()` and bounds `substring`/`byte_at` with `len()` - the #9034 shape.

## Census (heuristic: same receiver has .len() and .substring/.byte_at/.char_code_at, no .byte_len())
1003 function/receiver hits in src/lib, src/app, src/compiler. Many are ASCII-only
inputs (paths, identifiers) and harmless; JSON/SDN/LSP/protocol readers are real.
High-risk subset (json/sdn/lexer/escape/base64/redact/token/parse in path or name):

- src/app/bootstrap_builder/parser_qualification_parent_cache.spl:13 fn parser_qualification_source_fingerprint_v1 recv=value
- src/app/bootstrap_builder/parser_qualification_parent_cache.spl:23 pub fn parser_qualification_parent_cache_v1 recv=raw
- src/app/ci/pipeline_runner.spl:317 fn canonical_runtime_token recv=value
- src/app/cli/query_ast_query.spl:56 fn _parse_ast_pattern recv=rest
- src/app/cli/query_commands.spl:399 fn query_semantic_tokens recv=line
- src/app/cli/query_diagnostics.spl:268 fn _collect_check_output_diagnostics_json_clean recv=clean_output
- src/app/cli/query_helpers.spl:95 fn _classify_token recv=line
- src/app/cli/query_helpers.spl:95 fn _classify_token recv=word
- src/app/cli/query_tokens.spl:18 fn query_semantic_tokens recv=line
- src/app/cli/query_tokens.spl:148 fn query_inlay_hints recv=trimmed
- src/app/cli/query_tokens.spl:148 fn query_inlay_hints recv=after_name
- src/app/cli/query_tokens.spl:239 fn _emit_param_hints_for_line recv=line
- src/app/cli/query_tokens.spl:283 fn _extract_call_arg_positions recv=line
- src/app/cli/query_tokens.spl:326 fn _skip_whitespace recv=line
- src/app/cli/query_tokens.spl:336 fn _get_arg_text_at recv=line
- src/app/cli_debug/_DebugCommands/session_and_backend.spl:63 fn extract_json_field recv=after
- src/app/cli_debug/_DebugCommands/session_and_backend.spl:63 fn extract_json_field recv=content
- src/app/compile/c_helpers.spl:123 fn parse_fn_signature recv=without_fn
- src/app/compile/c_helpers.spl:415 fn parse_method_signature recv=without_prefix
- src/app/desugar/lazy_proxy_gen.spl:195 fn parse_proxy_annotation recv=trimmed
- src/app/doc/public_check/export_parser.spl:36 fn parse_export_list recv=name
- src/app/doc/public_check/export_parser.spl:91 fn parse_export_statements recv=trimmed
- src/app/isa_registry/parser.spl:19 fn check_id recv=value
- src/app/isa_registry/parser.spl:27 fn check_digest recv=value
- src/app/isa_registry/parser.spl:116 fn peek recv=ch
- src/app/isa_registry/parser.spl:116 fn peek recv=self.source
- src/app/jupyter_kernel/protocol.spl:71 fn extract_field_raw recv=json
- src/app/llm_caret/claude_api.spl:44 fn _extract_json_string recv=rest
- src/app/llm_caret/claude_api.spl:69 fn _extract_json_value recv=trimmed
- src/app/llm_caret/claude_full/bridge/jwtUtils.spl:288 fn parseLeadingInt recv=value
- src/app/llm_caret/claude_full/bridge/workSecret.spl:110 fn parseSafeInteger recv=value
- src/app/llm_caret/cs_container.spl:134 fn _cs_container_token recv=value
- src/app/llm_caret/messaging/adapter/server/primitive_dispatch.spl:27 fn primitive_http_text recv=json
- src/app/llm_caret/messaging/adapter/server/primitive_dispatch.spl:42 fn primitive_http_i64 recv=json
- src/app/llm_caret/messaging/mcp/protocol.spl:84 fn arg_text recv=json
- src/app/llm_caret/messaging/mcp/protocol.spl:102 fn arg_i64 recv=json
- src/app/llm_caret/openai_api.spl:44 fn _extract_json_string recv=rest
- src/app/llm_caret/openai_api.spl:69 fn _extract_json_value recv=trimmed
- src/app/llm_caret/redact.spl:198 fn _match_env_assignment recv=s
- src/app/llm_caret/redact.spl:241 fn _redact_ascii_run recv=text_in
- src/app/llm_caret/server.spl:58 fn _extract_json_string recv=rest
- src/app/llm_caret/session.spl:79 fn _extract_object_at recv=json
- src/app/llm_caret/session.spl:109 fn _extract_json_string recv=rest
- src/app/llm_caret/session.spl:132 fn _extract_json_int recv=after
- src/app/llm_caret/session.spl:183 fn parse_messages_array recv=json
- src/app/llm_caret/tools.spl:100 fn _json_get_str recv=rest
- src/app/llm_caret/tools.spl:126 fn _json_get_int recv=after
- src/app/llm_caret/tools.spl:536 fn _extract_object_at recv=json
- src/app/llm_caret/tools.spl:584 fn parse_tool_use_blocks recv=src
- src/app/llm_caret/tools.spl:612 fn parse_tool_use_tags recv=content
- src/app/mcp/main_lazy_json.spl:14 fn first_n_chars recv=s
- src/app/mcpgdb/json_helpers.spl:65 fn extract_string_field_with_pattern recv=json
- src/app/mcpgdb/json_helpers.spl:85 fn extract_field_raw recv=json
- src/app/protocol/framing.spl:47 fn frame_parse_decimal recv=s
- src/app/scv/db/github_provider.spl:95 fn db_github_json_depth recv=body
- src/app/search/render_adapter.spl:260 fn highlight_html recv=escaped_content
- src/app/spipe/model/canonical.spl:68 fn _json_escape recv=s
- src/app/test_dep_graph_shared.spl:317 fn dep_graph_unescape_text recv=s
- src/app/ui/renderdoc_diff/jsonflat.spl:148 fn json_pair_has_prefix recv=path
- src/app/verify/tooling_gate.spl:153 fn parse_git_status_output recv=line
- src/app/wm_compare/electron_geometry_compare.spl:39 fn _geometry_json_i32_after recv=rest
- src/app/wm_compare/graphical_backend_equality.spl:101 fn _parse_component_kind recv=component
- src/app/wm_compare/graphical_backend_equality.spl:107 fn _parse_component_name recv=component
- src/app/wm_compare/site_corpus_compat.spl:421 fn _json_number_after recv=rest
- src/app/wm_compare/site_corpus_layout_report.spl:325 fn _chrome_canvas_widths_sdn recv=width_rest
- src/app/wm_compare/site_corpus_layout_report.spl:325 fn _chrome_canvas_widths_sdn recv=section
- src/compiler/00.common/cache/phase_compatibility_manifest.spl:216 fn phase_compatibility_token_v1 recv=frame
- src/compiler/00.common/cache/reverse_reference_key.spl:133 fn reverse_reference_parse_text_token_v1 recv=frame
- src/compiler/00.common/cache/reverse_reference_key.spl:149 fn reverse_reference_parse_nat_token_v1 recv=frame
- src/compiler/00.common/cache/reverse_reference_key.spl:161 fn reverse_reference_parse_field_text_v1 recv=frame
- src/compiler/00.common/cache/reverse_reference_key.spl:168 fn reverse_reference_parse_field_nat_v1 recv=frame
- src/compiler/00.common/cache_contract/hir_cache_envelope_reader_v1.spl:63 pub fn hir_cache_envelope_parse recv=checksum_line
- src/compiler/10.frontend/cache_artifact/generic_tldr_projector.spl:95 fn _parse_type recv=s
- src/compiler/10.frontend/cache_artifact/macro_source_from_parse_v1.spl:166 fn _indent_of recv=line
- src/compiler/10.frontend/cache_artifact/macro_source_from_parse_v1.spl:175 fn _header_params recv=inner
- src/compiler/10.frontend/core/_ParserPrimary/asm_match_suffix.spl:156 fn parse_int_text recv=txt
- src/compiler/10.frontend/core/_ParserStmt/match_type_pattern.spl:34 fn parser_type_pattern_name_is_type recv=name
- src/compiler/10.frontend/core/parser_preprocessor.spl:390 fn _pp_leading_ws recv=line
- src/compiler/10.frontend/effect_registry.spl:118 fn effect_parse_budget recv=raw
- src/compiler/10.frontend/frontend_shared_parse_cas_v1.spl:83 fn _shared_parse_payload_has_host_path_v1 recv=normalized
- src/compiler/10.frontend/frontend_shared_parse_cas_v1.spl:92 fn _shared_parse_absolute_v1 recv=normalized
- src/compiler/35.semantics/lint/concurrency_api_misuse.spl:103 fn _cam_is_token recv=line
- src/compiler/70.backend/backend/llvm_version.spl:46 fn parse_llvm_version recv=cleaned
- src/compiler/70.backend/linker/riscv_arch_attributes.spl:38 fn riscv_isa_parse recv=token
- src/compiler/80.driver/cache/module_tldr_sections_v1.spl:127 pub fn module_tldr_sections_parse_v1 recv=rest
- src/compiler/80.driver/driver_build/go_to_end.spl:208 pub fn go_to_end_sdn_quote_v1 recv=value
- src/compiler/80.driver/driver_build/managed_parse_qualification.spl:83 fn managed_parse_qualification_evidence_v2 recv=value.worker_path
- src/compiler/80.driver/driver_build/native_staged_codegen.spl:109 pub fn native_staged_codegen_batch_parse_v1 recv=raw
- src/compiler/80.driver/driver_compile_vhdl_source_map.spl:506 fn _json_escape recv=value
- src/compiler/80.driver/driver_compile_vhdl_source_map.spl:653 fn _extract_json_field_i64 recv=tail
- src/compiler/80.driver/driver_hir_cache.spl:1208 fn _hir_cache_token recv=t
- src/compiler/80.driver/driver_managed_parse_group_main.spl:11 fn managed_parse_group_worker_main_v1 recv=name
- src/compiler/80.driver/driver_vhdl_artifacts.spl:620 fn vhdl_artifact_json_escape recv=value
- src/compiler/90.tools/duplicate_check/ollama_client.spl:80 fn parse_first_float_array recv=json
- src/compiler/90.tools/duplicate_check/ollama_client.spl:111 fn parse_float_array_from recv=json
- src/compiler/90.tools/leak_check/growth_runner.spl:20 fn _extract_numeric_token recv=trimmed
- src/compiler/90.tools/leak_check/internal_runner.spl:15 fn parse_mem_available_kb recv=after
- src/compiler/90.tools/leak_check/parser.spl:140 fn extract_number_before recv=before
- src/compiler/90.tools/leak_check/parser.spl:168 fn extract_number_after recv=trimmed
- src/compiler/90.tools/leak_check/static_runner.spl:72 fn parse_function_name recv=after
- src/compiler/90.tools/lint/_LintMain/os_freestanding_lints.spl:28 fn _fsk_trailing_ident_token recv=s
- src/compiler/90.tools/lint/_LintMain/os_freestanding_lints.spl:43 fn _fsk_leading_ident_token recv=s
- src/lib/blink/css_parser/selector.spl:108 fn str_split_char recv=s
- src/lib/blink/css_parser/selector.spl:122 fn str_trim recv=s
- src/lib/blink/css_parser/selector.spl:180 fn parse_compound recv=attr_name
- src/lib/blink/css_parser/selector.spl:180 fn parse_compound recv=raw
- src/lib/blink/css_parser/selector.spl:258 fn parse_selector recv=selector_text
- src/lib/blink/html_parser/tokenizer.spl:59 fn tokenize_html recv=html
- src/lib/common/config_core/schema.spl:201 pub fn config_parse_int recv=s
- src/lib/common/contracts/container/bound_intent_v2.spl:13 fn intent_token_v2 recv=value
- src/lib/common/contracts/container/host_capability_sdn_v1.spl:33 fn _decode_v1 recv=value
- src/lib/common/convert.spl:142 fn parse_positive_i64_exact_or_zero recv=value
- src/lib/common/css/length.spl:195 fn _tokenize recv=src
- src/lib/common/encoding/font_cldr_rank.spl:120 fn _cldr_parse_positive_i64 recv=raw
- src/lib/common/encoding/font_cldr_rank.spl:136 fn _cldr_parse_percent_micros recv=raw
- src/lib/common/encoding/font_cldr_rank.spl:191 fn _cldr_first_token recv=value
- src/lib/common/sdn/structural_inline_lexer_v2.spl:44 fn _inline_tokens_v2 recv=source
- src/lib/common/sdn/value.spl:251 fn _sdn_index recv=key
- src/lib/common/search/query_exec.spl:149 fn _json_quote recv=s
- src/lib/common/structural/hal_provider/config.spl:91 fn _hal_parse_enabled recv=value
- src/lib/common/structural/hal_provider/config.spl:112 fn hal_runtime_config_parse_v1 recv=source
- src/lib/common/text.spl:44 fn escape_json recv=ch
- src/lib/common/ui/theme_sync_sdn.spl:401 fn _split_kv recv=line
- src/lib/common/web/browser_renderer_protocol.spl:2137 fn _browser_renderer_base64_decoded_length recv=value
- src/lib/editor/view/md_editing.spl:801 fn _md_parse_i64 recv=raw
- src/lib/gc_async_mut/gpu/browser_engine/chrome_webgpu_draw_evidence.spl:45 fn _json_i64 recv=token
- src/lib/gc_async_mut/gpu/browser_engine/chrome_webgpu_draw_evidence.spl:69 fn _parse_i32_token recv=t
- src/lib/gc_async_mut/gpu/browser_engine/html_tokenizer.spl:570 fn _named_reference_text_less recv=left
- src/lib/gc_async_mut/gpu/browser_engine/html_tokenizer.spl:570 fn _named_reference_text_less recv=right
- src/lib/gc_async_mut/gpu/browser_engine/security/origin_policy.spl:60 fn _parse_port recv=raw
- src/lib/gc_async_mut/gpu/browser_engine/security/origin_policy.spl:98 fn _is_scheme_token recv=scheme
- src/lib/gc_async_mut/gpu/browser_engine/security/origin_policy.spl:112 fn _is_host_token recv=host
- src/lib/gc_async_mut/gpu/browser_engine/simple_web_fractional_box_resolver.spl:135 fn _web_fractional_rotate_translate recv=rotation_token
- src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core_selectors.spl:905 fn parse_selector_part recv=sel
- src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_foundation.spl:2267 fn css_timing_shorthand_tokens recv=raw
- src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_style.spl:726 fn parse_font_shorthand_family recv=s
- src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_style.spl:790 fn parse_float_to_255 recv=t
- src/lib/gc_async_mut/gpu/browser_engine/style/custom_properties.spl:277 pub fn parse_var_function recv=value
- src/lib/nogc_async_mut/container/providers/linux/engine_policy_v1.spl:161 fn _engine_json_depth_v1 recv=source
- src/lib/nogc_async_mut/container/providers/linux/oci_runtime_v1.spl:2079 fn _safe_token recv=value
- src/lib/nogc_async_mut/container/providers/windows/docker_engine_codec_v3.spl:464 pub fn windows_engine_http_parse_v3 recv=status_line
- src/lib/nogc_async_mut/debug/remote/protocol/gdb_mi_parser.spl:228 static fn unescape_mi_string recv=raw
- src/lib/nogc_async_mut/df/df_io.spl:113 fn parse_csv_f64 recv=value
- src/lib/nogc_async_mut/df/df_io.spl:166 fn parse_iso_date_days recv=value
- src/lib/nogc_async_mut/llm/json_helpers.spl:111 fn extract_json_string recv=rest
- src/lib/nogc_async_mut/llm/json_helpers.spl:138 fn extract_json_value recv=trimmed
- src/lib/nogc_async_mut/mcp/helpers.spl:104 fn extract_json_string_v2 recv=after_colon
- src/lib/nogc_async_mut/mcp/main_lazy_json.spl:78 fn extract_field_raw recv=rest
- src/lib/nogc_async_mut/mcp/main_lazy_json.spl:78 fn extract_field_raw recv=json
- src/lib/nogc_async_mut/mcp/main_lazy_json.spl:209 fn summarize_json_shape recv=inner
- src/lib/nogc_async_mut/mcp/main_lazy_json.spl:272 fn make_tool_result recv=result
- src/lib/nogc_async_mut/mcp/main_lazy_json.spl:285 fn make_tool_error recv=result
- src/lib/nogc_async_mut/mcp/resource_utils.spl:37 pub fn extract_json_string recv=json
- src/lib/nogc_async_mut/mcp/resource_utils.spl:69 pub fn extract_json_int recv=json
- src/lib/nogc_async_mut/mcp/resource_utils.spl:99 fn extract_json_float recv=json
- src/lib/nogc_async_mut/mcp/resource_utils.spl:128 pub fn extract_json_array recv=array_str
- src/lib/nogc_async_mut/mcp/resource_utils.spl:128 pub fn extract_json_array recv=json
- src/lib/nogc_async_mut/package/semver_old.spl:59 fn parse_int_component recv=s
- src/lib/nogc_async_mut/sosix/host_facade.spl:324 fn _parse_pct recv=frac
- src/lib/nogc_async_mut_noalloc/qemu/debug_boot_runner.spl:618 fn parse_hex_value_u64 recv=clean
- src/lib/nogc_sync_mut/composition/abi_digest.spl:43 fn simple_abi_digest_parse_hex_v1 recv=hex
- src/lib/nogc_sync_mut/container_session/podman_session_v1.spl:60 pub fn podman_session_token_valid_v1 recv=value
- src/lib/nogc_sync_mut/database/csm_seal.spl:117 fn csm_parse_tag recv=tag
- src/lib/nogc_sync_mut/database/csm_seal.spl:117 fn csm_parse_tag recv=stem
- src/lib/nogc_sync_mut/database/pure_sql/_PureDatabase/row_value_helpers.spl:224 fn _pdb_decimal_parse_strict recv=value
- src/lib/nogc_sync_mut/database/vector/codec.spl:38 fn _parse_vector_f64 recv=s
- src/lib/nogc_sync_mut/df/df_io.spl:113 fn parse_csv_f64 recv=value
- src/lib/nogc_sync_mut/df/df_io.spl:166 fn parse_iso_date_days recv=value
- src/lib/nogc_sync_mut/game2d/audio/sound_asset_sdn.spl:307 fn _parse_pattern_track recv=steps
- src/lib/nogc_sync_mut/js/engine/runtime.spl:285 static fn create recv=package_json
- src/lib/nogc_sync_mut/mcp_sdk/core/json.spl:299 fn extract_field_raw recv=json
- src/lib/nogc_sync_mut/notebook/magics.spl:68 fn parse_uint_arg recv=t
- src/lib/nogc_sync_mut/rt_hal/virtual_device.spl:87 fn _parse_num recv=s
- src/lib/nogc_sync_mut/rt_hal/virtual_device.spl:101 fn _parse_dec recv=s
- src/lib/nogc_sync_mut/text_layout/font_rasterizer.spl:241 fn _vector_font_parse_i64_decimal recv=raw
- src/lib/nogc_sync_mut/ui/theme_package.spl:944 fn _parse_decimal_i64 recv=trimmed

## Options for the class
1. Migrate callers per file (byte_len bounds) in small PRs, highest-risk first.
2. Extend the unit-mix gate with Rule 3 (len()-bounded byte op, no byte_len)
   as a baselined ratchet so new instances fail at push.
Recommendation: 2 first (stops growth), then 1 by risk.

Spec: test/01_unit/lib/text/text_unit_parity_scanner_spec.spl
