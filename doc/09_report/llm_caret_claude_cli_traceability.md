# LLM Caret Claude CLI Traceability

Date: 2026-07-05

## MDSOC+ Caret Boundary

`src/app/llm_caret` is the app-layer LLM provider caret. It owns provider
selection, CLI/API request construction, response normalization, and lightweight
server compatibility. Runtime I/O stays behind existing app/runtime facades
where available. This lane does not migrate Claude's React terminal UI,
remote-control bridge, OAuth, or full agent orchestration.

## Extracted Claude CLI Features

| Feature group | Claude source evidence | Simple target |
|---|---|---|
| CLI one-shot prompt and output flags | `tmp/claude/claude-code-main/src/entrypoints/cli.tsx`, `tmp/claude/claude-code-main/src/entrypoints/sdk/coreSchemas.ts` | `src/app/llm_caret/claude_cli.spl`, `provider.spl`, `mod.spl` |
| Message/session response normalization | `src/QueryEngine.ts`, `src/bootstrap/state.ts`, `src/types/logs.ts` | `claude_cli.spl`, `types.spl`, `chat.spl` |
| Tool/provider routing concept | `src/Tool.ts`, `src/constants/tools.ts`, `src/entrypoints/sdk/coreSchemas.ts` | `provider.spl`, `config.spl` |
| API-compatible request body and headers | `src/services/api/claude.js` reference from `src/QueryEngine.ts`, `src/entrypoints/sdk/coreSchemas.ts` | `claude_api.spl`, `openai_api.spl`, `openai_compat.spl` |
| Local history/state | `src/bootstrap/state.ts`, `src/assistant/sessionHistory.ts` | `chat.spl`, `mod.spl` |
| Compatibility server surface | `src/entrypoints/mcp.ts`, `src/entrypoints/sdk/coreSchemas.ts` | `server.spl` |

## Source File Mapping

| Simple source file | LOC | Role |
|---|---:|---|
| `src/app/llm_caret/agent_discovery.spl` | 85 | Agent capability discovery |
| `src/app/llm_caret/agent_files.spl` | 23 | Agent file change detection and snapshots |
| `src/app/llm_caret/agent_mailbox.spl` | 39 | Agent team messaging and coordination |
| `src/app/llm_caret/agent_manager_view.spl` | 111 | Agent manager UI view rendering |
| `src/app/llm_caret/agent_plan.spl` | 223 | Agent launch and review planning |
| `src/app/llm_caret/agent_runtime.spl` | 200 | Agent process execution and monitoring |
| `src/app/llm_caret/agent_tmux.spl` | 56 | Agent tmux pane integration |
| `src/app/llm_caret/agent_tui.spl` | 38 | Agent terminal UI components |
| `src/app/llm_caret/agent_vcs.spl` | 43 | Agent version control operations |
| `src/app/llm_caret/agent_workspace.spl` | 679 | Agent workspace management |
| `src/app/llm_caret/chat.spl` | 228 | Conversation history and message JSON |
| `src/app/llm_caret/chat_tui.spl` | 840 | Chat terminal UI implementation |
| `src/app/llm_caret/claude_api.spl` | 318 | Anthropic Messages API request/response |
| `src/app/llm_caret/claude_cli.spl` | 581 | Claude CLI argv and JSON/stream parsing |
| `src/app/llm_caret/codex_cli.spl` | 111 | Codex CLI integration |
| `src/app/llm_caret/config.spl` | 624 | Provider config and defaults |
| `src/app/llm_caret/cs_dashboard.spl` | 726 | Code search integration |
| `src/app/llm_caret/cs_main.spl` | 375 | Code search integration |
| `src/app/llm_caret/gui.spl` | 84 | GUI components and layout |
| `src/app/llm_caret/gui_metal.spl` | 205 | Metal/native GUI rendering backend |
| `src/app/llm_caret/gui_native_model.spl` | 69 | Native model provider for GUI |
| `src/app/llm_caret/harness_spec.spl` | 118 | Test harness infrastructure |
| `src/app/llm_caret/image_completion.spl` | 20 | Image-to-Markdown completion contract |
| `src/app/llm_caret/image_format.spl` | 181 | Bounded image-container inspection |
| `src/app/llm_caret/image_profile.spl` | 37 | Model image profile admission |
| `src/app/llm_caret/infra_mail.spl` | 504 | SMTP/IMAP mail infrastructure |
| `src/app/llm_caret/infra_mail_starttls.spl` | 157 | Mail STARTTLS protocol support |
| `src/app/llm_caret/infra_storage.spl` | 215 | Object storage (S3/MinIO) backend |
| `src/app/llm_caret/infra_wiki.spl` | 377 | Wiki/documentation backend |
| `src/app/llm_caret/interface_text.spl` | 13 | Interface definitions |
| `src/app/llm_caret/json_helpers.spl` | 277 | JSON construction and parsing helpers |
| `src/app/llm_caret/local_torch.spl` | 90 | Local model provider (Torch/TensorFlow) |
| `src/app/llm_caret/main.spl` | 1354 | Main entry point and CLI dispatch |
| `src/app/llm_caret/mod.spl` | 254 | Public API and state management |
| `src/app/llm_caret/multi_caret_manager.spl` | 153 | Multi-agent orchestration and management |
| `src/app/llm_caret/multimodal_provider.spl` | 159 | Provider serialization of admitted image data |
| `src/app/llm_caret/multimodal_types.spl` | 608 | Versioned multimodal and image-to-Markdown contracts |
| `src/app/llm_caret/openai_api.spl` | 336 | OpenAI-compatible API request/response |
| `src/app/llm_caret/openai_compat.spl` | 302 | Local/OpenAI-compatible endpoint provider |
| `src/app/llm_caret/opencode_cli.spl` | 187 | OpenCode adapter with Claude-like response |
| `src/app/llm_caret/pane_backend.spl` | 573 | Pane/terminal multiplexer backend |
| `src/app/llm_caret/provider.spl` | 384 | Provider registry and dispatching |
| `src/app/llm_caret/redact.spl` | 354 | Sensitive data redaction |
| `src/app/llm_caret/retry.spl` | 201 | Retry logic and backoff strategies |
| `src/app/llm_caret/server.spl` | 560 | HTTP/MCP-like compatibility server surface |
| `src/app/llm_caret/session.spl` | 245 | Session management and lifecycle |
| `src/app/llm_caret/tool_cli.spl` | 69 | Tool CLI interface |
| `src/app/llm_caret/tools.spl` | 594 | Tool definitions and management |
| `src/app/llm_caret/tui_input.spl` | 222 | Terminal UI input handling |
| `src/app/llm_caret/tui_io.spl` | 188 | Terminal UI I/O and output |
| `src/app/llm_caret/types.spl` | 225 | Request/response/event/config record types |
| `src/app/llm_caret/workspace_cli.spl` | 213 | Workspace CLI parsing and execution |

Mapped files: 52/52 = 100%, above the required 80%.
Mapped LOC: 14828/14828 = 100%, above the required 80%.

## Function Trace

| Simple file | Public or key functions/classes |
|---|---|
| `chat.spl` | `chat_clear`, `chat_set_system_prompt`, `chat_add_message`, `chat_truncate`, `chat_build_messages_json`, `chat_last_content`, `chat_last_role` |
| `claude_api.spl` | `ApiResponse`, `build_claude_api_body`, `build_claude_api_headers`, `build_single_message_json`, `parse_claude_api_response`, `claude_api_send` |
| `claude_cli.spl` | `CliResponse`, `CliStreamEvent`, `build_claude_args`, `build_claude_args_simple`, `parse_claude_json_response`, `parse_claude_stream_line`, `claude_cli_send`, `claude_cli_stream` |
| `config.spl` | `config_loaded`, `config_default_provider`, provider default getters, config parsing helpers |
| `json_helpers.spl` | `escape_json_text`, `jo1`-`jo6`, `ja`, `extract_json_string`, `extract_json_value`, `extract_json_int`, `extract_json_bool`, `extract_nested_string`, `build_message_json`, `build_messages_json` |
| `local_torch.spl` | `LocalResponse`, `build_torch_script`, `local_torch_send` |
| `mod.spl` | `llm_init_defaults`, `llm_init`, `llm_set_api_key`, `llm_set_base_url`, `llm_set_cli_path`, `llm_system`, `llm_clear`, `llm_history_*`, `llm_chat`, `llm_send` |
| `openai_api.spl` | `OpenAIResponse`, `build_openai_body`, `build_openai_headers`, `build_openai_messages_json`, `parse_openai_response`, `openai_send` |
| `openai_compat.spl` | `CompatResponse`, `build_compat_body`, `build_compat_headers`, `parse_compat_response`, `compat_send` |
| `opencode_cli.spl` | `OpencodeCliResponse`, `OpencodeProcessResult`, OpenCode argv/parse/process helpers |
| `provider.spl` | `LLMResponse`, `new_llm_error`, `list_providers`, `is_valid_provider`, `dispatch_send`, provider-specific dispatch helpers |
| `server.spl` | `build_health_response`, `build_models_response`, `build_chat_completion_response`, `build_anthropic_response`, `build_error_response`, `handle_route` |
| `types.spl` | `Message`, `ChatRequest`, `ChatResponse`, `StreamEvent`, `ProviderConfig`, constructors, response predicates |

## Simple Symbol Trace

This table is machine-checked by `scripts/check/check-llm-caret-claude-cli-trace.shs`.
Every current `fn`, `struct`, and `extern fn` symbol in `src/app/llm_caret/*.spl`
must appear as a backticked `kind:name` token.

| Simple source file | Traced symbols |
|---|---|
| `src/app/llm_caret/agent_discovery.spl` | `fn:_add_unique`, `fn:_all_between`, `fn:_line_value`, `fn:build_plugin_install_args`, `fn:discover_agent_capabilities`, `fn:parse_mcp_manifest`, `fn:parse_plugin_manifest`, `struct:AgentDiscoverySet` |
| `src/app/llm_caret/agent_files.spl` | `fn:detect_agent_file_changes`, `fn:snapshot_agent_files` |
| `src/app/llm_caret/agent_mailbox.spl` | `fn:agent_team_channel`, `fn:agent_team_inbox`, `fn:agent_team_transcript`, `fn:new_agent_team_mailbox`, `fn:post_agent_team_message`, `fn:post_btw_message`, `fn:post_side_message`, `struct:AgentTeamMailbox` |
| `src/app/llm_caret/agent_manager_view.spl` | `fn:_discover`, `fn:_fields`, `fn:_nonempty_lines`, `fn:_sh`, `fn:_subagents`, `fn:_usages`, `fn:main`, `fn:render_manager_view` |
| `src/app/llm_caret/agent_plan.spl` | `fn:_add_agent_change`, `fn:_agent_prompt`, `fn:_append_if_non_empty`, `fn:_append_lines`, `fn:_base_argv`, `fn:_fingerprint_for`, `fn:_has_change`, `fn:_provider_or_default`, `fn:build_agent_capability_launch_plan`, `fn:build_agent_change_review_plan`, `fn:build_agent_launch_plan`, `fn:build_agent_team_interaction_plan`, `fn:build_agent_team_plan`, `fn:build_btw_side_interaction_plan`, `fn:build_claude_advisor_plan`, `fn:build_codex_goal_plan`, `fn:build_low_agent_review_plan`, `fn:track_agent_file_changes`, `struct:AgentCapabilitySet`, `struct:AgentFileChangeSet`, `struct:AgentFileFingerprint`, `struct:AgentLaunchPlan`, `struct:AgentLaunchRequest`, `struct:AgentReviewRequest`, `struct:AgentTeamMessage` |
| `src/app/llm_caret/agent_runtime.spl` | `fn:agent_command_for_provider`, `fn:agent_command_for_provider_with_all`, `fn:agent_command_for_provider_with_gemini`, `fn:agent_process_status`, `fn:agent_team_status`, `fn:is_known_agent_provider`, `fn:launch_agent_plan`, `fn:launch_agent_plan_with_all`, `fn:launch_agent_plan_with_gemini`, `fn:launch_agent_team`, `fn:launch_agent_team_with_all`, `fn:launch_agent_team_with_gemini`, `fn:launch_messaging_agent_plan`, `fn:launch_messaging_agent_plan_with_all`, `fn:messaging_agent_environment`, `fn:stop_agent_process`, `fn:stop_agent_team`, `fn:summarize_agent_team`, `struct:AgentProcess`, `struct:AgentTeamProcess`, `struct:MessagingAgentLaunchContext` |
| `src/app/llm_caret/agent_tmux.spl` | `fn:_process_command`, `fn:_usage_for`, `fn:build_agent_tmux_embed`, `fn:render_agent_tmux_tui`, `struct:AgentProcessUsage`, `struct:AgentTmuxEmbed` |
| `src/app/llm_caret/agent_tui.spl` | `fn:_section`, `fn:render_agent_handoff_tui`, `fn:render_agent_mailbox_tui`, `fn:render_agent_messages_tui` |
| `src/app/llm_caret/agent_vcs.spl` | `fn:_add_unique`, `fn:discover_agent_vcs_changes`, `fn:parse_vcs_changed_files`, `struct:AgentVcsChangeResult` |
| `src/app/llm_caret/agent_workspace.spl` | `fn:_canonical`, `fn:_dir_of`, `fn:_err`, `fn:_fmt`, `fn:_hash`, `fn:_norm_path`, `fn:_ok`, `fn:_own_pane_id`, `fn:_ps_quote`, `fn:_run`, `fn:_simple_root`, `fn:_smux`, `fn:_smux_listener_is`, `fn:_smux_owner`, `fn:_smux_owner_forget`, `fn:_smux_owner_path`, `fn:_smux_owner_up`, `fn:_smux_pane_spawn`, `fn:_smux_private_dir`, `fn:_smux_req`, `fn:_smux_req_ok`, `fn:_smux_retire`, `fn:_smux_state_dir`, `fn:_tmux`, `fn:_valid_name`, `fn:_words`, `fn:_ws_pane`, `fn:_ws_panes`, `fn:agent_attach`, `fn:agent_detach`, `fn:agent_workspace`, `fn:capture_pane`, `fn:depth_exceeded`, `fn:launch_caret_suite`, `fn:list_panes`, `fn:list_panes_except`, `fn:pane_pid_lines`, `fn:pane_split`, `fn:send_to_each_pane`, `fn:send_to_pane`, `fn:session_alive`, `fn:session_ensure`, `fn:session_kill`, `fn:tmux_available`, `fn:wait_for_pane_text`, `fn:window_exists`, `fn:window_open`, `fn:with_depth`, `fn:workspace_available`, `fn:workspace_backend`, `fn:workspace_depth`, `fn:workspace_server_address`, `fn:workspace_server_alive`, `fn:workspace_server_token_path`, `fn:worktree_add`, `fn:worktree_list`, `fn:worktree_path`, `fn:worktree_remove`, `struct:AgentWorkspace`, `struct:SmuxOwner`, `struct:WorkspaceResult`, `struct:WsPane` |
| `src/app/llm_caret/chat.spl` | `fn:_LB`, `fn:_Q`, `fn:_RB`, `fn:_emit_tool`, `fn:_escape_json`, `fn:_tool_result_message`, `fn:chat_add_assistant`, `fn:chat_add_message`, `fn:chat_add_user`, `fn:chat_build_messages_json`, `fn:chat_clear`, `fn:chat_get_content`, `fn:chat_get_role`, `fn:chat_get_system_prompt`, `fn:chat_history_len`, `fn:chat_last_content`, `fn:chat_last_role`, `fn:chat_set_max_history`, `fn:chat_set_system_prompt`, `fn:chat_truncate`, `fn:run_agent_loop`, `fn:run_agent_loop_rendered`, `fn:tool_call_status`, `fn:tool_call_summary`, `struct:AgentResult` |
| `src/app/llm_caret/chat_tui.spl` | `fn:_apply_slash`, `fn:_code_span_style`, `fn:_dim_style`, `fn:_draw_frame`, `fn:_draw_if_visible`, `fn:_hint_line`, `fn:_inner_height`, `fn:_line_plain_text`, `fn:_read_line`, `fn:_render_history`, `fn:_replace_status_field`, `fn:_slash_msg`, `fn:_slash_status`, `fn:_split_first_space`, `fn:_status_line`, `fn:_ui_set_input`, `fn:_visible_content`, `fn:apply_slash_status`, `fn:bullet_indent`, `fn:caret_chat`, `fn:dispatch_slash`, `fn:format_tool_line`, `fn:format_turn_line`, `fn:inline_code_segments`, `fn:is_fence_line`, `fn:is_scrolled`, `fn:is_slash_command`, `fn:make_chat_tui`, `fn:make_chat_tui_with_status`, `fn:markdown_turn_lines`, `fn:parse_slash_command`, `fn:render_tool_call`, `fn:render_turn`, `fn:run_chat_plain`, `fn:run_chat_tui`, `fn:run_chat_tui_submission`, `fn:scroll_page_down`, `fn:scroll_page_up`, `fn:slash_help_text`, `fn:tui_role_label`, `fn:tui_role_style`, `fn:tui_tool_renderer`, `fn:tui_tool_style`, `fn:tui_transcript_len`, `fn:tui_transcript_line_text`, `fn:tui_transcript_reset`, `fn:visible_window`, `struct:ChatSubmissionResult`, `struct:ChatTui`, `struct:ProviderSwitchResult`, `struct:SessionHooks`, `struct:SessionResumeResult`, `struct:SlashResult` |
| `src/app/llm_caret/claude_api.spl` | `fn:_LB`, `fn:_Q`, `fn:_RB`, `fn:_escape_json`, `fn:_extract_json_int`, `fn:_extract_json_string`, `fn:_extract_json_value`, `fn:_has_json_key`, `fn:_has_json_string_value`, `fn:build_claude_api_body`, `fn:build_claude_api_headers`, `fn:build_claude_api_request`, `fn:build_single_message_json`, `fn:claude_api_endpoint_url`, `fn:claude_api_retry_transport`, `fn:claude_api_send`, `fn:complete_claude_api_exchange`, `fn:parse_claude_api_response`, `struct:ApiResponse`, `struct:ClaudeApiRequest` |
| `src/app/llm_caret/claude_cli.spl` | `fn:_invalid_cli_response`, `fn:_invalid_stream_event`, `fn:_json_bool`, `fn:_json_has_usage_key`, `fn:_json_i64`, `fn:_json_message_content`, `fn:_json_message_field`, `fn:_json_message_usage_i64`, `fn:_json_optional_kind`, `fn:_json_raw`, `fn:_json_text`, `fn:_json_text_fields_valid`, `fn:_json_usage_i64`, `fn:_json_usage_kinds_valid`, `fn:_supported_stream_type`, `fn:build_claude_args`, `fn:build_claude_stream_args`, `fn:claude_cli_send`, `fn:claude_cli_stream`, `fn:parse_claude_json_response`, `fn:parse_claude_stream_line`, `struct:CliResponse`, `struct:CliStreamEvent` |
| `src/app/llm_caret/codex_cli.spl` | `fn:_error_response`, `fn:build_codex_args`, `fn:build_codex_invocation`, `fn:codex_cli_kill`, `fn:codex_cli_running_status`, `fn:codex_cli_send`, `fn:codex_cli_spawn`, `fn:complete_codex_process`, `fn:parse_codex_response`, `struct:CodexCliResponse`, `struct:CodexInvocation`, `struct:CodexProcessResult` |
| `src/app/llm_caret/config.spl` | `fn:_apply_config`, `fn:_unwrap_idx_cfg`, `fn:complete_config_load`, `fn:config_claude_api_base_url`, `fn:config_claude_api_key`, `fn:config_claude_api_model`, `fn:config_claude_cli_model`, `fn:config_claude_cli_path`, `fn:config_codex_cli_model`, `fn:config_codex_cli_path`, `fn:config_compat_api_key`, `fn:config_compat_base_url`, `fn:config_compat_model`, `fn:config_deepseek_api_key`, `fn:config_deepseek_base_url`, `fn:config_deepseek_model`, `fn:config_default_provider`, `fn:config_glm_api_key`, `fn:config_glm_base_url`, `fn:config_glm_model`, `fn:config_history_file`, `fn:config_image_read_api_key`, `fn:config_image_read_api_key_env`, `fn:config_image_read_base_url`, `fn:config_image_read_detail`, `fn:config_image_read_egress`, `fn:config_image_read_location`, `fn:config_image_read_max_concurrency`, `fn:config_image_read_max_images`, `fn:config_image_read_max_output_tokens`, `fn:config_image_read_max_pixels`, `fn:config_image_read_max_request_bytes`, `fn:config_image_read_max_working_set_bytes`, `fn:config_image_read_model`, `fn:config_image_read_model_revision`, `fn:config_image_read_profile_id`, `fn:config_image_read_provider`, `fn:config_image_read_structured_output`, `fn:config_image_read_timeout_ms`, `fn:config_image_read_trust_scope`, `fn:config_image_read_vision`, `fn:config_kimi_api_key`, `fn:config_kimi_base_url`, `fn:config_kimi_model`, `fn:config_loaded`, `fn:config_local_model_path`, `fn:config_local_python_path`, `fn:config_mail_imap_host`, `fn:config_mail_imap_port`, `fn:config_mail_secret`, `fn:config_mail_secret_env`, `fn:config_mail_smtp_host`, `fn:config_mail_smtp_port`, `fn:config_mail_user`, `fn:config_max_history`, `fn:config_openai_api_key`, `fn:config_openai_base_url`, `fn:config_openai_model`, `fn:config_opencode_cli_model`, `fn:config_opencode_cli_path`, `fn:config_slang_api_key`, `fn:config_slang_base_url`, `fn:config_slang_model`, `fn:config_slang_model_root`, `fn:config_storage_access_key`, `fn:config_storage_access_key_env`, `fn:config_storage_backend`, `fn:config_storage_bucket`, `fn:config_storage_endpoint`, `fn:config_storage_secret_key`, `fn:config_storage_secret_key_env`, `fn:config_storage_tls`, `fn:config_wiki_backend`, `fn:config_wiki_base_url`, `fn:config_wiki_root`, `fn:config_wiki_space`, `fn:config_wiki_token`, `fn:config_wiki_token_env`, `fn:config_wiki_user`, `fn:load_caret_config`, `fn:load_config`, `fn:load_defaults`, `fn:parse_config_text`, `fn:reset_config` |
| `src/app/llm_caret/cs_dashboard.spl` | `fn:_agent_list_text`, `fn:_attach`, `fn:_dash`, `fn:_dashboard_lines`, `fn:_detach`, `fn:_detail_lines`, `fn:_find_pane`, `fn:_header`, `fn:_is_section`, `fn:_left_width`, `fn:_logged`, `fn:_measured`, `fn:_paint`, `fn:_resolve`, `fn:_rest`, `fn:_screen_lines`, `fn:_unmeasured`, `fn:_usage_text`, `fn:_which`, `fn:_with_screen`, `fn:_with_status`, `fn:_words`, `fn:cs_agent_area`, `fn:cs_apply_action`, `fn:cs_dashboard_new`, `fn:cs_fit`, `fn:cs_fit_sgr`, `fn:cs_frame_rows`, `fn:cs_handle_command`, `fn:cs_help_text`, `fn:cs_launch_argv`, `fn:cs_poll_screens`, `fn:cs_refresh`, `fn:cs_render`, `fn:cs_resize_agents`, `fn:cs_resolve_exe`, `fn:cs_stderr_path`, `fn:windows_executable_names`, `struct:CsAgent`, `struct:CsDashboard` |
| `src/app/llm_caret/cs_main.spl` | `fn:_char_count`, `fn:_clock`, `fn:_cs_step`, `fn:_drop_last_char`, `fn:_live_end`, `fn:_live_size`, `fn:_logged_outcome`, `fn:_plain_begin`, `fn:_plain_dim`, `fn:_plain_draw`, `fn:_plain_emit`, `fn:_plain_end`, `fn:_plain_is_tty`, `fn:_plain_no_input`, `fn:_plain_noop`, `fn:_plain_read_byte`, `fn:_plain_read_line`, `fn:_plain_size`, `fn:_same_rows`, `fn:_two`, `fn:_with_input`, `fn:cs_effective_size`, `fn:cs_live_input_supported`, `fn:cs_live_paint`, `fn:cs_plain_io`, `fn:cs_run`, `fn:cs_run_live`, `fn:cs_session_from_args`, `fn:main` |
| `src/app/llm_caret/gui.spl` | `fn:_caret_gui_html_escape`, `fn:caret_gui_html`, `fn:caret_gui_json_content`, `fn:caret_gui_json_error`, `fn:caret_gui_native_html`, `fn:caret_gui_prompt` |
| `src/app/llm_caret/gui_metal.spl` | `fn:_caret_metal_command_count`, `fn:_caret_metal_dispatch`, `fn:_caret_metal_emit`, `fn:_caret_metal_pack`, `fn:_caret_metal_point_in_send`, `fn:_caret_metal_present`, `fn:_caret_metal_prompt_arg`, `fn:_caret_metal_submit`, `fn:caret_metal_render_frame`, `fn:main`, `fn:run_caret_metal_gui`, `struct:CaretMetalFrame` |
| `src/app/llm_caret/gui_native_model.spl` | `fn:_caret_native_key_char`, `fn:_caret_native_with_prompt`, `fn:caret_native_apply_response`, `fn:caret_native_key`, `fn:caret_native_state`, `fn:caret_native_state_with_prompt`, `struct:CaretNativeState`, `struct:CaretNativeStep` |
| `src/app/llm_caret/harness_spec.spl` | `fn:_bad`, `fn:_count_char`, `fn:_is_known_caret_provider`, `fn:_is_known_harness`, `fn:harness_agent_provider`, `fn:harness_is_cli`, `fn:harness_spec_display`, `fn:known_caret_providers`, `fn:known_harnesses`, `fn:parse_harness_spec`, `struct:HarnessSpec` |
| `src/app/llm_caret/image_completion.spl` | `fn:complete_configured_image_v1`, `fn:validate_configured_image_secret_v1` |
| `src/app/llm_caret/image_format.spl` | `fn:_invalid_image_format_v1`, `fn:_png_crc_v1`, `fn:_u16_be_v1`, `fn:_u24_le_v1`, `fn:_u32_be_v1`, `fn:_u32_le_v1`, `fn:inspect_image_bytes_v1`, `fn:inspect_jpeg_bytes_v1`, `fn:inspect_png_bytes_v1`, `fn:inspect_webp_bytes_v1`, `struct:ImageFormatInfoV1` |
| `src/app/llm_caret/image_profile.spl` | `fn:configured_image_profile_v1` |
| `src/app/llm_caret/infra_mail.spl` | `fn:_LB`, `fn:_RB`, `fn:_close`, `fn:_connect`, `fn:_format_list`, `fn:_format_message`, `fn:_imap_command`, `fn:_imap_login`, `fn:_imap_ok`, `fn:_imap_select`, `fn:_imap_session_run`, `fn:_imap_tag`, `fn:_last`, `fn:_lines_of`, `fn:_link_error`, `fn:_prop`, `fn:_read_chunk`, `fn:_read_reply`, `fn:_schema`, `fn:_send`, `fn:_smtp_code`, `fn:_smtp_reply_complete`, `fn:_smtp_step`, `fn:_strip_crlf`, `fn:_timeout_error`, `fn:_uses_implicit_tls`, `fn:mail_build_message`, `fn:mail_configured`, `fn:mail_list`, `fn:mail_read`, `fn:mail_read_timeout_ms`, `fn:mail_secret_error`, `fn:mail_send`, `fn:mail_set_read_timeout_ms`, `fn:mail_tool_schemas`, `struct:MailLink`, `struct:MailReply` |
| `src/app/llm_caret/infra_mail_starttls.spl` | `fn:_fail`, `fn:_imap_tagged_ok`, `fn:_kind_name`, `fn:_smtp_code`, `fn:_state`, `fn:imap_capability_advertises_starttls`, `fn:smtp_ehlo_advertises_starttls`, `fn:starttls_begin`, `fn:starttls_feed`, `fn:starttls_run_script`, `fn:starttls_runtime_gap_error`, `struct:StarttlsState` |
| `src/app/llm_caret/infra_storage.spl` | `fn:_LB`, `fn:_RB`, `fn:_minio_cfg`, `fn:_minio_url`, `fn:_prop`, `fn:_resolve_bucket`, `fn:_schema`, `fn:_validate_key`, `fn:storage_config_error`, `fn:storage_configured`, `fn:storage_get`, `fn:storage_get_max_bytes`, `fn:storage_ls`, `fn:storage_put`, `fn:storage_put_max_bytes`, `fn:storage_tool_schemas` |
| `src/app/llm_caret/infra_wiki.spl` | `fn:_LB`, `fn:_RB`, `fn:_confluence_cfg`, `fn:_confluence_page_url`, `fn:_confluence_read`, `fn:_confluence_search`, `fn:_confluence_write`, `fn:_dirname`, `fn:_file_url`, `fn:_has_dotdot`, `fn:_is_abs_path`, `fn:_is_env_name`, `fn:_local_guard`, `fn:_local_read`, `fn:_local_root`, `fn:_local_search`, `fn:_local_title`, `fn:_local_write`, `fn:_norm_dir`, `fn:_prop`, `fn:_schema`, `fn:_slug`, `fn:wiki_config_error`, `fn:wiki_configured`, `fn:wiki_read`, `fn:wiki_search`, `fn:wiki_tool_schemas`, `fn:wiki_write` |
| `src/app/llm_caret/interface_text.spl` | `fn:caret_role_label`, `fn:caret_turn_line` |
| `src/app/llm_caret/json_helpers.spl` | `fn:LB`, `fn:Q`, `fn:RB`, `fn:_digit_val`, `fn:build_message_json`, `fn:build_messages_json`, `fn:escape_json_text`, `fn:extract_json_bool`, `fn:extract_json_int`, `fn:extract_json_string`, `fn:extract_json_value`, `fn:extract_nested_string`, `fn:ja`, `fn:jo1`, `fn:jo2`, `fn:jo3`, `fn:jo4`, `fn:jo5`, `fn:jo6`, `fn:jp`, `fn:js`, `fn:json_find`, `fn:json_parse_int` |
| `src/app/llm_caret/local_torch.spl` | `fn:build_torch_script`, `fn:complete_local_torch_exchange`, `fn:local_torch_send`, `fn:python_single_quoted`, `struct:LocalResponse` |
| `src/app/llm_caret/main.spl` | `fn:_build_policy`, `fn:_build_session_hooks`, `fn:_caret_electron_binary`, `fn:_default_model`, `fn:_effective_api_key`, `fn:_effective_base_url`, `fn:_effective_cli_path`, `fn:_effective_model`, `fn:_effective_port`, `fn:_effective_provider`, `fn:_gui_dispatch`, `fn:_gui_handle_connection`, `fn:_gui_http_handle`, `fn:_gui_read_request`, `fn:_gui_ready`, `fn:_gui_status_text`, `fn:_gui_write_response`, `fn:_hidden_commands_enabled`, `fn:_http_handle`, `fn:_last_user_content`, `fn:_messages_json`, `fn:_on_persist`, `fn:_proxy_dispatch`, `fn:_proxy_dispatch_multimodal`, `fn:_render_agent_transcript`, `fn:_resolve_workspace`, `fn:_slash_on_hidden_command`, `fn:_slash_on_model`, `fn:_slash_on_new`, `fn:_slash_on_provider`, `fn:_slash_on_resume`, `fn:_slash_on_sessions`, `fn:_to_http_status`, `fn:_workbench_requests`, `fn:apply_resumed_session`, `fn:bearer_ok`, `fn:build_model_response`, `fn:guard_request`, `fn:local_agent_tool_prompt`, `fn:main`, `fn:main_configure`, `fn:main_responder`, `fn:main_session_id`, `fn:parse_main_args`, `fn:print_help`, `fn:proxy_handle`, `fn:proxy_handle_multimodal`, `fn:proxy_handle_stream`, `fn:proxy_handle_stream_multimodal`, `fn:rate_limit_check`, `fn:rate_limit_reset`, `fn:required_token`, `fn:resolve_resume_backend`, `fn:run_gui`, `fn:run_main_args`, `fn:run_server`, `fn:run_workbench`, `fn:status_for_path`, `fn:validate_proxy_image_model_selection_v1`, `struct:MainArgs`, `struct:ResumeBackend` |
| `src/app/llm_caret/mod.spl` | `fn:_LB`, `fn:_Q`, `fn:_RB`, `fn:_build_direct_messages_json`, `fn:_build_messages_json`, `fn:_dispatch_current`, `fn:_effective_api_key`, `fn:_escape_json`, `fn:_record_provider_session`, `fn:llm_chat`, `fn:llm_clear`, `fn:llm_history_content`, `fn:llm_history_len`, `fn:llm_history_role`, `fn:llm_init`, `fn:llm_init_defaults`, `fn:llm_model`, `fn:llm_provider`, `fn:llm_send`, `fn:llm_set_api_key`, `fn:llm_set_base_url`, `fn:llm_set_cli_path`, `fn:llm_system` |
| `src/app/llm_caret/multi_caret_manager.spl` | `fn:_empty_team`, `fn:_leaked_processes`, `fn:_manager`, `fn:launch_multi_caret_manager`, `fn:list_multi_caret_agents`, `fn:multi_caret_manager_of`, `fn:poll_multi_caret_manager`, `fn:reconcile_multi_caret_manager`, `fn:render_multi_caret_agents`, `fn:settle_multi_caret_manager`, `fn:stop_multi_caret_manager`, `struct:ManagedAgent`, `struct:MultiCaretManager` |
| `src/app/llm_caret/multimodal_provider.spl` | `fn:_anthropic_content_part_json_v1`, `fn:_anthropic_system_prompt_v1`, `fn:_base_endpoint_v1`, `fn:_complete_provider_v1`, `fn:_openai_content_part_json_v1`, `fn:_timeout_exchange_v1`, `fn:complete_multimodal_v1`, `fn:complete_multimodal_wire_v1`, `fn:multimodal_messages_json_v1` |
| `src/app/llm_caret/multimodal_types.spl` | `fn:_image_category_valid_v1`, `fn:_is_loopback_http_endpoint_v1`, `fn:_source_bounds_inside_v1`, `fn:chart_type_valid_v1`, `fn:empty_source_bounds_v1`, `fn:image_data_part_v1`, `fn:image_part_v1`, `fn:image_value_status_name_v1`, `fn:model_completion_error_v1`, `fn:text_part_v1`, `fn:validate_chart_point_v1`, `fn:validate_content_part_v1`, `fn:validate_extraction_document_v1`, `fn:validate_model_profile_v1`, `fn:validate_multimodal_request_v1`, `struct:ChartAnnotationV1`, `struct:ChartLegendEntryV1`, `struct:ChartPanelV1`, `struct:ChartPointV1`, `struct:ChartSeriesV1`, `struct:ChartTickV1`, `struct:ContentPartV1`, `struct:ExtractionArtifactsV1`, `struct:ExtractionDocumentV1`, `struct:ExtractionReceiptV1`, `struct:ExtractionRegionV1`, `struct:ModelCompletionV1`, `struct:ModelProfileV1`, `struct:MultimodalErrorV1`, `struct:MultimodalMessageV1`, `struct:MultimodalRequestV1`, `struct:SourceBoundsV1`, `struct:TableCellV1`, `struct:TableV1`, `struct:TextSpanV1`, `struct:VisionCapabilitiesV1` |
| `src/app/llm_caret/openai_api.spl` | `fn:_LB`, `fn:_Q`, `fn:_RB`, `fn:_escape_json`, `fn:_extract_json_int`, `fn:_extract_json_string`, `fn:_extract_json_value`, `fn:_has_json_key`, `fn:_has_json_string_value`, `fn:build_openai_body`, `fn:build_openai_headers`, `fn:build_openai_messages_json`, `fn:build_openai_request`, `fn:complete_openai_exchange`, `fn:openai_endpoint_url`, `fn:openai_retry_transport`, `fn:openai_send`, `fn:parse_openai_response`, `struct:OpenAIApiRequest`, `struct:OpenAIResponse` |
| `src/app/llm_caret/openai_compat.spl` | `fn:_LB`, `fn:_Q`, `fn:_RB`, `fn:_ends_with_version`, `fn:_escape_json`, `fn:_extract_json_int`, `fn:_extract_json_string`, `fn:_extract_json_value`, `fn:_has_json_key`, `fn:_has_json_string_value`, `fn:build_compat_body`, `fn:build_compat_headers`, `fn:build_compat_request`, `fn:compat_endpoint_url`, `fn:compat_send`, `fn:compat_transport`, `fn:complete_compat_exchange`, `fn:parse_compat_response`, `struct:CompatRequest`, `struct:CompatResponse` |
| `src/app/llm_caret/opencode_cli.spl` | `fn:_error_response`, `fn:_first_non_empty`, `fn:_json_string_field_valid`, `fn:_json_text`, `fn:build_opencode_args`, `fn:build_opencode_invocation`, `fn:complete_opencode_process`, `fn:opencode_cli_kill`, `fn:opencode_cli_running_status`, `fn:opencode_cli_send`, `fn:opencode_cli_spawn`, `fn:parse_opencode_response`, `struct:OpencodeCliResponse`, `struct:OpencodeInvocation`, `struct:OpencodeProcessResult` |
| `src/app/llm_caret/pane_backend.spl` | `fn:_fields`, `fn:_is_digits`, `fn:_is_windows`, `fn:_no_pane`, `fn:_pane_capture`, `fn:_posix_launcher_create`, `fn:_posix_launcher_remove`, `fn:_smux_free_pane`, `fn:_smux_list`, `fn:_smux_pid`, `fn:_smux_scope`, `fn:_smux_spawn`, `fn:_smux_title`, `fn:_tmux_available`, `fn:_tmux_ok`, `fn:_use_tmux`, `fn:pane_backend_name`, `fn:pane_capture`, `fn:pane_capture_argv`, `fn:pane_capture_styled`, `fn:pane_key_bytes`, `fn:pane_key_tmux_name`, `fn:pane_kill`, `fn:pane_kill_argv`, `fn:pane_list`, `fn:pane_list_argv`, `fn:pane_parse_line`, `fn:pane_parse_lines`, `fn:pane_resize`, `fn:pane_select`, `fn:pane_select_argv`, `fn:pane_send`, `fn:pane_send_enter_argv`, `fn:pane_send_key`, `fn:pane_send_literal_argv`, `fn:pane_spawn`, `fn:pane_spawn_at`, `fn:pane_zoom`, `fn:pane_zoom_argv`, `fn:posix_command_line`, `fn:posix_exec_line`, `fn:posix_quote_arg`, `fn:windows_command_line`, `fn:windows_quote_arg`, `fn:windows_spawn_command_line`, `struct:Pane`, `struct:SmuxPaneInfo`, `struct:SmuxScope` |
| `src/app/llm_caret/provider.spl` | `fn:_dispatch_claude_api`, `fn:_dispatch_claude_cli`, `fn:_dispatch_codex_cli`, `fn:_dispatch_compat`, `fn:_dispatch_local_torch`, `fn:_dispatch_openai`, `fn:_dispatch_opencode_cli`, `fn:_dispatch_slang_local`, `fn:dispatch_send`, `fn:dispatch_send_advanced`, `fn:is_valid_provider`, `fn:list_providers`, `fn:new_llm_error`, `struct:LLMResponse` |
| `src/app/llm_caret/redact.spl` | `fn:_find`, `fn:_is_alnum`, `fn:_is_alpha`, `fn:_is_digit`, `fn:_is_ident_char`, `fn:_is_key_char`, `fn:_is_lower`, `fn:_is_space`, `fn:_is_upper`, `fn:_last4`, `fn:_match_akia`, `fn:_match_bearer`, `fn:_match_env_assignment`, `fn:_match_generic_sk`, `fn:_match_pem`, `fn:_match_prefixed_key`, `fn:_redact_ascii_run`, `fn:_replace_all`, `fn:_run_ident_chars`, `fn:_run_key_chars`, `fn:_run_non_space`, `fn:_run_upper_digit`, `fn:_sensitive_env_var_names`, `fn:redact`, `fn:redact_env_values`, `fn:wrap_untrusted` |
| `src/app/llm_caret/retry.spl` | `fn:_jitter_ms`, `fn:backoff_delay_ms`, `fn:default_retry_policy`, `fn:effective_delay_ms`, `fn:is_retryable_status`, `fn:retry_policy_from_env`, `fn:retry_remaining_ms`, `fn:should_retry`, `fn:with_retry`, `fn:with_retry_timeout`, `struct:RetryOutcome`, `struct:RetryPolicy` |
| `src/app/llm_caret/server.spl` | `extern:rt_http_request`, `fn:_LB`, `fn:_Q`, `fn:_RB`, `fn:_build_chat_completion_chunk`, `fn:_escape_json`, `fn:_extract_json_string`, `fn:_strict_base64_payload_v1`, `fn:_unwrap_idx`, `fn:anthropic_messages_to_openai_v1`, `fn:anthropic_system_text_v1`, `fn:build_anthropic_response`, `fn:build_anthropic_stream_response`, `fn:build_chat_completion_response`, `fn:build_chat_completion_stream_response`, `fn:build_error_response`, `fn:build_health_response`, `fn:build_models_response`, `fn:build_models_response_with_image_v1`, `fn:handle_route`, `fn:multimodal_messages_have_image_v1`, `fn:openai_messages_to_anthropic_v1`, `fn:parse_chat_request_content`, `fn:parse_chat_request_messages_json`, `fn:parse_chat_request_model`, `fn:parse_chat_request_system_text`, `fn:validate_proxy_image_messages_v1`, `fn:validate_proxy_image_messages_with_limits_v1` |
| `src/app/llm_caret/session.spl` | `fn:_extract_json_int`, `fn:_extract_json_string`, `fn:_extract_json_string_unescaped`, `fn:_extract_object_at`, `fn:_json_unescape`, `fn:_messages_json`, `fn:_sessions_dir`, `fn:gen_session_id`, `fn:list_session_ids`, `fn:load_session`, `fn:new_session`, `fn:parse_messages_array`, `fn:save_session`, `fn:session_from_json`, `fn:session_path`, `fn:session_to_json`, `struct:Session` |
| `src/app/llm_caret/tool_cli.spl` | `fn:_usage`, `fn:main`, `fn:run_tool_cli` |
| `src/app/llm_caret/tools.spl` | `fn:_LB`, `fn:_Q`, `fn:_RB`, `fn:_extract_input_object`, `fn:_extract_object_at`, `fn:_glob_match`, `fn:_has_dotdot`, `fn:_idx`, `fn:_infra_result`, `fn:_json_get_int`, `fn:_json_get_str`, `fn:_json_unescape`, `fn:_json_wire`, `fn:_list_contains`, `fn:_normalize_root`, `fn:_pad_left`, `fn:_rfind_brace`, `fn:_sq`, `fn:_truncate`, `fn:allow_all_policy`, `fn:default_policy`, `fn:exec_bash`, `fn:exec_glob`, `fn:exec_list_dir`, `fn:exec_read_file`, `fn:exec_write_file`, `fn:guard_path`, `fn:is_known_tool`, `fn:is_mutating_tool`, `fn:is_read_only_tool`, `fn:new_model_text`, `fn:new_model_tools`, `fn:new_tool_call`, `fn:new_tool_error`, `fn:new_tool_result`, `fn:parse_tool_use_blocks`, `fn:parse_tool_use_tags`, `fn:permission_decision`, `fn:policy_with_allow`, `fn:run_tool`, `fn:tool_schemas`, `struct:ModelResponse`, `struct:PermissionPolicy`, `struct:ToolCall`, `struct:ToolResult` |
| `src/app/llm_caret/tui_input.spl` | `fn:_ansi_final_key`, `fn:_raw_key_decode`, `fn:_raw_line_step`, `fn:_utf8_append`, `fn:_utf8_emit_or_reject`, `fn:_utf8_partial`, `fn:_utf8_state`, `fn:apply_raw_key_decode`, `fn:caret_is_tty`, `fn:caret_term_supports_tui`, `fn:decode_raw_key_byte`, `fn:make_raw_line_state`, `fn:select_renderer_mode`, `fn:step_raw_line_byte`, `struct:RawKeyDecodeResult`, `struct:RawLineState`, `struct:RawLineStep` |
| `src/app/llm_caret/tui_io.spl` | `fn:_production_begin_tui`, `fn:_production_clear_screen`, `fn:_production_draw_at`, `fn:_production_emit`, `fn:_production_end_tui`, `fn:_production_enter_raw`, `fn:_production_fd_input`, `fn:_production_fill_input`, `fn:_production_flush`, `fn:_production_input_pending`, `fn:_production_is_tty`, `fn:_production_read_byte`, `fn:_production_read_line`, `fn:_production_terminal_size`, `fn:caret_terminal_error`, `fn:caret_terminal_ok`, `fn:production_caret_io`, `struct:CaretIo`, `struct:CaretLoopResult`, `struct:CaretTerminalResult` |
| `src/app/llm_caret/types.spl` | `fn:is_assistant_message`, `fn:is_system_message`, `fn:is_user_message`, `fn:new_assistant_message`, `fn:new_chat_request`, `fn:new_chat_request_with_prompt`, `fn:new_chat_response`, `fn:new_error_response`, `fn:new_message`, `fn:new_message_stop`, `fn:new_provider_config`, `fn:new_stream_event`, `fn:new_success_response`, `fn:new_system_message`, `fn:new_text_delta`, `fn:new_user_message`, `fn:response_has_content`, `fn:response_ok`, `struct:ChatRequest`, `struct:ChatResponse`, `struct:Message`, `struct:ProviderConfig`, `struct:StreamEvent` |
| `src/app/llm_caret/workspace_cli.spl` | `fn:_join`, `fn:_need`, `fn:_report`, `fn:_status`, `fn:parse_workspace_args`, `fn:run_workspace_cli`, `fn:workspace_usage`, `struct:WorkspaceCliArgs` |

## Claude Source Trace

| Claude source file | Classes/types/functions used for migration comparison |
|---|---|
| `src/entrypoints/cli.tsx` | CLI fast paths, prompt-mode flags, non-interactive entry behavior |
| `src/QueryEngine.ts` | prompt send/response loop, session id handling, usage accumulation |
| `src/Tool.ts` | tool result/error concepts and tool dispatch shape |
| `src/entrypoints/sdk/coreSchemas.ts` | request/response schema fields for model, max tokens, tools, sessions, MCP config |
| `src/bootstrap/state.ts` | session id, model usage, token/cost counters, cwd/project state, mode flags |
| `src/assistant/sessionHistory.ts` | session message history concept |
| `src/entrypoints/mcp.ts` | server entry shape for tool-facing compatibility |

## Claude Key Symbol Trace

This is a selected source-side trace for the Claude files used as migration
evidence. It is intentionally limited to the key CLI/provider/session symbols
that map into `src/app/llm_caret`; it is not a full port of Claude Code.

| Claude source file | Key traced symbols |
|---|---|
| `tmp/claude/claude-code-main/src/entrypoints/cli.tsx` | `function:main` |
| `tmp/claude/claude-code-main/src/QueryEngine.ts` | `type:QueryEngineConfig`, `class:QueryEngine` |
| `tmp/claude/claude-code-main/src/Tool.ts` | `type:Tool`, `function:findToolByName`, `function:buildTool` |
| `tmp/claude/claude-code-main/src/bootstrap/state.ts` | `type:State`, session/model/token state accessors |

## Verification

Run:

```bash
sh scripts/check/check-llm-caret-claude-cli-trace.shs
bin/simple test test/03_system/tools/llm/llm_caret_claude_cli_traceability_spec.spl --mode=interpreter
```
