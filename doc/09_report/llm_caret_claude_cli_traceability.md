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

| Simple source file | LOC | Claude source match | Role |
|---|---:|---|---|
| `src/app/llm_caret/chat.spl` | 227 | `src/assistant/sessionHistory.ts`, `src/bootstrap/state.ts` | conversation history and message JSON |
| `src/app/llm_caret/claude_api.spl` | 241 | `src/QueryEngine.ts`, `src/entrypoints/sdk/coreSchemas.ts` | Anthropic Messages request/response |
| `src/app/llm_caret/claude_cli.spl` | 414 | `src/entrypoints/cli.tsx`, `src/QueryEngine.ts` | non-interactive Claude CLI argv and typed JSON/stream parsing |
| `src/app/llm_caret/config.spl` | 228 | `src/bootstrap/state.ts`, `src/constants/product.ts` | defaults and provider config |
| `src/app/llm_caret/json_helpers.spl` | 250 | Simple-only shared helper | local JSON helper caret utility |
| `src/app/llm_caret/local_torch.spl` | 98 | Simple-only provider extension | local model provider outside Claude parity |
| `src/app/llm_caret/mod.spl` | 400 | `src/QueryEngine.ts`, `src/bootstrap/state.ts` | public API, state, provider dispatch |
| `src/app/llm_caret/openai_api.spl` | 260 | `src/entrypoints/sdk/coreSchemas.ts` | OpenAI-compatible provider extension |
| `src/app/llm_caret/openai_compat.spl` | 203 | `src/entrypoints/sdk/coreSchemas.ts` | local/OpenAI-compatible endpoint provider |
| `src/app/llm_caret/opencode_cli.spl` | 149 | Simple-only Claude-like CLI provider | OpenCode adapter with Claude-like response shape |
| `src/app/llm_caret/provider.spl` | 398 | `src/Tool.ts`, `src/constants/tools.ts`, `src/entrypoints/sdk/coreSchemas.ts` | provider registry and normalized response |
| `src/app/llm_caret/server.spl` | 199 | `src/entrypoints/mcp.ts`, `src/entrypoints/sdk/coreSchemas.ts` | compatibility HTTP/MCP-like response surface |
| `src/app/llm_caret/types.spl` | 225 | `src/entrypoints/sdk/coreSchemas.ts`, `src/types/logs.ts` | request/response/event/config records |

Mapped files: 13/23 = 56%, below the required 80%.
Mapped LOC: 3292/6609 = 50%, below the required 80%.

## Function Trace

| Simple file | Public or key functions/classes |
|---|---|
| `chat.spl` | `chat_clear`, `chat_set_system_prompt`, `chat_add_message`, `chat_truncate`, `chat_build_messages_json`, `chat_last_content`, `chat_last_role` |
| `claude_api.spl` | `ApiResponse`, `build_claude_api_body`, `build_claude_api_headers`, `build_single_message_json`, `parse_claude_api_response`, `claude_api_send` |
| `claude_cli.spl` | `CliResponse`, `CliStreamEvent`, typed JSON helpers, `build_claude_args`, `build_claude_stream_args`, `parse_claude_json_response`, `parse_claude_stream_line`, `claude_cli_send`, `claude_cli_stream` |
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
| `src/app/llm_caret/chat.spl` | `fn:_LB`, `fn:_RB`, `fn:_Q`, `fn:_escape_json`, `fn:chat_clear`, `fn:chat_set_system_prompt`, `fn:chat_get_system_prompt`, `fn:chat_set_max_history`, `fn:chat_add_message`, `fn:chat_add_user`, `fn:chat_add_assistant`, `fn:chat_history_len`, `fn:chat_get_role`, `fn:chat_get_content`, `fn:chat_truncate`, `fn:chat_build_messages_json`, `fn:chat_last_content`, `fn:chat_last_role` |
| `src/app/llm_caret/claude_api.spl` | `extern:rt_http_request`, `fn:_LB`, `fn:_RB`, `fn:_Q`, `fn:_unwrap_idx`, `fn:_escape_json`, `fn:_extract_json_string`, `fn:_extract_json_value`, `fn:_extract_json_int`, `struct:ApiResponse`, `fn:build_claude_api_body`, `fn:build_claude_api_headers`, `fn:build_single_message_json`, `fn:parse_claude_api_response`, `fn:claude_api_send` |
| `src/app/llm_caret/claude_cli.spl` | `fn:_json_text`, `fn:_json_i64`, `fn:_json_bool`, `fn:_json_raw`, `fn:_json_usage_i64`, `fn:_json_message_field`, `fn:_json_message_usage_i64`, `fn:_json_message_content`, `struct:CliResponse`, `struct:CliStreamEvent`, `fn:_invalid_cli_response`, `fn:build_claude_args`, `fn:build_claude_args_simple`, `fn:build_claude_stream_args`, `fn:parse_claude_json_response`, `fn:parse_claude_stream_line`, `fn:claude_cli_send`, `fn:claude_cli_stream` |
| `src/app/llm_caret/config.spl` | `extern:rt_file_read_text`, `fn:config_loaded`, `fn:config_default_provider`, `fn:config_history_file`, `fn:config_max_history`, `fn:config_claude_cli_path`, `fn:config_claude_cli_model`, `fn:config_opencode_cli_path`, `fn:config_opencode_cli_model`, `fn:config_claude_api_key`, `fn:config_claude_api_base_url`, `fn:config_claude_api_model`, `fn:config_openai_api_key`, `fn:config_openai_base_url`, `fn:config_openai_model`, `fn:config_compat_base_url`, `fn:config_compat_model`, `fn:config_compat_api_key`, `fn:config_local_model_path`, `fn:config_local_python_path`, `fn:load_config`, `fn:parse_config_text`, `fn:_unwrap_idx_cfg`, `fn:_apply_config`, `fn:load_defaults`, `fn:reset_config` |
| `src/app/llm_caret/json_helpers.spl` | `fn:escape_json_text`, `fn:jo1`, `fn:jo2`, `fn:jo3`, `fn:jo4`, `fn:jo5`, `fn:jo6`, `fn:ja`, `fn:_unwrap_idx`, `fn:extract_json_string`, `fn:extract_json_value`, `fn:extract_json_int`, `fn:extract_json_bool`, `fn:extract_nested_string`, `fn:build_message_json`, `fn:build_messages_json` |
| `src/app/llm_caret/local_torch.spl` | `extern:rt_file_write_text`, `extern:rt_file_read_text`, `extern:rt_file_delete`, `extern:rt_time_now_unix_micros`, `struct:LocalResponse`, `fn:build_torch_script`, `fn:local_torch_send` |
| `src/app/llm_caret/mod.spl` | `fn:_LB`, `fn:_RB`, `fn:_Q`, `fn:_unwrap_idx`, `fn:_escape_json`, `fn:_extract_json_string`, `fn:_extract_json_value`, `fn:_extract_json_bool`, `fn:_extract_json_int`, `fn:llm_init_defaults`, `fn:llm_init`, `fn:llm_set_api_key`, `fn:llm_set_base_url`, `fn:llm_set_cli_path`, `fn:llm_system`, `fn:llm_provider`, `fn:llm_model`, `fn:llm_clear`, `fn:llm_history_len`, `fn:llm_history_role`, `fn:llm_history_content`, `fn:_build_messages_json`, `fn:llm_chat`, `fn:_send_claude_cli`, `fn:_send_opencode_cli`, `fn:_send_claude_api`, `fn:_send_openai`, `fn:llm_send` |
| `src/app/llm_caret/openai_api.spl` | `extern:rt_http_request`, `fn:_LB`, `fn:_RB`, `fn:_Q`, `fn:_unwrap_idx`, `fn:_escape_json`, `fn:_extract_json_string`, `fn:_extract_json_value`, `fn:_extract_json_int`, `struct:OpenAIResponse`, `fn:build_openai_body`, `fn:build_openai_headers`, `fn:build_openai_messages_json`, `fn:parse_openai_response`, `fn:openai_send` |
| `src/app/llm_caret/openai_compat.spl` | `extern:rt_http_request`, `fn:_LB`, `fn:_RB`, `fn:_Q`, `fn:_unwrap_idx`, `fn:_escape_json`, `fn:_extract_json_string`, `fn:_extract_json_value`, `fn:_extract_json_int`, `struct:CompatResponse`, `fn:build_compat_body`, `fn:build_compat_headers`, `fn:parse_compat_response`, `fn:compat_send` |
| `src/app/llm_caret/opencode_cli.spl` | `struct:OpencodeCliResponse`, `struct:OpencodeProcessResult`, `fn:_Q`, `fn:_unwrap_idx`, `fn:_extract_json_string`, `fn:_json_string_value_after_key`, `fn:_first_non_empty` |
| `src/app/llm_caret/provider.spl` | `extern:rt_http_request`, `fn:_LB`, `fn:_RB`, `fn:_Q`, `fn:_unwrap_idx`, `fn:_escape_json`, `fn:_extract_json_string`, `fn:_extract_json_value`, `fn:_extract_json_int`, `fn:_extract_json_bool`, `struct:LLMResponse`, `fn:new_llm_error`, `fn:list_providers`, `fn:is_valid_provider`, `fn:dispatch_send`, `fn:_dispatch_opencode_cli`, `fn:_build_cli_args`, `fn:_dispatch_claude_cli`, `fn:_dispatch_claude_api`, `fn:_dispatch_openai`, `fn:_dispatch_compat` |
| `src/app/llm_caret/server.spl` | `extern:rt_http_request`, `fn:_LB`, `fn:_RB`, `fn:_Q`, `fn:_unwrap_idx`, `fn:_escape_json`, `fn:_extract_json_string`, `fn:build_health_response`, `fn:build_models_response`, `fn:build_chat_completion_response`, `fn:build_anthropic_response`, `fn:build_error_response`, `fn:parse_chat_request_model`, `fn:parse_chat_request_content`, `fn:handle_route` |
| `src/app/llm_caret/types.spl` | `struct:Message`, `fn:new_message`, `fn:new_user_message`, `fn:new_assistant_message`, `fn:new_system_message`, `struct:ChatRequest`, `fn:new_chat_request`, `fn:new_chat_request_with_prompt`, `struct:ChatResponse`, `fn:new_chat_response`, `fn:new_error_response`, `fn:new_success_response`, `struct:StreamEvent`, `fn:new_stream_event`, `fn:new_text_delta`, `fn:new_message_stop`, `struct:ProviderConfig`, `fn:new_provider_config`, `fn:is_user_message`, `fn:is_assistant_message`, `fn:is_system_message`, `fn:response_ok`, `fn:response_has_content` |

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
