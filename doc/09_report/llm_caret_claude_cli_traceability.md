# LLM Caret Claude CLI Traceability

Date: 2026-07-05

## MDSOC+ Caret Boundary

`src/app/llm_caret` is the app-layer LLM provider caret. It owns provider
selection, CLI/API request construction, response normalization, and lightweight
server compatibility. Terminal effects are supplied through the Simple-only
`CaretIo` capability adapter in `tui_io.spl`; process and environment effects
remain behind existing app/runtime facades. This lane does not migrate Claude's
React terminal UI,
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
| `src/app/llm_caret/chat_tui.spl` | 794 | `src/screens/REPL.tsx`, `src/commands/*` | transcript, slash commands, session transitions, and lifecycle-safe injected I/O |
| `src/app/llm_caret/claude_api.spl` | 241 | `src/QueryEngine.ts`, `src/entrypoints/sdk/coreSchemas.ts` | Anthropic Messages request/response |
| `src/app/llm_caret/claude_cli.spl` | 580 | `src/entrypoints/cli.tsx`, `src/QueryEngine.ts` | non-interactive argv and typed JSON/stream parsing |
| `src/app/llm_caret/config.spl` | 228 | `src/bootstrap/state.ts`, `src/constants/product.ts` | defaults and provider config |
| `src/app/llm_caret/gui.spl` | 128 | Simple-only provider UI extension | browser GUI outside focused Claude CLI parity |
| `src/app/llm_caret/gui_metal.spl` | 205 | Simple-only provider UI extension | native Metal GUI outside focused Claude CLI parity |
| `src/app/llm_caret/gui_native_model.spl` | 69 | Simple-only provider UI extension | native GUI state outside focused Claude CLI parity |
| `src/app/llm_caret/interface_text.spl` | 11 | Simple-only presentation seam | shared role and transcript text |
| `src/app/llm_caret/json_helpers.spl` | 250 | Simple-only shared helper | local JSON helper caret utility |
| `src/app/llm_caret/local_torch.spl` | 98 | Simple-only provider extension | local model provider outside Claude parity |
| `src/app/llm_caret/main.spl` | 961 | `src/entrypoints/cli.tsx`, `src/QueryEngine.ts`, `src/screens/REPL.tsx` | CLI entrypoint, runtime state, proxy, and typed UI-result routing |
| `src/app/llm_caret/mod.spl` | 409 | `src/QueryEngine.ts`, `src/bootstrap/state.ts` | public API, state, provider dispatch |
| `src/app/llm_caret/openai_api.spl` | 260 | `src/entrypoints/sdk/coreSchemas.ts` | OpenAI-compatible provider extension |
| `src/app/llm_caret/openai_compat.spl` | 203 | `src/entrypoints/sdk/coreSchemas.ts` | local/OpenAI-compatible endpoint provider |
| `src/app/llm_caret/opencode_cli.spl` | 149 | Simple-only Claude-like CLI provider | OpenCode adapter with Claude-like response shape |
| `src/app/llm_caret/provider.spl` | 440 | `src/Tool.ts`, `src/constants/tools.ts`, `src/entrypoints/sdk/coreSchemas.ts` | provider registry and normalized response |
| `src/app/llm_caret/redact.spl` | 336 | Security utility; exact provenance unavailable | credential and diagnostic redaction |
| `src/app/llm_caret/retry.spl` | 188 | Claude API retry/backoff behavior (conceptual) | retry admission, delay, and deadline budget |
| `src/app/llm_caret/server.spl` | 199 | `src/entrypoints/mcp.ts`, `src/entrypoints/sdk/coreSchemas.ts` | compatibility HTTP/MCP-like response surface |
| `src/app/llm_caret/session.spl` | 245 | `src/assistant/sessionHistory.ts`, `src/bootstrap/state.ts` | persisted app/provider sessions |
| `src/app/llm_caret/tools.spl` | 508 | `src/Tool.ts`, `src/constants/tools.ts` | permission-gated tools and tool-use parsing |
| `src/app/llm_caret/tui_input.spl` | 222 | `src/screens/REPL.tsx` | real TTY/TERM renderer selection, ANSI/UTF-8 decoding, and raw-line control reduction |
| `src/app/llm_caret/tui_io.spl` | 101 | Simple-only terminal capability adapter | injected terminal size/raw/screen/byte/line/output operations with production stdlib wiring |
| `src/app/llm_caret/types.spl` | 225 | `src/entrypoints/sdk/coreSchemas.ts`, `src/types/logs.ts` | request/response/event/config records |

Mapped files at this checkpoint: 25/25 = 100%.
Mapped LOC at this checkpoint: 7278/7278 = 100%.
Current direct declaration inventory: 496 symbols; the checker must prove
496/496 after the symbol TSV is regenerated.

These counts include the new `tui_io.spl` row and match the regenerated
file-qualified inventory. They prove direct-file classification, not executed
behavior or full Claude parity. Simple-only and conceptual rows are explicit,
and upstream freshness remains unverifiable while the historical Claude source
tree is absent.

## Focused Test Mapping

| Behavior | Primary executable evidence |
|---|---|
| CLI argv, typed JSON/NDJSON, subprocess forwarding, redaction, public history | `test/03_system/tools/llm/llm_caret_claude_cli_feature_contract_spec.spl` |
| Caret process help/success/error/usage exits | `test/03_system/app/llm_caret/feature/llm_caret_cli_hardening_spec.spl` |
| TUI submission/state/session/permission/retry/hidden admission | `test/03_system/app/llm_caret/feature/llm_caret_tui_hidden_feature_spec.spl` |
| Live terminal routing/lifecycle/UTF-8/geometry/raw rejection | `test/03_system/app/llm_caret/feature/llm_caret_tui_pty_spec.spl` through `scripts/check/check-llm-caret-tui-pty.shs`; execution requires cached `bin/caret`, `script(1)`, and `stty` |
| Focused unit branches | `test/01_unit/app/llm_caret/claude_cli_spec.spl`, `chat_spec.spl`, `chat_tui_spec.spl`, `chat_tui_input_spec.spl`, `chat_tui_runtime_spec.spl`, `main_spec.spl`, `config_spec.spl`, `tools_spec.spl`, `types_spec.spl`, `provider_spec.spl`, `retry_spec.spl` under `test/01_unit/app/llm_caret/` |
| Offline native seams | `test/04_smoke/llm_caret_cli_tui_hardening_smoke.spl` |

These specs do not green historical full-parity rows whose implementation
target is absent.

## Function Trace

| Simple file | Public or key functions/classes |
|---|---|
| `chat.spl` | `chat_clear`, `chat_set_system_prompt`, `chat_add_message`, `chat_truncate`, `chat_build_messages_json`, `chat_last_content`, `chat_last_role` |
| `chat_tui.spl` | `SessionHooks`, `dispatch_slash`, `run_chat_tui_submission`, `run_chat_tui`, `run_chat_plain`, `caret_chat` |
| `claude_api.spl` | `ApiResponse`, `build_claude_api_body`, `build_claude_api_headers`, `build_single_message_json`, `parse_claude_api_response`, `claude_api_send` |
| `claude_cli.spl` | `CliResponse`, `CliStreamEvent`, typed JSON helpers, `build_claude_args`, `build_claude_stream_args`, `parse_claude_json_response`, `parse_claude_stream_line`, `claude_cli_send`, `claude_cli_stream` |
| `config.spl` | `config_loaded`, `config_default_provider`, provider default getters, config parsing helpers |
| `gui.spl` | `run_gui` and GUI route/process helpers |
| `gui_metal.spl` | `CaretMetalState`, Metal composition/presentation helpers, `run_caret_metal_gui` |
| `gui_native_model.spl` | `CaretNativeModelState` and native model updates |
| `interface_text.spl` | `caret_role_label`, `caret_turn_line` |
| `json_helpers.spl` | `escape_json_text`, `jo1`-`jo6`, `ja`, `extract_json_string`, `extract_json_value`, `extract_json_int`, `extract_json_bool`, `extract_nested_string`, `build_message_json`, `build_messages_json` |
| `local_torch.spl` | `LocalResponse`, `build_torch_script`, `local_torch_send` |
| `main.spl` | `MainArgs`, `ResumeBackend`, `resolve_resume_backend`, `main_configure`, `main_responder`, proxy guards, slash hooks, `main` |
| `mod.spl` | `llm_init_defaults`, `llm_init`, `llm_set_api_key`, `llm_set_base_url`, `llm_set_cli_path`, `llm_system`, `llm_clear`, `llm_history_*`, `llm_chat`, `llm_send` |
| `openai_api.spl` | `OpenAIResponse`, `build_openai_body`, `build_openai_headers`, `build_openai_messages_json`, `parse_openai_response`, `openai_send` |
| `openai_compat.spl` | `CompatResponse`, `build_compat_body`, `build_compat_headers`, `parse_compat_response`, `compat_send` |
| `opencode_cli.spl` | `OpencodeCliResponse`, `OpencodeProcessResult`, OpenCode argv/parse/process helpers |
| `provider.spl` | `LLMResponse`, `dispatch_send`, `dispatch_send_advanced`, provider-specific dispatch helpers |
| `redact.spl` | secret classifiers and text/JSON/URL/header redaction |
| `retry.spl` | `RetryPolicy`, `RetryOutcome`, retry admission, capped backoff, deadline-budgeted `with_retry` |
| `server.spl` | `build_health_response`, `build_models_response`, `build_chat_completion_response`, `build_anthropic_response`, `build_error_response`, `handle_route` |
| `session.spl` | `Session`, session ID/path/save/load/list helpers |
| `tools.spl` | permission policy, tool models, path guards, execution, tool-use parsing |
| `tui_input.spl` | renderer selection, real stdin TTY plus TERM policy, ANSI/UTF-8 raw-key decoding, raw-line control reduction, input transitions |
| `tui_io.spl` | `CaretIo`, production terminal capability adapters, terminal size/raw/screen/read/emit functions |
| `types.spl` | `Message`, `ChatRequest`, `ChatResponse`, `StreamEvent`, `ProviderConfig`, constructors, response predicates |

## Simple Symbol Trace

The authoritative file-qualified inventory is `doc/09_report/llm_caret_claude_cli_symbols.tsv`. It is generated from every direct `fn`, `pub fn`, `struct`, and `extern fn` declaration. The trace checker compares exact `source-file<TAB>kind:name` identities in both directions, so symbols with the same name in different files cannot satisfy one another and stale rows fail.

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
sh scripts/check/check-llm-caret-tui-pty.shs --case all
bin/simple test test/03_system/tools/llm/llm_caret_claude_cli_traceability_spec.spl --mode=interpreter
bin/simple test test/03_system/app/llm_caret/feature/llm_caret_tui_pty_spec.spl --mode=interpreter
```
