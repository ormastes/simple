# MCP/LSP Core-Lane Dependency Inventory

Date: 2026-05-04

Parent plan: `doc/03_plan/default_native_runtime_shift_phase2_plan.md`

## Scope

Live entrypoints:
- `src/app/mcp/main.spl`
- `src/app/simple_lsp_mcp/main.spl`

Adjacent modules required by the phase 2 plan:
- `src/app/mcp/main_dispatch.spl`
- `src/app/mcp/tool_registry.spl`
- `src/app/mcp/startup_log.spl`
- `src/app/simple_lsp_mcp/protocol.spl`
- `src/app/simple_lsp_mcp/tools.spl`

## Startup-Critical Dependencies

These are required before the servers can pass initialize, initialized, and tools/list health checks on a core lane.

| Area | MCP evidence | Simple LSP MCP evidence | Core-lane requirement |
|------|--------------|-------------------------|-----------------------|
| Framed stdio input | `main.spl` calls `read_stdin_message`; `main_lazy_protocol.spl` declares `stdin_read_char` and parses `Content-Length` | `main.spl` calls `read_stdin_message`; `json_helpers.spl` declares `stdin_read_char`, `rt_stdin_read_line`, and parses `Content-Length` | Core stdin char or framed-read primitive; no stdlib loader read block during startup |
| Framed stdio output | `main.spl` calls `write_stdout_message`; `main_lazy_protocol.spl` formats `Content-Length` | `main.spl` calls `write_stdout_message`; `json_helpers.spl` declares `print_raw` and formats `Content-Length` | Core stdout raw write with exact byte length behavior |
| JSON field extraction and response building | `main_lazy_json.spl`, `main_lazy_protocol.spl` provide `extract_id`, method detection, JSON result/error helpers | `json_helpers.spl`, `protocol.spl` provide equivalent helpers and initialize/tools schemas | Pure Simple text parsing/serialization must remain reachable without hosted runtime |
| Process exit | `main.spl` declares/calls `rt_exit` | `main.spl` calls `rt_exit` | `rt_exit` remains core-required |
| Startup diagnostics | `startup_log.spl` declares `rt_env_get`, `rt_env_cwd`, `rt_file_append_text`, `rt_file_exists`, `rt_time_now_unix_micros`, `rt_dir_create_all` | same pattern in `simple_lsp_mcp/startup_log.spl` | Either port these env/file/time helpers or make startup logging optional with a clear hosted-only boundary |
| Tool registry response | `main.spl` uses `_mcp_static_tools_result()` for tools/list | `protocol.spl` builds static tool schemas | Static tools/list must not require subprocess, filesystem scans, or hosted archive fallback |

## Hot Request Path Dependencies

These are needed after startup for normal tool calls. They can be ported after startup if missing capabilities fail clearly as hosted-only.

| Area | Evidence | Classification |
|------|----------|----------------|
| File read/write/existence | MCP: `rt_file_read_text`, `rt_file_write_text`, `rt_file_exists`, `file_read`, `file_write`; LSP: `rt_file_exists`; assistant modules use `rt_file_read_text`, `rt_file_write_text`, `rt_dir_list`, `rt_mkdir_p` | Core utility for workspace tools, or explicit hosted-only for write/list/session storage |
| Environment and cwd | MCP and LSP startup logs use `rt_env_get`, `rt_env_cwd`; query helpers use `rt_env_get`; LSP helper discovers `SIMPLE_BINARY` and `OS` | Startup-critical for current logging and binary discovery unless logging/discovery is gated |
| Process execution | MCP `main_lazy_json.spl`, dialog/play tools, and CLI passthrough use `rt_process_run`; LSP `json_helpers.spl` and `tools.spl` use `rt_process_run` | Hosted-only until a core process API is defined; must not force whole server to `rust-hosted` |
| Async process/session control | `dap_bridge.spl` declares `rt_process_spawn_async`, `rt_process_is_running`, `rt_process_kill`; assistant/session modules use time and filesystem storage | Hosted-only until process/session helpers are ported |
| Time | startup logs, assistant/session types, and DAP bridge use `rt_time_now_unix_micros` | Core time helper or hosted-only diagnostics/session boundary |
| TRACE32/dialog tooling | `main_lazy_dialog_tools.spl` shells to `t32rem` through `rt_process_run` | Hosted-only tool boundary |

## First Port/Gate Order

1. Framed stdio: `stdin_read_char`, raw stdout write, exact `Content-Length`.
2. Pure Simple JSON helpers for initialize, initialized, tools/list, logging/setLevel, roots/list.
3. Startup diagnostics: either port env/cwd/file append/time/dir create, or disable with a clear nonfatal hosted-only message.
4. File/env helpers used by read-only workspace tools.
5. Process execution and async sessions as explicit hosted-only tool capabilities until a core process API exists.

## Verification Anchors

- `test/system/mcp/mcp_startup_test_system.shs`
- `test/system/mcp/mcp_lifecycle_test_system.shs`
- `test/integration/app/mcp_stdio_integration_spec.spl`
- Native package checks must reject `libsimple_native_all.a` and unwind dependencies before MCP/LSP packaging is considered core-lane complete.

## Probe Results 2026-05-04

- Full MCP core-C build command:
  `bin/simple native-build --runtime-bundle core-c --source src/compiler --source src/app --source src/lib --entry-closure --entry src/app/mcp/main.spl --strip --output /tmp/simple_mcp_core_c_probe --clean`
  Result: fails before link with `src/compiler/frontend/flat_ast_bridge.spl` HIR error: `Cannot infer field type: struct 'Function' field 'params'`.
- Full Simple LSP MCP core-C build with `src/compiler` included hits the same compiler-module class of blocker before runtime closure can be validated.
- Startup-only Simple LSP MCP build with `--source src/app --source src/lib` links on `core-c`:
  `Build complete: 93 compiled, 0 cached, 0 failed`, binary size `262416` bytes when stripped.
- Tiny direct ABI probes for `extern fn print_raw(s: text)` and `extern fn stdin_read_char() -> text` pass on `core-c`.
- Imported `write_stdout_message("X")` now emits output after adding core text helpers for `rt_len`, `rt_to_string`, and `rt_string_concat`.
- Imported `read_stdin_message()` now returns JSON-lines input correctly after adding core text predicates/parsers for `rt_native_eq`, `rt_native_neq`, `rt_slice`, `rt_string_starts_with`, `rt_string_ends_with`, `rt_string_replace`, `rt_string_trim`, and `rt_string_to_int`.
- Startup-only Simple LSP MCP now answers JSON-lines `initialize` and `tools/list` on `core-c`:
  - `initialize` returns protocol/capabilities/serverInfo.
  - `tools/list` returns an empty tools array in this reduced-source probe because `src/compiler` is intentionally omitted to avoid the known compiler HIR blocker.
- Simple LSP MCP output framing is now deterministic `Content-Length`; a startup-only core-C probe returns a framed initialize response (`Content-Length: 379`) for a framed initialize request.
- Regression coverage: `test_core_c_lane_simple_lsp_mcp_startup_initialize_reduced_source` builds the reduced-source Simple LSP MCP startup binary through the current Rust native-project builder and asserts the framed initialize response.
- Full Simple LSP MCP with `--source src/compiler --source src/app --source src/lib` now links on `core-c`; the build still generates internal Simple stubs, so it is not yet a package-closure PASS.
- Full MCP with `--source src/compiler --source src/app --source src/lib` now links on `core-c`; it also generates internal Simple stubs, so it is not yet a package-closure PASS.
- Full Simple LSP MCP now passes a two-message framed initialize + tools/list smoke on `core-c`: two `Content-Length` responses, id `2` present, and real LSP tool names including `lsp_definition` and `lsp_type_definition`.
- App-only MCP and Simple LSP MCP package-shape builds now succeed on `core-c` with `--source src/app --entry-closure`; this avoids pulling the broader compiler/lib source roots into the package closure.
- App-only MCP JSON-lines initialize + tools/list smoke passes on `core-c`; `tools/list` includes real static tool schemas such as `debug_create_session`, `simple_check`, and `test_daemon_status`.
- App-only Simple LSP MCP framed initialize + tools/list smoke passes on `core-c`; `tools/list` includes real LSP tool schemas such as `lsp_definition`.
- Closure audit for the app-only MCP and Simple LSP MCP core-C binaries found no `libsimple_native_all.a`, `rust-hosted`, or unwind symbols/strings.
- The native linker still emits its generic `_stubs.o` allowlist, but app-only builds no longer report direct unresolved internal/runtime symbols in the package probes.
- `scripts/check-mcp-native-smoke.shs` now validates MCP JSON-lines and Simple LSP MCP framed `Content-Length` output; package outputs report `mcp_tools_count=144` and `lsp_tools_count=11` with valid schemas.
- `scripts/check-simple-core-runtime-smoke.shs` now provides a repeatable explicit `simple-core` gate for hello, the generated standalone TUI wrapper, and the real `run_tui("examples/ui/minimal.ui.sdn")` app path, with closure checks for hosted-runtime and unwind markers.
- Core C runtime now implements the compiled Simple array ABI used by core-lane entry closures (`rt_array_push` returns success, `rt_array_get`/`rt_index_get` return raw runtime values, and `rt_len` recognizes raw arrays). A native `[text]` probe verifies push/len/index on explicit `simple-core`.
