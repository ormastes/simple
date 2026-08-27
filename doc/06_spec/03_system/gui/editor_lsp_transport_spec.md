# Editor Lsp Transport Specification

> <details>

<!-- sdn-diagram:id=editor_lsp_transport_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=editor_lsp_transport_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

editor_lsp_transport_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=editor_lsp_transport_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 48 | 48 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Lsp Transport Specification

## Scenarios

### LSP transport — Content-Length framing

#### defines LspTransportConfig struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("struct LspTransportConfig:")).to_equal(true)
expect(src.contains("server_command: text")).to_equal(true)
expect(src.contains("server_args: [text]")).to_equal(true)
expect(src.contains("root_uri: text")).to_equal(true)
```

</details>

#### defines StdioTransport struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("struct StdioTransport:")).to_equal(true)
expect(src.contains("running: bool")).to_equal(true)
expect(src.contains("send_buffer: [text]")).to_equal(true)
expect(src.contains("recv_buffer: [text]")).to_equal(true)
```

</details>

#### has lsp_frame_message for Content-Length framing

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("fn lsp_frame_message(json: text) -> text")).to_equal(true)
expect(src.contains("Content-Length:")).to_equal(true)
expect(src.contains("\\r\\n\\r\\n")).to_equal(true)
```

</details>

#### has lsp_parse_frame for reading framed messages

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("fn lsp_parse_frame(buf: text) -> (text, i64)")).to_equal(true)
expect(src.contains("_lsp_find_header_end")).to_equal(true)
expect(src.contains("_lsp_parse_content_length")).to_equal(true)
```

</details>

### LSP transport — message building

#### has lsp_build_initialize_params

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("fn lsp_build_initialize_params(root_uri: text, client_name: text) -> text")).to_equal(true)
expect(src.contains("processId")).to_equal(true)
expect(src.contains("capabilities")).to_equal(true)
```

</details>

#### has lsp_build_did_open_params

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("fn lsp_build_did_open_params(uri: text, language_id: text, version: i64, content: text) -> text")).to_equal(true)
```

</details>

#### has lsp_build_did_change_params

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("fn lsp_build_did_change_params(uri: text, version: i64, content: text) -> text")).to_equal(true)
```

</details>

#### has lsp_build_position_params for completion/hover/definition

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("fn lsp_build_position_params(uri: text, line: i64, col: i64) -> text")).to_equal(true)
```

</details>

### LSP transport — URI handling

#### has lsp_path_to_uri

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("fn lsp_path_to_uri(path: text) -> text")).to_equal(true)
expect(src.contains("file://")).to_equal(true)
```

</details>

#### has lsp_uri_to_path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("fn lsp_uri_to_path(uri: text) -> text")).to_equal(true)
```

</details>

### LSP transport — response parsing

#### has lsp_parse_response_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("fn lsp_parse_response_id(json: text) -> i64")).to_equal(true)
```

</details>

#### has lsp_parse_response_result and lsp_parse_response_error

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("fn lsp_parse_response_result(json: text) -> text")).to_equal(true)
expect(src.contains("fn lsp_parse_response_error(json: text) -> text")).to_equal(true)
```

</details>

#### has lsp_is_response and lsp_is_notification

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("fn lsp_is_response(json: text) -> bool")).to_equal(true)
expect(src.contains("fn lsp_is_notification(json: text) -> bool")).to_equal(true)
```

</details>

#### has lsp_parse_notification_params

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("fn lsp_parse_notification_params(json: text) -> text")).to_equal(true)
```

</details>

#### has lsp_parse_notification_method

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("fn lsp_parse_notification_method(json: text) -> text")).to_equal(true)
```

</details>

### LSP client — transport wiring

#### has transport field on LspClient

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_client.spl")
expect(src.contains("transport: StdioTransport")).to_equal(true)
```

</details>

#### has start and stop lifecycle methods

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_client.spl")
expect(src.contains("me start() -> bool")).to_equal(true)
expect(src.contains("me stop()")).to_equal(true)
```

</details>

#### has pending_requests tracking

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_client.spl")
expect(src.contains("pending_requests: [LspPendingRequest]")).to_equal(true)
expect(src.contains("struct LspPendingRequest:")).to_equal(true)
```

</details>

#### sends JSON-RPC via transport

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_client.spl")
expect(src.contains("fn lsp_jsonrpc_request(id: text, method: text, params: text) -> text")).to_equal(true)
expect(src.contains("fn lsp_jsonrpc_notification(method: text, params: text) -> text")).to_equal(true)
expect(src.contains("jsonrpc")).to_equal(true)
expect(src.contains("2.0")).to_equal(true)
```

</details>

#### has initialized_notification

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_client.spl")
expect(src.contains("me initialized_notification()")).to_equal(true)
```

</details>

#### has exit for clean shutdown

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_client.spl")
expect(src.contains("me exit()")).to_equal(true)
```

</details>

#### has poll_notifications for server push

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_client.spl")
expect(src.contains("me poll_notifications() -> [LspNotification]")).to_equal(true)
```

</details>

#### has lsp_response_from_json parser

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_client.spl")
expect(src.contains("fn lsp_response_from_json(json: text) -> LspResponse")).to_equal(true)
```

</details>

### diagnostics — LSP publishDiagnostics wiring

#### has diagnostics_handle_publish

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/diagnostics.spl")
expect(src.contains("fn diagnostics_handle_publish(store: DiagnosticStore, params_json: text)")).to_equal(true)
```

</details>

#### extracts URI from publish params

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/diagnostics.spl")
expect(src.contains("fn _diag_extract_uri(json: text) -> text")).to_equal(true)
expect(src.contains("lsp_uri_to_path")).to_equal(true)
```

</details>

#### parses diagnostic entries from JSON array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/diagnostics.spl")
expect(src.contains("fn _diag_parse_diagnostics(json: text, path: text) -> [EditorDiagnostic]")).to_equal(true)
expect(src.contains("fn _diag_parse_single(entry: text, path: text) -> EditorDiagnostic")).to_equal(true)
```

</details>

#### maps LSP severity codes to editor severities

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/diagnostics.spl")
expect(src.contains("fn _diag_severity_from_lsp(code: i64) -> text")).to_equal(true)
```

</details>

### completion — LSP completion response wiring

#### has completion_handle_response

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/completion.spl")
expect(src.contains("fn completion_handle_response(state: CompletionState, result_json: text, prefix: text)")).to_equal(true)
```

</details>

#### parses completion items from JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/completion.spl")
expect(src.contains("fn _completion_parse_items(json: text) -> [CompletionItem]")).to_equal(true)
```

</details>

#### maps LSP completion kind codes to names

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/completion.spl")
expect(src.contains("fn _completion_kind_name(code: i64) -> text")).to_equal(true)
```

</details>

#### parses LSP result items

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = "{\"items\":[{\"label\":\"print\",\"detail\":\"fn\",\"insertText\":\"print()\",\"kind\":3},{\"label\":\"val\",\"kind\":14}]}"
val items = _completion_parse_items(result)
expect(items.len()).to_equal(2)
expect(items[0].label).to_equal("print")
expect(items[0].insert_text).to_equal("print()")
expect(items[0].kind).to_equal("function")
expect(items[1].insert_text).to_equal("val")
expect(items[1].kind).to_equal("keyword")
```

</details>

### LSP transport — stdio operations

#### has stdio_transport_new factory

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("fn stdio_transport_new(config: LspTransportConfig) -> StdioTransport")).to_equal(true)
```

</details>

#### has start and stop

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("fn stdio_transport_start(transport: StdioTransport) -> bool")).to_equal(true)
expect(src.contains("fn stdio_transport_stop(transport: StdioTransport)")).to_equal(true)
```

</details>

#### has send and receive

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("fn stdio_transport_send(transport: StdioTransport, json: text) -> bool")).to_equal(true)
expect(src.contains("fn stdio_transport_receive(transport: StdioTransport) -> text")).to_equal(true)
```

</details>

#### has inject_response for testing

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("fn stdio_transport_inject_response(transport: StdioTransport, json: text)")).to_equal(true)
```

</details>

### LSP transport — process-backed StdioProcessTransport

#### declares rt_process_spawn_piped extern

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("extern fn rt_process_spawn_piped(cmd: text, args: [text]) -> i64")).to_equal(true)
```

</details>

#### declares rt_process_write_stdin extern

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("extern fn rt_process_write_stdin(pid: i64, data: text) -> bool")).to_equal(true)
```

</details>

#### declares rt_process_read_stdout extern

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("extern fn rt_process_read_stdout(pid: i64) -> text")).to_equal(true)
```

</details>

#### declares rt_process_is_alive extern

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("extern fn rt_process_is_alive(pid: i64) -> bool")).to_equal(true)
```

</details>

#### declares rt_process_kill extern

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("extern fn rt_process_kill(pid: i64) -> bool")).to_equal(true)
```

</details>

#### defines StdioProcessTransport class with pid field

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("class StdioProcessTransport:")).to_equal(true)
expect(src.contains("pid: i64")).to_equal(true)
```

</details>

#### defines StdioProcessTransport class with server_cmd and server_args fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("server_cmd: text")).to_equal(true)
expect(src.contains("server_args: [text]")).to_equal(true)
```

</details>

#### defines StdioProcessTransport class with buffer field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("buffer: text")).to_equal(true)
```

</details>

#### has static new constructor that spawns process

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("static fn new(cmd: text, args: [text]) -> StdioProcessTransport")).to_equal(true)
expect(src.contains("rt_process_spawn_piped")).to_equal(true)
```

</details>

#### has send method writing framed message to stdin

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("me send(message: text) -> bool")).to_equal(true)
expect(src.contains("rt_process_write_stdin")).to_equal(true)
expect(src.contains("lsp_frame_message")).to_equal(true)
```

</details>

#### has receive method reading from stdout and parsing frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("me receive() -> text")).to_equal(true)
expect(src.contains("rt_process_read_stdout")).to_equal(true)
expect(src.contains("lsp_parse_frame")).to_equal(true)
```

</details>

#### has is_connected method checking process liveness

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("fn is_connected() -> bool")).to_equal(true)
expect(src.contains("rt_process_is_alive")).to_equal(true)
```

</details>

#### has close method killing process

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("me close()")).to_equal(true)
expect(src.contains("rt_process_kill")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/editor_lsp_transport_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- LSP transport — Content-Length framing
- LSP transport — message building
- LSP transport — URI handling
- LSP transport — response parsing
- LSP client — transport wiring
- diagnostics — LSP publishDiagnostics wiring
- completion — LSP completion response wiring
- LSP transport — stdio operations
- LSP transport — process-backed StdioProcessTransport

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 48 |
| Active scenarios | 48 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
