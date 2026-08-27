# Editor Lsp Transport Specification

> Tests covering LSP transport — Content-Length framing, LSP transport — message building, LSP transport — URI handling, LSP transport — response parsing, LSP client — transport wiring, diagnostics — LSP publishDiagnostics wiring, completion — LSP completion response wiring, LSP transport — stdio operations, LSP transport — process-backed StdioProcessTransport.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 48 | 48 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Lsp Transport Specification

## Scenarios

### LSP transport — Content-Length framing

#### defines LspTransportConfig struct

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defines LspTransportConfig struct
   - Expected: src contains `struct LspTransportConfig:`
   - Expected: src contains `server_command: text`
   - Expected: src contains `server_args: [text]`
   - Expected: src contains `root_uri: text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines LspTransportConfig struct")
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("struct LspTransportConfig:")).to_equal(true)
expect(src.contains("server_command: text")).to_equal(true)
expect(src.contains("server_args: [text]")).to_equal(true)
expect(src.contains("root_uri: text")).to_equal(true)
```

</details>

#### defines StdioTransport struct

- defines StdioTransport struct
   - Expected: src contains `struct StdioTransport:`
   - Expected: src contains `running: bool`
   - Expected: src contains `send_buffer: [text]`
   - Expected: src contains `recv_buffer: [text]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines StdioTransport struct")
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("struct StdioTransport:")).to_equal(true)
expect(src.contains("running: bool")).to_equal(true)
expect(src.contains("send_buffer: [text]")).to_equal(true)
expect(src.contains("recv_buffer: [text]")).to_equal(true)
```

</details>

#### has lsp_frame_message for Content-Length framing

- has lsp_frame_message for Content-Length framing
   - Expected: src contains `fn lsp_frame_message(json: text) -> text`
   - Expected: src contains `Content-Length:`
   - Expected: src contains `\\r\\n\\r\\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has lsp_frame_message for Content-Length framing")
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("fn lsp_frame_message(json: text) -> text")).to_equal(true)
expect(src.contains("Content-Length:")).to_equal(true)
expect(src.contains("\\r\\n\\r\\n")).to_equal(true)
```

</details>

#### has lsp_parse_frame for reading framed messages

- has lsp_parse_frame for reading framed messages
   - Expected: src contains `fn lsp_parse_frame(buf: text) -> (text, i64)`
   - Expected: src contains `_lsp_find_header_end`
   - Expected: src contains `_lsp_parse_content_length`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has lsp_parse_frame for reading framed messages")
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("fn lsp_parse_frame(buf: text) -> (text, i64)")).to_equal(true)
expect(src.contains("_lsp_find_header_end")).to_equal(true)
expect(src.contains("_lsp_parse_content_length")).to_equal(true)
```

</details>

### LSP transport — message building

#### has lsp_build_initialize_params

- has lsp_build_initialize_params
   - Expected: src contains `fn lsp_build_initialize_params(root_uri: text, client_name: text) -> text`
   - Expected: src contains `processId`
   - Expected: src contains `capabilities`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has lsp_build_initialize_params")
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("fn lsp_build_initialize_params(root_uri: text, client_name: text) -> text")).to_equal(true)
expect(src.contains("processId")).to_equal(true)
expect(src.contains("capabilities")).to_equal(true)
```

</details>

#### has lsp_build_did_open_params

- has lsp_build_did_open_params
   - Expected: src contains `fn lsp_build_did_open_params(uri: text, language_id: text, version: i64, cont... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has lsp_build_did_open_params")
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("fn lsp_build_did_open_params(uri: text, language_id: text, version: i64, content: text) -> text")).to_equal(true)
```

</details>

#### has lsp_build_did_change_params

- has lsp_build_did_change_params
   - Expected: src contains `fn lsp_build_did_change_params(uri: text, version: i64, content: text) -> text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has lsp_build_did_change_params")
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("fn lsp_build_did_change_params(uri: text, version: i64, content: text) -> text")).to_equal(true)
```

</details>

#### has lsp_build_position_params for completion/hover/definition

- has lsp_build_position_params for completion/hover/definition
   - Expected: src contains `fn lsp_build_position_params(uri: text, line: i64, col: i64) -> text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has lsp_build_position_params for completion/hover/definition")
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("fn lsp_build_position_params(uri: text, line: i64, col: i64) -> text")).to_equal(true)
```

</details>

### LSP transport — URI handling

#### has lsp_path_to_uri

- has lsp_path_to_uri
   - Expected: src contains `fn lsp_path_to_uri(path: text) -> text`
   - Expected: src contains `file://`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has lsp_path_to_uri")
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("fn lsp_path_to_uri(path: text) -> text")).to_equal(true)
expect(src.contains("file://")).to_equal(true)
```

</details>

#### has lsp_uri_to_path

- has lsp_uri_to_path
   - Expected: src contains `fn lsp_uri_to_path(uri: text) -> text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has lsp_uri_to_path")
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("fn lsp_uri_to_path(uri: text) -> text")).to_equal(true)
```

</details>

### LSP transport — response parsing

#### has lsp_parse_response_id

- has lsp_parse_response_id
   - Expected: src contains `fn lsp_parse_response_id(json: text) -> i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has lsp_parse_response_id")
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("fn lsp_parse_response_id(json: text) -> i64")).to_equal(true)
```

</details>

#### has lsp_parse_response_result and lsp_parse_response_error

- has lsp_parse_response_result and lsp_parse_response_error
   - Expected: src contains `fn lsp_parse_response_result(json: text) -> text`
   - Expected: src contains `fn lsp_parse_response_error(json: text) -> text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has lsp_parse_response_result and lsp_parse_response_error")
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("fn lsp_parse_response_result(json: text) -> text")).to_equal(true)
expect(src.contains("fn lsp_parse_response_error(json: text) -> text")).to_equal(true)
```

</details>

#### has lsp_is_response and lsp_is_notification

- has lsp_is_response and lsp_is_notification
   - Expected: src contains `fn lsp_is_response(json: text) -> bool`
   - Expected: src contains `fn lsp_is_notification(json: text) -> bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has lsp_is_response and lsp_is_notification")
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("fn lsp_is_response(json: text) -> bool")).to_equal(true)
expect(src.contains("fn lsp_is_notification(json: text) -> bool")).to_equal(true)
```

</details>

#### has lsp_parse_notification_params

- has lsp_parse_notification_params
   - Expected: src contains `fn lsp_parse_notification_params(json: text) -> text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has lsp_parse_notification_params")
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("fn lsp_parse_notification_params(json: text) -> text")).to_equal(true)
```

</details>

#### has lsp_parse_notification_method

- has lsp_parse_notification_method
   - Expected: src contains `fn lsp_parse_notification_method(json: text) -> text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has lsp_parse_notification_method")
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("fn lsp_parse_notification_method(json: text) -> text")).to_equal(true)
```

</details>

### LSP client — transport wiring

#### has transport field on LspClient

- has transport field on LspClient
   - Expected: src contains `transport: StdioTransport`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has transport field on LspClient")
val src = read_text("src/lib/editor/services/lsp_client.spl")
expect(src.contains("transport: StdioTransport")).to_equal(true)
```

</details>

#### has start and stop lifecycle methods

- has start and stop lifecycle methods
   - Expected: src contains `me start() -> bool`
   - Expected: src contains `me stop()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has start and stop lifecycle methods")
val src = read_text("src/lib/editor/services/lsp_client.spl")
expect(src.contains("me start() -> bool")).to_equal(true)
expect(src.contains("me stop()")).to_equal(true)
```

</details>

#### has pending_requests tracking

- has pending_requests tracking
   - Expected: src contains `pending_requests: [LspPendingRequest]`
   - Expected: src contains `struct LspPendingRequest:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has pending_requests tracking")
val src = read_text("src/lib/editor/services/lsp_client.spl")
expect(src.contains("pending_requests: [LspPendingRequest]")).to_equal(true)
expect(src.contains("struct LspPendingRequest:")).to_equal(true)
```

</details>

#### sends JSON-RPC via transport

- sends JSON-RPC via transport
   - Expected: src contains `fn lsp_jsonrpc_request(id: text, method: text, params: text) -> text`
   - Expected: src contains `fn lsp_jsonrpc_notification(method: text, params: text) -> text`
   - Expected: src contains `jsonrpc`
   - Expected: src contains `2.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sends JSON-RPC via transport")
val src = read_text("src/lib/editor/services/lsp_client.spl")
expect(src.contains("fn lsp_jsonrpc_request(id: text, method: text, params: text) -> text")).to_equal(true)
expect(src.contains("fn lsp_jsonrpc_notification(method: text, params: text) -> text")).to_equal(true)
expect(src.contains("jsonrpc")).to_equal(true)
expect(src.contains("2.0")).to_equal(true)
```

</details>

#### has initialized_notification

- has initialized_notification
   - Expected: src contains `me initialized_notification()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has initialized_notification")
val src = read_text("src/lib/editor/services/lsp_client.spl")
expect(src.contains("me initialized_notification()")).to_equal(true)
```

</details>

#### has exit for clean shutdown

- has exit for clean shutdown
   - Expected: src contains `me exit()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has exit for clean shutdown")
val src = read_text("src/lib/editor/services/lsp_client.spl")
expect(src.contains("me exit()")).to_equal(true)
```

</details>

#### has poll_notifications for server push

- has poll_notifications for server push
   - Expected: src contains `me poll_notifications() -> [LspNotification]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has poll_notifications for server push")
val src = read_text("src/lib/editor/services/lsp_client.spl")
expect(src.contains("me poll_notifications() -> [LspNotification]")).to_equal(true)
```

</details>

#### has lsp_response_from_json parser

- has lsp_response_from_json parser
   - Expected: src contains `fn lsp_response_from_json(json: text) -> LspResponse`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has lsp_response_from_json parser")
val src = read_text("src/lib/editor/services/lsp_client.spl")
expect(src.contains("fn lsp_response_from_json(json: text) -> LspResponse")).to_equal(true)
```

</details>

### diagnostics — LSP publishDiagnostics wiring

#### has diagnostics_handle_publish

- has diagnostics_handle_publish
   - Expected: src contains `fn diagnostics_handle_publish(store: DiagnosticStore, params_json: text)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has diagnostics_handle_publish")
val src = read_text("src/lib/editor/services/diagnostics.spl")
expect(src.contains("fn diagnostics_handle_publish(store: DiagnosticStore, params_json: text)")).to_equal(true)
```

</details>

#### extracts URI from publish params

- extracts URI from publish params
   - Expected: src contains `fn _diag_extract_uri(json: text) -> text`
   - Expected: src contains `lsp_uri_to_path`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("extracts URI from publish params")
val src = read_text("src/lib/editor/services/diagnostics.spl")
expect(src.contains("fn _diag_extract_uri(json: text) -> text")).to_equal(true)
expect(src.contains("lsp_uri_to_path")).to_equal(true)
```

</details>

#### parses diagnostic entries from JSON array

- parses diagnostic entries from JSON array
   - Expected: src contains `fn _diag_parse_diagnostics(json: text, path: text) -> [EditorDiagnostic]`
   - Expected: src contains `fn _diag_parse_single(entry: text, path: text) -> EditorDiagnostic`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses diagnostic entries from JSON array")
val src = read_text("src/lib/editor/services/diagnostics.spl")
expect(src.contains("fn _diag_parse_diagnostics(json: text, path: text) -> [EditorDiagnostic]")).to_equal(true)
expect(src.contains("fn _diag_parse_single(entry: text, path: text) -> EditorDiagnostic")).to_equal(true)
```

</details>

#### maps LSP severity codes to editor severities

- maps LSP severity codes to editor severities
   - Expected: src contains `fn _diag_severity_from_lsp(code: i64) -> text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps LSP severity codes to editor severities")
val src = read_text("src/lib/editor/services/diagnostics.spl")
expect(src.contains("fn _diag_severity_from_lsp(code: i64) -> text")).to_equal(true)
```

</details>

### completion — LSP completion response wiring

#### has completion_handle_response

- has completion_handle_response
   - Expected: src contains `fn completion_handle_response(state: CompletionState, result_json: text, pref... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has completion_handle_response")
val src = read_text("src/lib/editor/services/completion.spl")
expect(src.contains("fn completion_handle_response(state: CompletionState, result_json: text, prefix: text)")).to_equal(true)
```

</details>

#### parses completion items from JSON

- parses completion items from JSON
   - Expected: src contains `fn _completion_parse_items(json: text) -> [CompletionItem]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses completion items from JSON")
val src = read_text("src/lib/editor/services/completion.spl")
expect(src.contains("fn _completion_parse_items(json: text) -> [CompletionItem]")).to_equal(true)
```

</details>

#### maps LSP completion kind codes to names

- maps LSP completion kind codes to names
   - Expected: src contains `fn _completion_kind_name(code: i64) -> text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps LSP completion kind codes to names")
val src = read_text("src/lib/editor/services/completion.spl")
expect(src.contains("fn _completion_kind_name(code: i64) -> text")).to_equal(true)
```

</details>

#### parses LSP result items

- parses LSP result items
   - Expected: items.len() equals `2`
   - Expected: items[0].label equals `print`
   - Expected: items[0].insert_text equals `print()`
   - Expected: items[0].kind equals `function`
   - Expected: items[1].insert_text equals `val`
   - Expected: items[1].kind equals `keyword`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses LSP result items")
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

- has stdio_transport_new factory
   - Expected: src contains `fn stdio_transport_new(config: LspTransportConfig) -> StdioTransport`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has stdio_transport_new factory")
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("fn stdio_transport_new(config: LspTransportConfig) -> StdioTransport")).to_equal(true)
```

</details>

#### has start and stop

- has start and stop
   - Expected: src contains `fn stdio_transport_start(transport: StdioTransport) -> bool`
   - Expected: src contains `fn stdio_transport_stop(transport: StdioTransport)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has start and stop")
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("fn stdio_transport_start(transport: StdioTransport) -> bool")).to_equal(true)
expect(src.contains("fn stdio_transport_stop(transport: StdioTransport)")).to_equal(true)
```

</details>

#### has send and receive

- has send and receive
   - Expected: src contains `fn stdio_transport_send(transport: StdioTransport, json: text) -> bool`
   - Expected: src contains `fn stdio_transport_receive(transport: StdioTransport) -> text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has send and receive")
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("fn stdio_transport_send(transport: StdioTransport, json: text) -> bool")).to_equal(true)
expect(src.contains("fn stdio_transport_receive(transport: StdioTransport) -> text")).to_equal(true)
```

</details>

#### has inject_response for testing

- has inject_response for testing
   - Expected: src contains `fn stdio_transport_inject_response(transport: StdioTransport, json: text)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has inject_response for testing")
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("fn stdio_transport_inject_response(transport: StdioTransport, json: text)")).to_equal(true)
```

</details>

### LSP transport — process-backed StdioProcessTransport

#### declares rt_process_spawn_piped extern

- declares rt_process_spawn_piped extern
   - Expected: src contains `extern fn rt_process_spawn_piped(cmd: text, args: [text]) -> i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("declares rt_process_spawn_piped extern")
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("extern fn rt_process_spawn_piped(cmd: text, args: [text]) -> i64")).to_equal(true)
```

</details>

#### declares rt_process_write_stdin extern

- declares rt_process_write_stdin extern
   - Expected: src contains `extern fn rt_process_write_stdin(pid: i64, data: text) -> bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("declares rt_process_write_stdin extern")
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("extern fn rt_process_write_stdin(pid: i64, data: text) -> bool")).to_equal(true)
```

</details>

#### declares rt_process_read_stdout extern

- declares rt_process_read_stdout extern
   - Expected: src contains `extern fn rt_process_read_stdout(pid: i64) -> text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("declares rt_process_read_stdout extern")
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("extern fn rt_process_read_stdout(pid: i64) -> text")).to_equal(true)
```

</details>

#### declares rt_process_is_alive extern

- declares rt_process_is_alive extern
   - Expected: src contains `extern fn rt_process_is_alive(pid: i64) -> bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("declares rt_process_is_alive extern")
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("extern fn rt_process_is_alive(pid: i64) -> bool")).to_equal(true)
```

</details>

#### declares rt_process_kill extern

- declares rt_process_kill extern
   - Expected: src contains `extern fn rt_process_kill(pid: i64) -> bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("declares rt_process_kill extern")
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("extern fn rt_process_kill(pid: i64) -> bool")).to_equal(true)
```

</details>

#### defines StdioProcessTransport class with pid field

- defines StdioProcessTransport class with pid field
   - Expected: src contains `class StdioProcessTransport:`
   - Expected: src contains `pid: i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines StdioProcessTransport class with pid field")
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("class StdioProcessTransport:")).to_equal(true)
expect(src.contains("pid: i64")).to_equal(true)
```

</details>

#### defines StdioProcessTransport class with server_cmd and server_args fields

- defines StdioProcessTransport class with server_cmd and server_args fields
   - Expected: src contains `server_cmd: text`
   - Expected: src contains `server_args: [text]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines StdioProcessTransport class with server_cmd and server_args fields")
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("server_cmd: text")).to_equal(true)
expect(src.contains("server_args: [text]")).to_equal(true)
```

</details>

#### defines StdioProcessTransport class with buffer field

- defines StdioProcessTransport class with buffer field
   - Expected: src contains `buffer: text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines StdioProcessTransport class with buffer field")
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("buffer: text")).to_equal(true)
```

</details>

#### has static new constructor that spawns process

- has static new constructor that spawns process
   - Expected: src contains `static fn new(cmd: text, args: [text]) -> StdioProcessTransport`
   - Expected: src contains `rt_process_spawn_piped`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has static new constructor that spawns process")
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("static fn new(cmd: text, args: [text]) -> StdioProcessTransport")).to_equal(true)
expect(src.contains("rt_process_spawn_piped")).to_equal(true)
```

</details>

#### has send method writing framed message to stdin

- has send method writing framed message to stdin
   - Expected: src contains `me send(message: text) -> bool`
   - Expected: src contains `rt_process_write_stdin`
   - Expected: src contains `lsp_frame_message`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has send method writing framed message to stdin")
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("me send(message: text) -> bool")).to_equal(true)
expect(src.contains("rt_process_write_stdin")).to_equal(true)
expect(src.contains("lsp_frame_message")).to_equal(true)
```

</details>

#### has receive method reading from stdout and parsing frame

- has receive method reading from stdout and parsing frame
   - Expected: src contains `me receive() -> text`
   - Expected: src contains `rt_process_read_stdout`
   - Expected: src contains `lsp_parse_frame`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has receive method reading from stdout and parsing frame")
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("me receive() -> text")).to_equal(true)
expect(src.contains("rt_process_read_stdout")).to_equal(true)
expect(src.contains("lsp_parse_frame")).to_equal(true)
```

</details>

#### has is_connected method checking process liveness

- has is_connected method checking process liveness
   - Expected: src contains `fn is_connected() -> bool`
   - Expected: src contains `rt_process_is_alive`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has is_connected method checking process liveness")
val src = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("fn is_connected() -> bool")).to_equal(true)
expect(src.contains("rt_process_is_alive")).to_equal(true)
```

</details>

#### has close method killing process

- has close method killing process
   - Expected: src contains `me close()`
   - Expected: src contains `rt_process_kill`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has close method killing process")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering LSP transport — Content-Length framing, LSP transport — message building, LSP transport — URI handling, LSP transport — response parsing, LSP client — transport wiring, diagnostics — LSP publishDiagnostics wiring, completion — LSP completion response wiring, LSP transport — stdio operations, LSP transport — process-backed StdioProcessTransport.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0c651f6178c7e7a6354fa7dd351fa234c95d35627c89912d5ab2d44443f64c8b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0c651f6178c7e7a6354fa7dd351fa234c95d35627c89912d5ab2d44443f64c8b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0c651f6178c7e7a6354fa7dd351fa234c95d35627c89912d5ab2d44443f64c8b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/gui/editor_lsp_transport_spec.spl
mirror: doc/06_spec/03_system/gui/editor_lsp_transport_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/editor_lsp_transport_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/editor_lsp_transport_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/editor_lsp_transport_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/gui/editor_lsp_transport_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines LspTransportConfig struct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/editor_lsp_transport_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines StdioTransport struct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/editor_lsp_transport_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has lsp_frame_message for Content-Length framing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
