# Mcp Stdio Integration Specification

## Scenarios

### MCP Protocol Runtime

#### survives initialize followed by tools/list on the same server process _(slow)_

- Operator sends a Content-Length framed initialize request
   - Protocol capture: after_step
   - Evidence: protocol response verified by 3 expected checks
   - Expected: output contains `"protocolVersion":"2025-06-18"`
   - Expected: output contains `"serverInfo":{"name":"simple-mcp-full"`
   - Expected: output does not contain `"error":`
- Operator sends the initialized notification and lists tools
   - Protocol capture: after_step
   - Evidence: protocol response verified by 10 expected checks
   - Expected: output_frames_valid is true
   - Expected: output does not contain `Content-Length: 2305843009213693951`
   - Expected: output contains `"protocolVersion":"2025-06-18"`
   - Expected: output contains `"tools":`
   - Expected: output contains `"inputSchema":`
   - Expected: jsonl_output contains `"protocolVersion":"2025-06-18"`
   - Expected: jsonl_output contains `"tools":`
   - Expected: jsonl_output contains `"inputSchema":`
   - Expected: jsonl_output contains `"name":"debug_create_session"`
   - Expected: jsonl_output does not contain `"error":`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = init_request("1")
val output = send_mcp(input)
expect(output.contains("\"protocolVersion\":\"2025-06-18\"")).to_equal(true)
expect(output.contains("\"serverInfo\":{\"name\":\"simple-mcp-full\"")).to_equal(true)
expect(output.contains("\"error\":")).to_equal(false)

val init = "{\"jsonrpc\":\"2.0\",\"id\":\"1\",\"method\":\"initialize\",\"params\":{\"protocolVersion\":\"2025-06-18\",\"capabilities\":{},\"clientInfo\":{\"name\":\"spec\",\"version\":\"1.0\"}}}"
val initialized = "{\"jsonrpc\":\"2.0\",\"method\":\"notifications/initialized\",\"params\":{}}"
val req = "{\"jsonrpc\":\"2.0\",\"id\":\"2\",\"method\":\"tools/list\",\"params\":{}}"
val input = mcp_msg(init) + mcp_msg(initialized) + mcp_msg(req)
val output = send_mcp(input)
val output_frames_valid = has_valid_content_length_frames(output)
expect(output_frames_valid).to_equal(true)
expect(output.contains("Content-Length: 2305843009213693951")).to_equal(false)
expect(output.contains("\"protocolVersion\":\"2025-06-18\"")).to_equal(true)
expect(output.contains("\"tools\":")).to_equal(true)
expect(output.contains("\"inputSchema\":")).to_equal(true)

val jsonl_tools = mcp_jsonl(init) + mcp_jsonl("{\"jsonrpc\":\"2.0\",\"method\":\"initialized\",\"params\":{}}") + mcp_jsonl(req)
val jsonl_output = send_mcp(jsonl_tools)
expect(jsonl_output.contains("\"protocolVersion\":\"2025-06-18\"")).to_equal(true)
expect(jsonl_output.contains("\"tools\":")).to_equal(true)
expect(jsonl_output.contains("\"inputSchema\":")).to_equal(true)
expect(jsonl_output.contains("\"name\":\"debug_create_session\"")).to_equal(true)
expect(jsonl_output.contains("\"error\":")).to_equal(false)
```

</details>

#### returns tool-level isError for unknown tool _(slow)_

- Operator sends a Content-Length framed initialize request
   - Protocol capture: after_step
   - Evidence: protocol response verified by 3 expected checks
   - Expected: output contains `"protocolVersion":"2025-06-18"`
   - Expected: output contains `"serverInfo":{"name":"simple-mcp-full"`
   - Expected: output does not contain `"error":`
- Operator calls an unknown tool to verify tool-level errors
   - Protocol capture: after_step
   - Evidence: protocol response verified by 3 expected checks
   - Expected: unknown_output contains `"isError":true`
   - Expected: unknown_output contains `Unknown tool`
   - Expected: unknown_output does not contain `"error":`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = init_request("1")
val output = send_mcp(input)
expect(output.contains("\"protocolVersion\":\"2025-06-18\"")).to_equal(true)
expect(output.contains("\"serverInfo\":{\"name\":\"simple-mcp-full\"")).to_equal(true)
expect(output.contains("\"error\":")).to_equal(false)

val init = "{\"jsonrpc\":\"2.0\",\"id\":\"1\",\"method\":\"initialize\",\"params\":{\"protocolVersion\":\"2025-06-18\",\"capabilities\":{},\"clientInfo\":{\"name\":\"spec\",\"version\":\"1.0\"}}}"
val unknown_req = "{\"jsonrpc\":\"2.0\",\"id\":\"2\",\"method\":\"tools/call\",\"params\":{\"name\":\"no_such_tool\",\"arguments\":{}}}"
val unknown_input = mcp_jsonl(init) + mcp_jsonl("{\"jsonrpc\":\"2.0\",\"method\":\"initialized\",\"params\":{}}") + mcp_jsonl(unknown_req)
val unknown_output = send_mcp(unknown_input)
expect(unknown_output.contains("\"isError\":true")).to_equal(true)
expect(unknown_output.contains("Unknown tool")).to_equal(true)
expect(unknown_output.contains("\"error\":")).to_equal(false)
```

</details>

#### advertises and dispatches the safe shared editor MCP subset _(slow)_

- Operator sends the initialized notification and lists tools
   - API capture: after_step
   - Evidence: API response verified by 10 expected checks
   - Expected: output_frames_valid is true
   - Expected: output does not contain `Content-Length: 2305843009213693951`
   - Expected: output contains `"protocolVersion":"2025-06-18"`
   - Expected: output contains `"tools":`
   - Expected: output contains `"inputSchema":`
   - Expected: jsonl_output contains `"protocolVersion":"2025-06-18"`
   - Expected: jsonl_output contains `"tools":`
   - Expected: jsonl_output contains `"inputSchema":`
   - Expected: jsonl_output contains `"name":"debug_create_session"`
   - Expected: jsonl_output does not contain `"error":`
- Operator prepares an editor note
   - API capture: after_step
   - Evidence: API response verified by 1 expected check
   - Expected: file_write(path, "# MCP Note\n\nhello editor\n") is true
- Operator opens and reads the note through the safe editor tools
   - API capture: after_step
   - Evidence: API response verified by 10 expected checks
   - Expected: output contains `"name":"editor.open_file"`
   - Expected: output contains `"name":"editor.read_buffer"`
   - Expected: output contains `"name":"editor.list_open_files"`
   - Expected: output does not contain `"name":"editor.edit"`
   - Expected: output does not contain `"name":"editor.search"`
   - Expected: output does not contain `"name":"editor.diagnostics"`
   - Expected: output contains `"opened " + path`
   - Expected: output contains `hello editor`
   - Expected: output contains `path`
   - Expected: output does not contain `"error":`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val init = "{\"jsonrpc\":\"2.0\",\"id\":\"1\",\"method\":\"initialize\",\"params\":{\"protocolVersion\":\"2025-06-18\",\"capabilities\":{},\"clientInfo\":{\"name\":\"spec\",\"version\":\"1.0\"}}}"
val initialized = "{\"jsonrpc\":\"2.0\",\"method\":\"notifications/initialized\",\"params\":{}}"
val req = "{\"jsonrpc\":\"2.0\",\"id\":\"2\",\"method\":\"tools/list\",\"params\":{}}"
val input = mcp_msg(init) + mcp_msg(initialized) + mcp_msg(req)
val output = send_mcp(input)
val output_frames_valid = has_valid_content_length_frames(output)
expect(output_frames_valid).to_equal(true)
expect(output.contains("Content-Length: 2305843009213693951")).to_equal(false)
expect(output.contains("\"protocolVersion\":\"2025-06-18\"")).to_equal(true)
expect(output.contains("\"tools\":")).to_equal(true)
expect(output.contains("\"inputSchema\":")).to_equal(true)

val jsonl_tools = mcp_jsonl(init) + mcp_jsonl("{\"jsonrpc\":\"2.0\",\"method\":\"initialized\",\"params\":{}}") + mcp_jsonl(req)
val jsonl_output = send_mcp(jsonl_tools)
expect(jsonl_output.contains("\"protocolVersion\":\"2025-06-18\"")).to_equal(true)
expect(jsonl_output.contains("\"tools\":")).to_equal(true)
expect(jsonl_output.contains("\"inputSchema\":")).to_equal(true)
expect(jsonl_output.contains("\"name\":\"debug_create_session\"")).to_equal(true)
expect(jsonl_output.contains("\"error\":")).to_equal(false)

val path = "/tmp/simple_mcp_editor_note.md"
expect(file_write(path, "# MCP Note\n\nhello editor\n")).to_equal(true)

val init = "{\"jsonrpc\":\"2.0\",\"id\":\"1\",\"method\":\"initialize\",\"params\":{\"protocolVersion\":\"2025-06-18\",\"capabilities\":{},\"clientInfo\":{\"name\":\"spec\",\"version\":\"1.0\"}}}"
val list_req = "{\"jsonrpc\":\"2.0\",\"id\":\"2\",\"method\":\"tools/list\",\"params\":{}}"
val open_req = "{\"jsonrpc\":\"2.0\",\"id\":\"3\",\"method\":\"tools/call\",\"params\":{\"name\":\"editor.open_file\",\"arguments\":{\"path\":\"" + path + "\"}}}"
val read_req = "{\"jsonrpc\":\"2.0\",\"id\":\"4\",\"method\":\"tools/call\",\"params\":{\"name\":\"editor.read_buffer\",\"arguments\":{}}}"
val files_req = "{\"jsonrpc\":\"2.0\",\"id\":\"5\",\"method\":\"tools/call\",\"params\":{\"name\":\"editor.list_open_files\",\"arguments\":{}}}"
val input = mcp_jsonl(init) + mcp_jsonl("{\"jsonrpc\":\"2.0\",\"method\":\"initialized\",\"params\":{}}") + mcp_jsonl(list_req) + mcp_jsonl(open_req) + mcp_jsonl(read_req) + mcp_jsonl(files_req)
val output = send_mcp(input)
expect(output.contains("\"name\":\"editor.open_file\"")).to_equal(true)
expect(output.contains("\"name\":\"editor.read_buffer\"")).to_equal(true)
expect(output.contains("\"name\":\"editor.list_open_files\"")).to_equal(true)
expect(output.contains("\"name\":\"editor.edit\"")).to_equal(false)
expect(output.contains("\"name\":\"editor.search\"")).to_equal(false)
expect(output.contains("\"name\":\"editor.diagnostics\"")).to_equal(false)
expect(output.contains("opened " + path)).to_equal(true)
expect(output.contains("hello editor")).to_equal(true)
expect(output.contains(path)).to_equal(true)
expect(output.contains("\"error\":")).to_equal(false)
```

</details>

<details>
<summary>Advanced: reads editor MCP arguments only from params.arguments</summary>

#### reads editor MCP arguments only from params.arguments _(slow)_

- Operator prepares an editor note
   - API capture: after_step
   - Evidence: API response verified by 1 expected check
   - Expected: file_write(path, "# MCP Note\n\nhello editor\n") is true
- Operator opens and reads the note through the safe editor tools
   - API capture: after_step
   - Evidence: API response verified by 10 expected checks
   - Expected: output contains `"name":"editor.open_file"`
   - Expected: output contains `"name":"editor.read_buffer"`
   - Expected: output contains `"name":"editor.list_open_files"`
   - Expected: output does not contain `"name":"editor.edit"`
   - Expected: output does not contain `"name":"editor.search"`
   - Expected: output does not contain `"name":"editor.diagnostics"`
   - Expected: output contains `"opened " + path`
   - Expected: output contains `hello editor`
   - Expected: output contains `path`
   - Expected: output does not contain `"error":`
- Operator prepares a scoped-argument editor note
   - API capture: after_step
   - Evidence: API response verified by 1 expected check
   - Expected: file_write(path, "# Scoped Argument\n\nfrom arguments\n") is true
- Operator verifies editor.open_file reads params.arguments.path
   - API capture: after_step
   - Evidence: API response verified by 4 expected checks
   - Expected: output contains `"opened " + path`
   - Expected: output contains `from arguments`
   - Expected: output does not contain `wrong_top_level`
   - Expected: output does not contain `"error":`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/simple_mcp_editor_note.md"
expect(file_write(path, "# MCP Note\n\nhello editor\n")).to_equal(true)

val init = "{\"jsonrpc\":\"2.0\",\"id\":\"1\",\"method\":\"initialize\",\"params\":{\"protocolVersion\":\"2025-06-18\",\"capabilities\":{},\"clientInfo\":{\"name\":\"spec\",\"version\":\"1.0\"}}}"
val list_req = "{\"jsonrpc\":\"2.0\",\"id\":\"2\",\"method\":\"tools/list\",\"params\":{}}"
val open_req = "{\"jsonrpc\":\"2.0\",\"id\":\"3\",\"method\":\"tools/call\",\"params\":{\"name\":\"editor.open_file\",\"arguments\":{\"path\":\"" + path + "\"}}}"
val read_req = "{\"jsonrpc\":\"2.0\",\"id\":\"4\",\"method\":\"tools/call\",\"params\":{\"name\":\"editor.read_buffer\",\"arguments\":{}}}"
val files_req = "{\"jsonrpc\":\"2.0\",\"id\":\"5\",\"method\":\"tools/call\",\"params\":{\"name\":\"editor.list_open_files\",\"arguments\":{}}}"
val input = mcp_jsonl(init) + mcp_jsonl("{\"jsonrpc\":\"2.0\",\"method\":\"initialized\",\"params\":{}}") + mcp_jsonl(list_req) + mcp_jsonl(open_req) + mcp_jsonl(read_req) + mcp_jsonl(files_req)
val output = send_mcp(input)
expect(output.contains("\"name\":\"editor.open_file\"")).to_equal(true)
expect(output.contains("\"name\":\"editor.read_buffer\"")).to_equal(true)
expect(output.contains("\"name\":\"editor.list_open_files\"")).to_equal(true)
expect(output.contains("\"name\":\"editor.edit\"")).to_equal(false)
expect(output.contains("\"name\":\"editor.search\"")).to_equal(false)
expect(output.contains("\"name\":\"editor.diagnostics\"")).to_equal(false)
expect(output.contains("opened " + path)).to_equal(true)
expect(output.contains("hello editor")).to_equal(true)
expect(output.contains(path)).to_equal(true)
expect(output.contains("\"error\":")).to_equal(false)

val path = "/tmp/simple_mcp_editor_scoped_arg_note.md"
expect(file_write(path, "# Scoped Argument\n\nfrom arguments\n")).to_equal(true)

val init = "{\"jsonrpc\":\"2.0\",\"id\":\"1\",\"method\":\"initialize\",\"params\":{\"protocolVersion\":\"2025-06-18\",\"capabilities\":{},\"clientInfo\":{\"name\":\"spec\",\"version\":\"1.0\"}}}"
val open_req = "{\"jsonrpc\":\"2.0\",\"id\":\"2\",\"method\":\"tools/call\",\"params\":{\"name\":\"editor.open_file\",\"path\":\"/tmp/wrong_top_level.md\",\"arguments\":{\"path\":\"" + path + "\"}}}"
val read_req = "{\"jsonrpc\":\"2.0\",\"id\":\"3\",\"method\":\"tools/call\",\"params\":{\"name\":\"editor.read_buffer\",\"arguments\":{}}}"
val input = mcp_jsonl(init) + mcp_jsonl("{\"jsonrpc\":\"2.0\",\"method\":\"initialized\",\"params\":{}}") + mcp_jsonl(open_req) + mcp_jsonl(read_req)
val output = send_mcp(input)
expect(output.contains("opened " + path)).to_equal(true)
expect(output.contains("from arguments")).to_equal(true)
expect(output.contains("wrong_top_level")).to_equal(false)
expect(output.contains("\"error\":")).to_equal(false)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/mcp_stdio_integration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MCP Protocol Runtime

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 5 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

