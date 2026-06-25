# Mcp Stdio Integration Specification

> 1. Operator sends a Content-Length framed initialize request

<!-- sdn-diagram:id=mcp_stdio_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_stdio_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_stdio_integration_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_stdio_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Stdio Integration Specification

## Scenarios

### MCP Protocol Runtime

#### survives initialize followed by tools/list on the same server process

1. Operator sends a Content-Length framed initialize request
   - Protocol capture: after_step
   - Evidence: protocol response verified by 3 expected checks
   - Expected: output contains `"protocolVersion":"2025-06-18"`
   - Expected: output contains `"serverInfo":{"name":"simple-mcp-full"`
   - Expected: output does not contain `"error":`

2. Operator sends the initialized notification and lists tools
   - Protocol capture: after_step
   - Evidence: protocol response verified by 7 expected checks
   - Expected: exec_evidence.body contains `input: initialize, initialized, tools/list`
   - Expected: protocol_evidence.body contains `params: jsonrpc=2.0; method=tools/list; id=2`
   - Expected: protocol_evidence.body contains `response fields: protocolVersion=2025-06-18; result.tools=present; error=absent`
   - Expected: output contains `"protocolVersion":"2025-06-18"`
   - Expected: output contains `"result":{"tools":[`
   - Expected: output contains `"name":"debug_create_session"`
   - Expected: output does not contain `"error":`


<details>
<summary>Executable SPipe</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = init_request("1")
val output = send_mcp(input)
expect(output.contains("\"protocolVersion\":\"2025-06-18\"")).to_equal(true)
expect(output.contains("\"serverInfo\":{\"name\":\"simple-mcp-full\"")).to_equal(true)
expect(output.contains("\"error\":")).to_equal(false)

val init = "{\"jsonrpc\":\"2.0\",\"id\":\"1\",\"method\":\"initialize\",\"params\":{\"protocolVersion\":\"2025-06-18\",\"capabilities\":{},\"clientInfo\":{\"name\":\"spec\",\"version\":\"1.0\"}}}"
val req = "{\"jsonrpc\":\"2.0\",\"id\":\"2\",\"method\":\"tools/list\",\"params\":{}}"
val input = mcp_jsonl(init) + mcp_jsonl("{\"jsonrpc\":\"2.0\",\"method\":\"initialized\",\"params\":{}}") + mcp_jsonl(req)
val output = send_mcp(input)
val exec_evidence = capture_exec_detailed(
    "MCP stdio tools/list execution",
    "bin/simple_mcp_server",
    "stdio JSON-RPC over stdin",
    "initialize, initialized, tools/list",
    "initialize result and tools/list result",
    "stderr redirected during protocol smoke",
    0
)
val protocol_evidence = capture_api_protocol_fields(
    "MCP tools/list protocol exchange",
    "JSON-RPC",
    "stdio:tools/list",
    ["jsonrpc", "method", "id"],
    ["2.0", "tools/list", "2"],
    ["transport"],
    ["stdio"],
    ["protocolVersion", "result.tools", "error"],
    ["2025-06-18", "present", "absent"]
)
expect(exec_evidence.body.contains("input: initialize, initialized, tools/list")).to_equal(true)
expect(protocol_evidence.body.contains("params: jsonrpc=2.0; method=tools/list; id=2")).to_equal(true)
expect(protocol_evidence.body.contains("response fields: protocolVersion=2025-06-18; result.tools=present; error=absent")).to_equal(true)
expect(output.contains("\"protocolVersion\":\"2025-06-18\"")).to_equal(true)
expect(output.contains("\"result\":{\"tools\":[")).to_equal(true)
expect(output.contains("\"name\":\"debug_create_session\"")).to_equal(true)
expect(output.contains("\"error\":")).to_equal(false)
```

</details>

#### returns tool-level isError for unknown tool

1. Operator sends a Content-Length framed initialize request
   - Protocol capture: after_step
   - Evidence: protocol response verified by 3 expected checks
   - Expected: output contains `"protocolVersion":"2025-06-18"`
   - Expected: output contains `"serverInfo":{"name":"simple-mcp-full"`
   - Expected: output does not contain `"error":`

2. Operator calls an unknown tool to verify tool-level errors
   - Protocol capture: after_step
   - Evidence: protocol response verified by 3 expected checks
   - Expected: output contains `"isError":true`
   - Expected: output contains `Unknown tool`
   - Expected: output does not contain `"error":`


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = init_request("1")
val output = send_mcp(input)
expect(output.contains("\"protocolVersion\":\"2025-06-18\"")).to_equal(true)
expect(output.contains("\"serverInfo\":{\"name\":\"simple-mcp-full\"")).to_equal(true)
expect(output.contains("\"error\":")).to_equal(false)

val init = "{\"jsonrpc\":\"2.0\",\"id\":\"1\",\"method\":\"initialize\",\"params\":{\"protocolVersion\":\"2025-06-18\",\"capabilities\":{},\"clientInfo\":{\"name\":\"spec\",\"version\":\"1.0\"}}}"
val req = "{\"jsonrpc\":\"2.0\",\"id\":\"2\",\"method\":\"tools/call\",\"params\":{\"name\":\"no_such_tool\",\"arguments\":{}}}"
val input = mcp_jsonl(init) + mcp_jsonl("{\"jsonrpc\":\"2.0\",\"method\":\"initialized\",\"params\":{}}") + mcp_jsonl(req)
val output = send_mcp(input)
expect(output.contains("\"isError\":true")).to_equal(true)
expect(output.contains("Unknown tool")).to_equal(true)
expect(output.contains("\"error\":")).to_equal(false)
```

</details>

#### advertises and dispatches the safe shared editor MCP subset

1. Operator sends the initialized notification and lists tools
   - Protocol capture: after_step
   - Evidence: protocol response verified by 7 expected checks
   - Expected: exec_evidence.body contains `input: initialize, initialized, tools/list`
   - Expected: protocol_evidence.body contains `params: jsonrpc=2.0; method=tools/list; id=2`
   - Expected: protocol_evidence.body contains `response fields: protocolVersion=2025-06-18; result.tools=present; error=absent`
   - Expected: output contains `"protocolVersion":"2025-06-18"`
   - Expected: output contains `"result":{"tools":[`
   - Expected: output contains `"name":"debug_create_session"`
   - Expected: output does not contain `"error":`

2. Operator prepares an editor note
   - API capture: after_step
   - Evidence: API response verified by 1 expected check
   - Expected: rt_file_write_text(path, "# MCP Note\n\nhello editor\n") is true

3. Operator opens and reads the note through the safe editor tools
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
<summary>Executable SPipe</summary>

Runnable source: 51 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val init = "{\"jsonrpc\":\"2.0\",\"id\":\"1\",\"method\":\"initialize\",\"params\":{\"protocolVersion\":\"2025-06-18\",\"capabilities\":{},\"clientInfo\":{\"name\":\"spec\",\"version\":\"1.0\"}}}"
val req = "{\"jsonrpc\":\"2.0\",\"id\":\"2\",\"method\":\"tools/list\",\"params\":{}}"
val input = mcp_jsonl(init) + mcp_jsonl("{\"jsonrpc\":\"2.0\",\"method\":\"initialized\",\"params\":{}}") + mcp_jsonl(req)
val output = send_mcp(input)
val exec_evidence = capture_exec_detailed(
    "MCP stdio tools/list execution",
    "bin/simple_mcp_server",
    "stdio JSON-RPC over stdin",
    "initialize, initialized, tools/list",
    "initialize result and tools/list result",
    "stderr redirected during protocol smoke",
    0
)
val protocol_evidence = capture_api_protocol_fields(
    "MCP tools/list protocol exchange",
    "JSON-RPC",
    "stdio:tools/list",
    ["jsonrpc", "method", "id"],
    ["2.0", "tools/list", "2"],
    ["transport"],
    ["stdio"],
    ["protocolVersion", "result.tools", "error"],
    ["2025-06-18", "present", "absent"]
)
expect(exec_evidence.body.contains("input: initialize, initialized, tools/list")).to_equal(true)
expect(protocol_evidence.body.contains("params: jsonrpc=2.0; method=tools/list; id=2")).to_equal(true)
expect(protocol_evidence.body.contains("response fields: protocolVersion=2025-06-18; result.tools=present; error=absent")).to_equal(true)
expect(output.contains("\"protocolVersion\":\"2025-06-18\"")).to_equal(true)
expect(output.contains("\"result\":{\"tools\":[")).to_equal(true)
expect(output.contains("\"name\":\"debug_create_session\"")).to_equal(true)
expect(output.contains("\"error\":")).to_equal(false)

val path = "/tmp/simple_mcp_editor_note.md"
expect(rt_file_write_text(path, "# MCP Note\n\nhello editor\n")).to_equal(true)
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

#### reads editor MCP arguments only from params.arguments

1. Operator prepares an editor note
   - API capture: after_step
   - Evidence: API response verified by 1 expected check
   - Expected: rt_file_write_text(path, "# MCP Note\n\nhello editor\n") is true

2. Operator opens and reads the note through the safe editor tools
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

3. Operator prepares a scoped-argument editor note
   - API capture: after_step
   - Evidence: API response verified by 1 expected check
   - Expected: rt_file_write_text(path, "# Scoped Argument\n\nfrom arguments\n") is true

4. Operator verifies editor.open_file reads params.arguments.path
   - API capture: after_step
   - Evidence: API response verified by 4 expected checks
   - Expected: output contains `"opened " + path`
   - Expected: output contains `from arguments`
   - Expected: output does not contain `wrong_top_level`
   - Expected: output does not contain `"error":`


<details>
<summary>Executable SPipe</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/simple_mcp_editor_note.md"
expect(rt_file_write_text(path, "# MCP Note\n\nhello editor\n")).to_equal(true)
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
expect(rt_file_write_text(path, "# Scoped Argument\n\nfrom arguments\n")).to_equal(true)
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
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
