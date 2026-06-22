# MCP Library Integration

> Tests end-to-end MCP library integration including server startup, tool listing, and tool execution through the full protocol stack. Verifies that all MCP library components work together correctly for complete request-response cycles.

<!-- sdn-diagram:id=integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

integration_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP Library Integration

Tests end-to-end MCP library integration including server startup, tool listing, and tool execution through the full protocol stack. Verifies that all MCP library components work together correctly for complete request-response cycles.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | In Progress |
| Source | `test/03_system/feature/lib/mcp/integration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests end-to-end MCP library integration including server startup, tool listing,
and tool execution through the full protocol stack. Verifies that all MCP library
components work together correctly for complete request-response cycles.

## Scenarios

### MCP Library - Integration

#### builds complete MCP initialize response

1. jp
2. jp
3. jp


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val init_result = """{"protocolVersion":"2025-06-18","capabilities":{"tools":{}}}"""
val response = jo3(
    jp("jsonrpc", js("2.0")),
    jp("id", "1"),
    jp("result", init_result)
)
expect(response).to_contain("\"jsonrpc\":\"2.0\"")
expect(response).to_contain("\"id\":1")
expect(response).to_contain("protocolVersion")
```

</details>

#### builds tools/list response with pre-computed schemas

1. init core schemas


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
init_core_schemas()
val tools = get_all_tool_schemas()
expect(tools).to_start_with("[")
expect(tools).to_contain("read_code")
```

</details>

#### extracts method from JSON-RPC request

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val request = """{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"""
val method = extract_json_string_v2(request, "method")
expect(method).to_equal("initialize")
```

</details>

#### creates error response

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error = make_error_response("42", -32600, "Invalid request")
expect(error).to_contain("\"id\":42")
expect(error).to_contain("\"error\"")
expect(error).to_contain("-32600")
expect(error).to_contain("Invalid request")
```

</details>

#### manages session lifecycle

1. var state = create mcp state
   - Expected: state.initialized is false
   - Expected: state.initialized is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = create_mcp_state()
expect(state.initialized).to_equal(false)

state.initialized = true
expect(state.initialized).to_equal(true)
```

</details>

#### registers and finds tool handlers

1. register tool handler
   - Expected: found.name equals `test_tool`
   - Expected: found.handler_module equals `app.handlers.test`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handler = create_tool_handler(
    "test_tool",
    "Test tool",
    """{"name":"test_tool"}""",
    "app.handlers.test",
    "handle_test"
)
register_tool_handler(handler)

val found = find_tool_handler("test_tool")
expect(found.name).to_equal("test_tool")
expect(found.handler_module).to_equal("app.handlers.test")
```

</details>

#### handles full request-response cycle

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Simulate receiving a request
val request = """{"jsonrpc":"2.0","id":3,"method":"tools/call","params":{"name":"read_code","arguments":{"path":"test.spl"}}}"""

# Extract components
val method = extract_json_string_v2(request, "method")
expect(method).to_equal("tools/call")

# Extract argument
val path = extract_arg(request, "path")
expect(path).to_equal("test.spl")

# Build tool result response
val tool_result = make_tool_result("3", "File content here")
expect(tool_result).to_contain("\"id\":3")
expect(tool_result).to_contain("\"result\"")
expect(tool_result).to_contain("File content here")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
