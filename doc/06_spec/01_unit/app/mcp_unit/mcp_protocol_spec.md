# Mcp Protocol Specification

> <details>

<!-- sdn-diagram:id=mcp_protocol_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_protocol_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_protocol_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_protocol_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Protocol Specification

## Scenarios

### MCP JSON-RPC 2.0 Protocol

#### when handling initialize request

#### builds response with protocol version

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val proto = "2025-06-18"
val result = jo1(jp("protocolVersion", js(proto)))
val response = make_result_response("1", result)
expect(response.contains("protocolVersion")).to_equal(true)
expect(response.contains("2025-06-18")).to_equal(true)
```

</details>

#### builds response with server information

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server_info = jo2(jp("name", js("simple-mcp")), jp("version", js("2.0.0")))
expect(server_info.contains("simple-mcp")).to_equal(true)
expect(server_info.contains("2.0.0")).to_equal(true)
```

</details>

#### when handling tools/list request

#### builds tool list response

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool = jo2(jp("name", js("read_code")), jp("description", js("Read file")))
val tools = "[" + tool + "]"
val result = jo1(jp("tools", tools))
expect(result.contains("read_code")).to_equal(true)
```

</details>

#### when handling errors

#### builds method not found error

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_error_response("1", -32601, "Method not found")
expect(response.contains("-32601")).to_equal(true)
expect(response.contains("Method not found")).to_equal(true)
```

</details>

#### builds invalid params error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_error_response("1", -32602, "Invalid params")
expect(response.contains("-32602")).to_equal(true)
```

</details>

### MCP Message Format

#### when formatting responses

#### builds valid JSON response

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_result_response("1", LB() + RB())
expect(response.starts_with(LB())).to_equal(true)
expect(response.ends_with(RB())).to_equal(true)
```

</details>

#### includes jsonrpc version in result response

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_result_response("1", "null")
expect(response.contains("\"jsonrpc\":\"2.0\"")).to_equal(true)
```

</details>

#### includes jsonrpc version in error response

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_error_response("1", -32600, "Bad request")
expect(response.contains("\"jsonrpc\":\"2.0\"")).to_equal(true)
```

</details>

### MCP Capability Negotiation

#### when server declares capabilities

#### builds capabilities JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tools_cap = jo1("")
val resources_cap = jo1("")
val prompts_cap = jo1("")
val caps = jo3(jp("tools", tools_cap), jp("resources", resources_cap), jp("prompts", prompts_cap))
expect(caps.contains("\"tools\"")).to_equal(true)
expect(caps.contains("\"resources\"")).to_equal(true)
expect(caps.contains("\"prompts\"")).to_equal(true)
```

</details>

### MCP Request ID Handling

#### when request has string ID

#### preserves string ID in response

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_result_response("\"test-123\"", "null")
expect(response.contains("\"id\":\"test-123\"")).to_equal(true)
```

</details>

#### when request has numeric ID

#### preserves numeric ID in response

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_result_response("42", "null")
expect(response.contains("\"id\":42")).to_equal(true)
```

</details>

### MCP Method Routing

#### when extracting method from request

#### extracts method field

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = jo2(jp("method", js("initialize")), jp("id", "1"))
val method = extract_json_string(req, "method")
expect(method).to_equal("initialize")
```

</details>

#### extracts tools/list method

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = jo2(jp("method", js("tools/list")), jp("id", "2"))
val method = extract_json_string(req, "method")
expect(method).to_equal("tools/list")
```

</details>

#### extracts tools/call method

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = jo2(jp("method", js("tools/call")), jp("id", "3"))
val method = extract_json_string(req, "method")
expect(method).to_equal("tools/call")
```

</details>

### Log Level Utilities

<details>
<summary>Advanced: maps debug to 0</summary>

#### maps debug to 0 _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("debug")).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: maps info to 1</summary>

#### maps info to 1 _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("info")).to_equal(1)
```

</details>


</details>

<details>
<summary>Advanced: maps warning to 3</summary>

#### maps warning to 3 _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("warning")).to_equal(3)
```

</details>


</details>

<details>
<summary>Advanced: maps error to 4</summary>

#### maps error to 4 _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("error")).to_equal(4)
```

</details>


</details>

<details>
<summary>Advanced: maps critical to 5</summary>

#### maps critical to 5 _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("critical")).to_equal(5)
```

</details>


</details>

<details>
<summary>Advanced: returns -1 for unknown level</summary>

#### returns -1 for unknown level _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("unknown")).to_equal(-1)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/mcp_protocol_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MCP JSON-RPC 2.0 Protocol
- MCP Message Format
- MCP Capability Negotiation
- MCP Request ID Handling
- MCP Method Routing
- Log Level Utilities

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 6 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
