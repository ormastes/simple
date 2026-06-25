# MCP Protocol Runtime

> Tests the wire-level MCP protocol handling for the active simple-mcp server wrapper. Verifies JSON-RPC framing, request/response correlation, error codes, and protocol negotiation at the transport layer.

<!-- sdn-diagram:id=mcp_protocol_runtime_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_protocol_runtime_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_protocol_runtime_spec -> std
mcp_protocol_runtime_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_protocol_runtime_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP Protocol Runtime

Tests the wire-level MCP protocol handling for the active simple-mcp server wrapper. Verifies JSON-RPC framing, request/response correlation, error codes, and protocol negotiation at the transport layer.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | In Progress |
| Source | `test/03_system/feature/app/mcp_protocol_runtime_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the wire-level MCP protocol handling for the active simple-mcp server
wrapper. Verifies JSON-RPC framing, request/response correlation, error codes,
and protocol negotiation at the transport layer.

## Scenarios

### MCP Protocol Runtime

<details>
<summary>Advanced: supports protocol/runtime matrix in one session</summary>

#### supports protocol/runtime matrix in one session

<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req1 = generic_request("2", "resources/templates/list", "{}")
val req2 = generic_request("3", "resources/read", "{\"uri\":\"project:///info\"}")
val req3 = generic_request("4", "resources/read", "{\"uri\":\"bugdb:///stats\"}")
val req4 = generic_request("5", "prompts/get", "{\"name\":\"analyze-file\",\"arguments\":{\"path\":\"src/app/mcp/main_lazy.spl\"}}")
val req5 = generic_request("6", "completion/complete", "{\"ref\":{\"type\":\"ref/prompt\",\"name\":\"analyze-file\"},\"argument\":{\"name\":\"path\",\"value\":\"src\"}}")
val req6 = generic_request("7", "logging/setLevel", "{\"level\":\"debug\"}")
val req7 = generic_request("8", "roots/list", "{}")
val req8 = generic_request("9", "tools/call", "{\"name\":\"no_such_tool\",\"arguments\":{}}")
val req9 = generic_request("10", "tools/list", "{}")
val req10 = generic_request("11", "tools/call", "{\"name\":\"debug_log_status\",\"arguments\":{}}")
val input = init_request("abc-1") + initialized_notification() + req1 + req2 + req3 + req4 + req5 + req6 + req7 + req8 + req9 + req10 + shutdown_request("12")
val output = send_mcp(input)
expect(output.contains("\"id\":\"abc-1\"")).to_equal(true)
expect(output.contains("\"capabilities\"")).to_equal(true)
expect(output.contains("resourceTemplates")).to_equal(true)
expect(output.contains("project:///info")).to_equal(true)
expect(output.contains("Working Dir")).to_equal(true)
expect(output.contains("bugdb:///stats")).to_equal(true)
expect(output.contains("\"health\"")).to_equal(true)
expect(output.contains("\"description\":\"Analyze file\"")).to_equal(true)
expect(output.contains("\"messages\"")).to_equal(true)
expect(output.contains("\"completion\"")).to_equal(true)
expect(output.contains("\"values\":[")).to_equal(true)
expect(output.contains("src/")).to_equal(true)
expect(output.contains("\"level\":\"debug\"")).to_equal(true)
expect(output.contains("\"roots\":[")).to_equal(true)
expect(output.contains("\"uri\":\"file://")).to_equal(true)
expect(output.contains("\"isError\":true")).to_equal(true)
expect(output.contains("Unknown tool")).to_equal(true)
expect(output.contains("\"error\":")).to_equal(false)
expect(output.contains("\"name\":\"simple_read\"")).to_equal(true)
expect(output.contains("\"name\":\"debug_set_data_breakpoint\"")).to_equal(true)
expect(output.contains("\"required\":[\"path\"]")).to_equal(true)
expect(output.contains("\"annotations\"")).to_equal(true)
expect(output.contains("\"structuredContent\"")).to_equal(true)
expect(output.contains("\"inferredType\":\"object\"")).to_equal(true)
expect(output.contains("\"shape\":\"object")).to_equal(true)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
