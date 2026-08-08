# MCP Server

> Tests the MCP server implementation including tool registration, request dispatch, and response formatting. Verifies that the server correctly handles initialize, tools/list, and tools/call methods per the MCP specification.

<!-- sdn-diagram:id=server_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=server_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

server_spec -> std
server_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=server_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP Server

Tests the MCP server implementation including tool registration, request dispatch, and response formatting. Verifies that the server correctly handles initialize, tools/list, and tools/call methods per the MCP specification.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | In Progress |
| Source | `test/03_system/feature/app/mcp/server_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the MCP server implementation including tool registration, request dispatch,
and response formatting. Verifies that the server correctly handles initialize,
tools/list, and tools/call methods per the MCP specification.

## Scenarios

### MCP Server

#### responds to initialize message with protocolVersion

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires compiled MCP server binary":
    val base_dir = cwd()
    val mcp_server = base_dir + "/bin/simple_mcp_server_optimized"
    val init_msg = "{\"jsonrpc\":\"2.0\",\"method\":\"initialize\",\"params\":{\"protocolVersion\":\"2025-06-18\",\"capabilities\":{}},\"id\":1}"
    val init_cmd = "(echo 'Content-Length: " + init_msg.len().to_text() + "'; echo ''; echo '" + init_msg + "'; sleep 0.5) | timeout 2 " + mcp_server + " server 2>/dev/null"
    val init_result = shell(init_cmd)
    expect(contains(init_result.stdout, "protocolVersion")).to_equal(true)
```

</details>

#### responds to tools/list with tool names

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires compiled MCP server binary":
    val base_dir = cwd()
    val mcp_server = base_dir + "/bin/simple_mcp_server_optimized"
    val init_msg = "{\"jsonrpc\":\"2.0\",\"method\":\"initialize\",\"params\":{\"protocolVersion\":\"2025-06-18\",\"capabilities\":{}},\"id\":1}"
    val tools_msg = "{\"jsonrpc\":\"2.0\",\"method\":\"tools/list\",\"id\":2}"
    val tools_cmd = "(echo 'Content-Length: " + init_msg.len().to_text() + "'; echo ''; echo '" + init_msg + "'; echo 'Content-Length: " + tools_msg.len().to_text() + "'; echo ''; echo '" + tools_msg + "'; sleep 0.5) | timeout 2 " + mcp_server + " server 2>/dev/null"
    val tools_result = shell(tools_cmd)
    expect(contains(tools_result.stdout, "tools")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
