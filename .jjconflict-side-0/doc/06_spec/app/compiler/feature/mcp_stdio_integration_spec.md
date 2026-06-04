# MCP Stdio Integration

**Feature ID:** #MCP-STDIO-INTEGRATION-001 | **Category:** Integration | **Status:** Active

_Source: `test/02_integration/app/mcp_stdio_integration_spec.spl`_

---

## Overview

Scenario manual for the stdio MCP server. It shows the operator path for
initializing the server, listing tools, checking tool-level failures, and using
the safe shared editor tool subset.

## Test Summary

| Metric | Count |
|--------|-------|
| Primary scenarios | 3 |
| Inline setup scenarios | 1 |
| Folded detail scenarios | 1 |

## Test Structure

### MCP Protocol Runtime

#### Operator lists MCP tools after initialization

1. Operator sends a Content-Length framed `initialize` request.

   Capture: `protocol`, after step.

   Expected result:
   - response includes protocol version `2025-06-18`
   - response includes server name `simple-mcp-full`
   - response has no top-level JSON-RPC error

2. Operator sends the `initialized` notification and a `tools/list` request on
   the same server process.

   Capture: `protocol`, after step.

   Expected result:
   - response contains a tools array
   - response advertises `debug_create_session`
   - response has no top-level JSON-RPC error

#### Operator sees tool-level error for an unknown tool

1. Operator sends a Content-Length framed `initialize` request.

   Capture: `protocol`, after step.

2. Operator calls `tools/call` with tool name `no_such_tool`.

   Capture: `protocol`, after step.

   Expected result:
   - response sets `isError` to `true`
   - response text includes `Unknown tool`
   - response has no top-level JSON-RPC error

#### Operator opens and reads a file through the safe editor subset

1. Operator initializes the server and lists MCP tools.

   Capture: `protocol`, after step.

2. Operator calls `editor.open_file`, `editor.read_buffer`, and
   `editor.list_open_files`.

   Capture: `api`, after step.

   Expected result:
   - advertised tools include `editor.open_file`, `editor.read_buffer`, and
     `editor.list_open_files`
   - unsafe editor tools are not advertised
   - response contains the opened path and file content
   - response has no top-level JSON-RPC error

<details>
<summary>Folded detail: editor arguments are read only from params.arguments</summary>

This regression keeps the manual reproducible without promoting scoped argument
plumbing to the primary operator flow. The server receives a wrong top-level
`path` and the correct `params.arguments.path`; the response must open and read
only the argument-scoped path.

</details>
