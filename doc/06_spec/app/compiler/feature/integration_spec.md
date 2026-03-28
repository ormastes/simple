# MCP Library Integration Tests

**Feature ID:** #MCP-LIB-004 | **Category:** Standard Library | **Status:** Active

_Source: `test/feature/lib/mcp/integration_spec.spl`_

---

## Overview

End-to-end integration tests for the MCP library verifying complete request-response
cycles. Tests building MCP initialize responses, tools/list responses with pre-computed
schemas, JSON-RPC method extraction, error response creation, session lifecycle management,
tool handler registration and lookup, and full request-response simulation including
argument extraction and tool result building.

## Syntax

```simple
val request = """{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"""
val method = extract_json_string_v2(request, "method")
expect(method).to_equal("initialize")

init_core_schemas()
val tools = get_all_tool_schemas()
expect(tools).to_contain("read_code")
```

---


