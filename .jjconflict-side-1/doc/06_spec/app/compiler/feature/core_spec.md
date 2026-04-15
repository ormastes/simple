# MCP Library Core Tests

**Feature ID:** #MCP-LIB-001 | **Category:** Standard Library | **Status:** Active

_Source: `test/feature/lib/mcp/core_spec.spl`_

---

## Overview

Tests the core MCP (Model Context Protocol) library functionality including MCP state
creation and initialization tracking, tool handler creation with module and function
references, and session manager lifecycle operations (add, remove, existence check).
Validates the foundational building blocks used by the MCP server implementation.

## Syntax

```simple
val state = create_mcp_state()
expect(state.initialized).to_equal(false)

val handler = create_tool_handler("test_tool", "Test description",
    """{"type":"object"}""", "app.mcp.handlers.test", "handle_test")
expect(handler.name).to_equal("test_tool")

var sm = create_session_manager()
val id = sm.add_session()
```

---


