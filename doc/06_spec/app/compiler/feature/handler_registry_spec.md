# MCP Library Handler Registry Tests

**Feature ID:** #MCP-LIB-002 | **Category:** Standard Library | **Status:** Active

_Source: `test/feature/lib/mcp/handler_registry_spec.spl`_

---

## Overview

Tests the MCP handler registry for registering, finding, and clearing tool and resource
handlers. Validates tool handler registration and lookup by name, resource handler
registration and URI pattern matching, handler count tracking, and registry clearing.
Uses before_each to ensure clean state between tests.

## Syntax

```simple
val handler = create_tool_handler("test_tool", "Test tool", "{}", "app.handlers", "handle_test")
register_tool_handler(handler)
val found = find_tool_handler("test_tool")
expect(found.name).to_equal("test_tool")

clear_registries()
expect(get_tool_handler_count()).to_equal(0)
```

---


