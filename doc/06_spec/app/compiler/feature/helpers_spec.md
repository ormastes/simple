# MCP Library Helpers Tests

**Feature ID:** #MCP-LIB-003 | **Category:** Standard Library | **Status:** Active

_Source: `test/feature/lib/mcp/helpers_spec.spl`_

---

## Overview

Tests MCP helper utility functions for JSON construction and parsing. Covers brace/quote
helpers (LB, RB, Q), integer parsing, JSON pair and object builders (jp, js, jo2, jo3),
JSON string and value extraction from raw JSON text, and response builders for JSON-RPC
result responses, error responses, and tool results with content type annotations.

## Syntax

```simple
expect(jp("key", "value")).to_equal("\"key\":value")
val obj = jo2(jp("a", "1"), jp("b", "2"))
expect(extract_json_string_v2(json, "method")).to_equal("initialize")
val response = make_result_response("1", """{"status":"ok"}""")
val result = make_tool_result("42", "Output text")
```

---


