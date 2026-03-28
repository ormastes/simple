# MCP Debug Log Tools

**Feature ID:** #MCP-001 | **Category:** Application | **Status:** Active

_Source: `test/feature/app/mcp_debug_log_spec.spl`_

---

## Overview

Tests the MCP tool handlers and JSON schemas for AOP debug logging. Validates schema generation
for enable, disable, clear, query, tree, and status tools including correct parameter definitions
and hint annotations (readOnlyHint, destructiveHint). Tests handler functions for enabling/disabling
logging, clearing entries, querying with filters, rendering text and JSON call trees, and
accessing debug log data through the resource endpoint (/status, /entries, /tree, /text).

## Syntax

```simple
val schema = schema_debug_log_enable()
expect(schema).to_contain("debug_log_enable")

debug_log_enable("*")
val g1 = debug_log_enter("func", "mod", "", 1, "")
debug_log_exit("func", "mod", g1, 0)
val result = handle_debug_log_query("4", body)
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 19 |

## Test Structure

### MCP Debug Log Tools

#### tool schemas

- ✅ generates enable schema with pattern param
- ✅ generates disable schema
- ✅ generates clear schema with destructive hint
- ✅ generates query schema with filter params
- ✅ generates tree schema with format and expand params
- ✅ generates status schema as read-only
#### handle_debug_log_enable

- ✅ enables logging and returns status
#### handle_debug_log_disable

- ✅ disables logging
#### handle_debug_log_clear

- ✅ clears all entries
#### handle_debug_log_query

- ✅ returns entries as JSON
- ✅ filters by entry_type
#### handle_debug_log_tree

- ✅ returns text tree by default
- ✅ returns JSON tree when format=json
#### handle_debug_log_status

- ✅ returns current status
#### debuglog resource

- ✅ handles /status query
- ✅ handles /entries query
- ✅ handles /tree query
- ✅ handles /text query
- ✅ returns error for unknown query

