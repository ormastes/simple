# MCP Log Store

**Feature ID:** #MCP-003 | **Category:** Application | **Status:** Active

_Source: `test/feature/app/mcp_log_store_spec.spl`_

---

## Overview

Tests the JSON serialization and tree rendering of AOP debug log entries for the MCP log store.
Validates single entry and multi-entry JSON serialization, hierarchical tree building from nested
function calls, text-based tree rendering with collapsed (>>) and expanded (v>) markers and
indentation, and status serialization including enabled state, filter pattern, entry count,
and current depth.

## Syntax

```simple
val json = log_entry_to_json(entry)
expect(json).to_contain("\"function_name\":\"start\"")

val text_tree = format_log_tree_text(entries, expanded)
expect(text_tree).to_contain(">> app.mcp.main::start_server")
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 10 |

## Test Structure

### MCP Log Store

#### log_entry_to_json

- ✅ serializes a single entry to JSON
#### log_entries_to_json

- ✅ serializes empty array
- ✅ serializes multiple entries
#### log_tree_to_json

- ✅ builds hierarchical tree from nested calls
- ✅ returns empty array for no entries
#### format_log_tree_text

- ✅ renders collapsed tree with >> markers
- ✅ renders expanded tree with v> markers
- ✅ renders nested indentation
#### log_status_to_json

- ✅ serializes status correctly
- ✅ serializes disabled status

