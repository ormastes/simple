# MCP Stdio Debug Log Tree

**Feature ID:** #MCP-STDIO-DEBUGTREE-001 | **Category:** Integration | **Status:** Active

_Source: `test/integration/app/mcp_debug_log_tree_stdio_spec.spl`_

---

## Overview

Validates MCP stdio transport behavior for `tools/call` with:
- `debug_log_enable`
- `debug_log_tree` using `{"format":"json"}`

This regression protects against connection drops/EOF on JSON tree responses.

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 1 |

## Test Structure

### MCP Stdio Debug Log Tree

- ✅ returns JSON tree and keeps session alive
