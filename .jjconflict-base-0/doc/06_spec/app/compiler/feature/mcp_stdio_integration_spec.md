# MCP Stdio Integration

**Feature ID:** #MCP-STDIO-INTEGRATION-001 | **Category:** Integration | **Status:** Active

_Source: `test/integration/app/mcp_stdio_integration_spec.spl`_

---

## Overview

Validates framed MCP stdio transport against `bin/simple_mcp_server` for tool-level
error behavior.

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 1 |

## Test Structure

### MCP Protocol Runtime

- ✅ returns tool-level isError for unknown tool
