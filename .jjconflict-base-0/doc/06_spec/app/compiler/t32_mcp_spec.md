*Source: `test/feature/app/t32_tools/t32_mcp_spec.spl`*
*Last Updated: 2026-03-12*

---

# T32 MCP Server -- JSON & Protocol Tests

**Feature IDs:** #T32-MCP-001
**Category:** Tooling
**Difficulty:** 2/5
**Status:** Implemented

## Overview

Tests for the T32 MCP server JSON helpers: encoding, object builders,
field extraction, and JSON-RPC / MCP protocol response builders.
All functions under test are pure (no I/O, no side effects).

## Source

`examples/10_tooling/trace32_tools/t32_mcp/json_helpers.spl`
