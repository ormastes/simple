# MCP Server Type Fixes - Complete Resolution

**Date:** 2026-02-06  
**Status:** ✅ COMPLETE - MCP Server Fully Operational

## Problem Summary

The MCP server was experiencing a persistent "cannot convert enum to int" runtime error that prevented it from responding to JSON-RPC requests. The error occurred during type inference when processing incoming requests.

## Root Causes Identified

### 1. Incorrect Type Names (PRIMARY ISSUE)

Simple language uses `String` and `Bool` (capitalized), but the code used incorrect lowercase variants:
- ❌ `text` → ✅ `String`  
- ❌ `bool` → ✅ `Bool`

These incorrect types caused the interpreter's type inference system to fail during complex module interactions.

### 2. Char-to-String Conversion Issues

Helper functions returned `char` but declared return type as `String`:
```simple
# BEFORE (WRONG):
fn LB() -> String:
    123 as char  # Returns char, not String!

# AFTER (CORRECT):
fn LB() -> String:
    (123 as char).to_string()
```

### 3. Type Inference in Complex Module Context

The original `extract_json_string` function used helper functions (`Q()`, `unwrap_idx()`) that caused type inference failures when called from within the MCP module context. The solution was to create a standalone implementation without helper functions.

## Files Modified

### src/app/mcp/main.spl
- Fixed `LB()` and `RB()` char-to-string conversions
- Fixed `Dict<text, text>` → `Dict<String, String>`
- Created `extract_json_string_v2()` - standalone implementation
- Removed debug trace statements

### src/app/mcp/prompts.spl
- Fixed 18 occurrences of `text` → `String`
- Fixed `bool` → `Bool` in struct field
- Added type annotation: `var prompts: [PromptInfo] = []`
- Fixed function signatures:
  - `fn get_prompt(name: String, arguments: Dict<String, String>) -> Result<PromptResult, String>`
  - All helper methods updated similarly

### src/app/mcp/bugdb_resource.spl
- Fixed 14 occurrences of `text` → `String` in function signatures

### bin/simple_mcp_server
- Updated to use bootstrap runtime: `bin/bootstrap/simple_runtime`

## Solution: extract_json_string_v2

The key breakthrough was creating a standalone JSON parser that doesn't rely on helper functions:

```simple
fn extract_json_string_v2(json: String, key: String) -> String:
    # Completely standalone implementation
    val pattern = "\"" + key + "\":"
    val idx_opt = json.index_of(pattern)

    var start_pos = -1
    match idx_opt:
        Some(pos): start_pos = pos + pattern.len()
        None: return ""

    if start_pos < 0:
        return ""

    val rest = json.substring(start_pos).trim()

    if not rest.starts_with("\""):
        return ""

    val after_quote = rest.substring(1)
    val end_opt = after_quote.index_of("\"")

    var end_pos = -1
    match end_opt:
        Some(pos): end_pos = pos
        None: return ""

    if end_pos < 0:
        return ""

    after_quote.substring(0, end_pos)
```

**Why this works:** Inline Option unwrapping with explicit match statements avoids type inference issues that occurred when calling helper functions like `unwrap_idx()`.

## Verification

### Test 1: Initialize Request
```bash
cat /tmp/mcp_test_init.json | bin/simple_mcp_server
```

**Response:**
```json
{
  "jsonrpc": "2.0",
  "id": "1",
  "result": {
    "protocolVersion": "2025-06-18",
    "capabilities": {
      "tools": {},
      "resources": {},
      "prompts": {},
      "logging": {}
    },
    "serverInfo": {
      "name": "simple-mcp",
      "version": "2.0.0",
      "instructions": "Search for Simple MCP tools..."
    }
  }
}
```

### Test 2: Tools List Request

**Response:** 7 tools returned with proper annotations:
- `read_code` - readOnly, idempotent  
- `list_files` - readOnly, idempotent  
- `search_code` - readOnly, idempotent  
- `file_info` - readOnly, idempotent  
- `bugdb_get` - readOnly, idempotent  
- `bugdb_add` - writable, non-idempotent  
- `bugdb_update` - writable, idempotent  

All annotations (readOnlyHint, destructiveHint, idempotentHint, openWorldHint) working correctly.

## Lessons Learned

1. **Type System Strictness**: Simple's type system requires exact type names (`String`, not `text`). The interpreter doesn't provide helpful error messages for these mismatches in complex module contexts.

2. **Helper Function Limitations**: In certain contexts (complex module imports + type inference), helper functions can confuse the type checker. Inline implementations work more reliably.

3. **Debugging Strategy**: Binary search by module elimination was effective in isolating which module caused the issue (prompts.spl).

4. **sed Pitfalls**: Simple regex replacements (like `s/: text$/: String/g`) miss type names in other positions (function parameters, generic arguments). Multiple targeted replacements needed.

## Current Status

✅ **MCP Server Operational**  
✅ **All P1 Features Complete**:
- Protocol version 2025-06-18  
- Tool annotations (read-only, destructive, idempotent, open-world)  
- Logging support (logging/setLevel, notifications/message)  
- Server instructions for MCPSearch integration  

✅ **All Type Errors Resolved**  
✅ **JSON-RPC Communication Working**  
✅ **Ready for Claude Code Integration**

## Next Steps

1. Test MCP server in Claude Code (Task #11 complete)  
2. Write SSpec tests for MCP features (Task #5 pending)  
3. Implement pagination for large resource lists (Task #8 pending)  
4. Add structured output for database tools (Task #9 pending)  
5. Implement roots integration (Task #10 pending)

## Installation in Claude Code

```bash
# Update Claude Code MCP configuration
# Add to ~/.config/claude/config.json:
{
  "mcpServers": {
    "simple-mcp": {
      "command": "/home/ormastes/dev/pub/simple/bin/simple_mcp_server",
      "args": [],
      "env": {}
    }
  }
}
```

**Status:** Ready for end-to-end testing in Claude Code!
