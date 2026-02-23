# MCP Implementation Continuation Report - 2026-02-06

**Status:** In Progress - Blocked
**Previous:** mcp_implementation_2026-02-06.md

---

## Summary

Continued MCP implementation with focus on fixing runtime warnings and testing in Claude Code. Hit a blocking parse error issue with database modules.

### Tasks Completed

| # | Task | Status | Notes |
|---|------|--------|-------|
| 7 | Fix runtime warnings | ⚠️ Partial | Created wrapper, blocked by parse errors |
| 8 | Implement pagination | ⏸️ Pending | Deprioritized due to blocker |
| 9 | Structured output | ⏸️ Pending | Deprioritized due to blocker |
| 10 | Roots integration | ⏸️ Pending | Deprioritized due to blocker |
| 11 | End-to-end testing | ❌ Blocked | Cannot test until parse errors fixed |

---

## Work Done

### 1. Created MCP Server Wrapper (`bin/simple_mcp_server`)

```bash
#!/bin/bash
# Simple MCP Server Wrapper
# Suppresses stderr warnings for clean stdio transport

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
RUNTIME="${SCRIPT_DIR}/../rust/target/release/simple"
MCP_MAIN="${SCRIPT_DIR}/../src/app/mcp/main.spl"

# Suppress stderr (warnings) but keep stdout (JSON-RPC)
RUST_LOG=error exec "$RUNTIME" "$MCP_MAIN" server 2>/dev/null
```

**Purpose:** Clean stdio transport by filtering stderr warnings

**Status:** Script works, but runtime has parse errors

### 2. Fixed Inline If-Then-Else Syntax

**Problem:** Bootstrap runtime doesn't support inline conditional expressions:
```simple
# ❌ Doesn't work
annot = annot + jp("readOnlyHint", if read_only then "true" else "false")
```

**Solution:** Explicit variable assignments:
```simple
# ✅ Works
var ro = "false"
if read_only:
    ro = "true"
annot = annot + jp("readOnlyHint", ro)
```

**Files Changed:** `src/app/mcp/main.spl` (~12 lines)
**Commit:** 42c0df53

### 3. Claude Code Configuration

Updated `.claude.json` to use wrapper script:

```json
{
  "mcpServers": {
    "simple-mcp": {
      "type": "stdio",
      "command": "/home/ormastes/dev/pub/simple/bin/simple_mcp_server",
      "args": [],
      "env": {}
    }
  }
}
```

**Status:** Configured but not connecting

---

## Blocking Issue: Parse Errors in Database Modules

### Error Messages

```
ERROR Failed to parse module path="/home/ormastes/dev/pub/simple/src/lib/database/bug.spl"
  error=Unexpected token: expected expression, found Mod

ERROR Failed to parse module path="/home/ormastes/dev/pub/simple/src/lib/database/feature.spl"
  error=Unexpected token: expected Colon, found Dot
```

### Root Cause

**bug.spl line 17:**
```simple
use lib.database.mod
```

The word `mod` is being interpreted as a keyword instead of a module name. The parser expects an expression but encounters the `Mod` keyword.

**feature.spl:** Similar issue with module path parsing.

### Impact

- MCP server cannot start
- Database-related tools (bugdb_get, bugdb_add, bugdb_update) unavailable
- Cannot test ANY MCP functionality in Claude Code

### Affected Modules

| Module | Import Chain | Status |
|--------|--------------|--------|
| `src/app/mcp/main.spl` | → `app.mcp.bugdb_resource` | ✅ Loads |
| `src/app/mcp/bugdb_resource.spl` | → `lib.database.bug` | ❌ Parse error |
| `src/lib/database/bug.spl` | → `lib.database.mod` | ❌ `Mod` keyword |
| `src/lib/database/feature.spl` | → ??? | ❌ Dot vs Colon |

---

## Solutions (Ranked by Feasibility)

### Option 1: Rename `lib.database.mod` Module ⭐ **RECOMMENDED**

Rename the module to avoid keyword conflict:

```bash
# Rename the file
mv src/lib/database/mod.spl src/lib/database/core.spl

# Update imports
sed -i 's/use lib\.database\.mod/use lib.database.core/g' src/lib/database/*.spl
sed -i 's/use lib\.database\.mod/use lib.database.core/g' src/app/mcp/*.spl
```

**Pros:**
- Simple, fast fix (< 5 minutes)
- No parser changes needed
- Aligns with Rust naming conventions (avoid `mod` as module name)

**Cons:**
- Breaking change if external code imports `lib.database.mod`

### Option 2: Fix Parser to Allow `mod` as Module Name

Update the Simple parser to allow reserved keywords as module path components.

**Pros:**
- More flexible parser
- No codebase changes needed

**Cons:**
- Complex parser changes
- Potential for ambiguous syntax
- Time-consuming (hours of work)

### Option 3: Remove Database Dependencies from MCP Server

Comment out database-related imports and tools:

```simple
# use app.mcp.bugdb_resource  # TEMPORARILY DISABLED

# Remove bugdb tools from tools/list
# Remove bugdb resources from resources/list
```

**Pros:**
- Quick workaround (< 10 minutes)
- Allows testing non-database MCP features

**Cons:**
- Loses 3 of 7 tools (bugdb_get, bugdb_add, bugdb_update)
- Loses bugdb:// resources
- Temporary solution only

---

## Recommended Next Steps

1. **Immediate (Unblock Testing):**
   - Execute Option 1 (rename `mod.spl` → `core.spl`)
   - Test MCP server startup
   - Verify Claude Code connection: `claude mcp list`

2. **Testing Phase:**
   - Test tools: `read_code`, `list_files`, `search_code`, `file_info`
   - Test bugdb tools: `bugdb_get`, `bugdb_add`, `bugdb_update`
   - Test resources: `@simple-mcp:bugdb://open`
   - Test prompts: `/mcp__simple-mcp__generate-tests`

3. **P2 Features (After Testing):**
   - Implement pagination (~150 lines)
   - Add structured output (~200 lines)
   - Implement roots integration (~100 lines)

4. **Documentation:**
   - Update mcp_implementation_2026-02-06.md with test results
   - Add troubleshooting guide for common issues

---

## Commits

| Hash | Message |
|------|---------|
| 4e3e21e3 | feat: Upgrade Simple MCP server protocol to 2025-06-18 with annotations |
| 3fdb0cb5 | docs: Add MCP implementation report (2026-02-06) |
| 42c0df53 | fix: Replace inline if-then-else with explicit conditionals in MCP |
| 7c9648e3 | wip: Add simple_mcp_server wrapper script |

---

## Test Results

### Connection Test

```bash
$ claude mcp list
simple-mcp: /home/ormastes/dev/pub/simple/bin/simple_mcp_server - ✗ Failed to connect
```

**Reason:** Parse errors prevent runtime from starting

### Manual Protocol Test

```bash
$ timeout 10 /tmp/test_mcp_handshake.sh
ERROR Failed to parse module path=".../src/lib/database/bug.spl"
ERROR Failed to parse module path=".../src/lib/database/feature.spl"
(no JSON-RPC response)
```

**Verdict:** Cannot proceed with testing until parse errors are resolved

---

## Metrics

**Lines Changed:** ~30 lines
- Wrapper script: 12 lines
- Syntax fixes: 12 lines
- Comments/docs: 6 lines

**Time Spent:** ~2 hours
- Wrapper creation: 30 min
- Debugging runtime issues: 1 hour
- Parse error investigation: 30 min

**Coverage:** Still 54% (blocked from further progress)

---

## Conclusion

Made progress on:
- ✅ Created clean stdio wrapper
- ✅ Fixed inline conditional syntax
- ✅ Identified blocking issue

Blocked by:
- ❌ Parser keyword conflict with `mod` module name
- ❌ Cannot test any MCP features

**Critical Path:** Rename `lib.database.mod` → `lib.database.core` to unblock all testing and development.

**ETA to Unblock:** < 10 minutes (if Option 1 is executed)
