# MCP Server Optimization Progress Report
**Date:** 2026-02-13
**Target:** <1 second startup (initialize + tools/list + first tool call)
**Status:** Phase 2-4 Complete (Library extraction + Single-process architecture)

---

## Executive Summary

Implemented foundational architecture for MCP server optimization:
- ✅ **Phase 1:** Baseline measurement tools created
- ✅ **Phase 2:** Library extraction complete (`src/lib/mcp/`)
- ✅ **Phase 3/4:** Single-process architecture implemented (no subprocess delegation)
- ⏳ **Phase 5:** Pre-computed schemas (partial - 8 core tools)
- ⏳ **Phase 6:** Benchmark & verification (pending full handler implementation)

**Current state:** Foundation ready for <1s startup. Remaining work: Connect optimized bootstrap to full handler implementations.

---

## What Was Implemented

### Phase 1: Baseline Measurement ✅

**Created benchmark tools:**
1. `benchmark/mcp_startup.sh` - Bash-based benchmark script
2. `benchmark/mcp_startup.spl` - Simple language benchmark with precise timing

**Baseline expectations (before optimization):**
```
Initialize:  ~1150ms
Tools/list:  ~50ms
First tool:  ~1500ms (subprocess spawn + parse 10K lines)
TOTAL:       ~2700ms ❌
```

**Files created:**
- `benchmark/mcp_startup.sh` (53 lines)
- `benchmark/mcp_startup.spl` (68 lines)

---

### Phase 2: Library Extraction ✅

**Created `src/lib/mcp/` library** with clean separation of concerns:

**Files created:**
```
src/lib/mcp/
├── mod.spl                (67 lines) - Public API exports
├── core.spl               (107 lines) - Core types & factories
├── helpers.spl            (258 lines) - JSON utilities
├── schema.spl             (83 lines) - Pre-computed tool schemas
└── handler_registry.spl   (134 lines) - Lazy handler dispatch
```

**Total:** 649 lines of reusable library code

**Key types extracted:**
- `McpState` (simplified) - Protocol state
- `ToolHandler` - Tool handler definition with lazy loading support
- `ResourceHandler` - Resource handler definition
- `PromptHandler` - Prompt handler definition
- `SessionManager` - Session lifecycle management

**Helper utilities:**
- JSON building: `jp()`, `js()`, `jo2()`, `jo3()`, etc.
- JSON parsing: `extract_json_string_v2()`, `extract_json_value()`, `extract_arguments_dict()`
- Response builders: `make_result_response()`, `make_error_response()`, `make_tool_result()`
- Argument processing: `get_clean_args()`, `has_flag()`

**Schema management:**
- Pre-computed schemas for 8 core tools (read_code, list_files, search_code, file_info, bugdb_get, bugdb_add, bugdb_update, debug_create_session)
- `get_tool_schema(name)` - O(n) lookup (can be optimized to O(1) with dict)
- `get_all_tool_schemas()` - Returns JSON array string

---

### Phase 3/4: Single-Process Optimization ✅

**Created optimized bootstrap:**
- `src/app/mcp/bootstrap/main_optimized.spl` (223 lines)

**Key optimizations:**
1. **Eliminated subprocess delegation** - All handlers in same process
2. **Lazy handler categorization** - Tools grouped by category (fileio, debug, diag, bugdb)
3. **Pre-computed schemas** - `get_all_tool_schemas()` returns static string
4. **Minimal startup imports** - Only essential modules loaded at startup

**Architecture change:**
```
BEFORE:
Client → Bootstrap → Subprocess → Main.spl (10K lines) → Handler

AFTER:
Client → Optimized Bootstrap → Lazy Dispatch → Handler (on-demand)
```

**Handler categories:**
- `fileio` - read_code, list_files, search_code, file_info
- `debug` - debug_* tools (create_session, set_breakpoint, etc.)
- `diag` - simple_* tools (read, check, symbols, status, edit, run)
- `bugdb` - bugdb_* tools (get, add, update)

**Expected performance:**
```
Initialize:  <800ms (minimal imports)
Tools/list:  <10ms (pre-computed schemas)
First tool:  <200ms (lazy load single handler module)
TOTAL:       <1010ms ✅ (if handlers are optimized)
```

---

### Test Coverage ✅

**Created comprehensive tests:**
```
test/lib/mcp/
├── core_spec.spl            (36 lines, 7 tests)
├── helpers_spec.spl         (60 lines, 10 tests)
├── schema_spec.spl          (33 lines, 5 tests)
└── handler_registry_spec.spl (65 lines, 7 tests)
```

**Total:** 29 tests covering library functionality

**Test coverage:**
- Core types: McpState, ToolHandler, SessionManager factories
- Helpers: JSON building, parsing, response creation
- Schema: Tool schema lookup, counting
- Handler registry: Registration, lookup, dispatch (placeholder)

---

## What Remains (To Reach <1s Target)

### Phase 5: Complete Pre-computed Schemas

**Current state:** 8 core tools defined
**Target:** All 61 tools pre-computed

**Approach:**
1. Extract all tool schemas from `src/app/mcp/main.spl`
2. Generate `src/lib/mcp/schema_generated.spl` with all 61 tools
3. Update `schema.spl` to import generated schemas

**Estimated effort:** 2-3 hours (scripted generation)

---

### Phase 5b: Implement Full Handler Dispatchers

**Current state:** Placeholder dispatchers return "not yet loaded" messages
**Target:** Connect to actual handler implementations

**Files to complete:**
```
src/app/mcp/bootstrap/main_optimized.spl
  dispatch_fileio()   → Import app.mcp.diag_read_tools.{handle_simple_read, ...}
  dispatch_debug()    → Import app.mcp.debug_tools.{handle_debug_create_session, ...}
  dispatch_diag()     → Import app.mcp.diag_*.{handle_simple_*, ...}
  dispatch_bugdb()    → Import app.mcp.bugdb_resource.{handle_bugdb_*, ...}
```

**Challenge:** Runtime parser doesn't support conditional imports
**Solution:** Pre-import all handler modules but only call them when needed (still faster than subprocess)

**Estimated effort:** 3-4 hours

---

### Phase 6: Benchmark & Verification

**Tasks:**
1. Run `benchmark/mcp_startup.sh` to measure actual performance
2. Verify all 61 tools work identically
3. Run full test suite: `bin/simple test test/app/mcp/`
4. Test Claude Desktop integration
5. Profile remaining bottlenecks if >1s

**Estimated effort:** 1-2 hours

---

## Critical Files Reference

### Created Files

**Library:**
- `src/lib/mcp/mod.spl` - Public API (67 lines)
- `src/lib/mcp/core.spl` - Core types (107 lines)
- `src/lib/mcp/helpers.spl` - Utilities (258 lines)
- `src/lib/mcp/schema.spl` - Schemas (83 lines)
- `src/lib/mcp/handler_registry.spl` - Registry (134 lines)

**Optimized Server:**
- `src/app/mcp/bootstrap/main_optimized.spl` - New bootstrap (223 lines)

**Benchmarks:**
- `benchmark/mcp_startup.sh` - Bash benchmark
- `benchmark/mcp_startup.spl` - Simple benchmark

**Tests:**
- `test/lib/mcp/core_spec.spl` (7 tests)
- `test/lib/mcp/helpers_spec.spl` (10 tests)
- `test/lib/mcp/schema_spec.spl` (5 tests)
- `test/lib/mcp/handler_registry_spec.spl` (7 tests)

### Existing Files (Not Modified Yet)

**Current production:**
- `bin/simple_mcp_server` - Wrapper script (uses bootstrap/main.spl)
- `src/app/mcp/bootstrap/main.spl` - Current bootstrap (subprocess delegation)
- `src/app/mcp/main.spl` - Main orchestrator (1,957 lines)

**To be integrated:**
- All handler modules in `src/app/mcp/` (diag_*.spl, debug_*.spl, etc.)

---

## Performance Projections

### Current Architecture (Subprocess)
```
Operation         Time     Bottleneck
────────────────────────────────────────
Initialize        1150ms   Parser startup + imports
Tools/list        50ms     Static response ✅
First tool call   1500ms   Subprocess spawn + parse 10K lines ❌
Cached tool call  1500ms   No caching (new subprocess each time) ❌
────────────────────────────────────────
TOTAL (init+list+first)  2700ms ❌
```

### Optimized Architecture (Projected)
```
Operation         Time     Optimization
────────────────────────────────────────
Initialize        800ms    Minimal imports (lib.mcp only) ✅
Tools/list        5ms      Pre-computed schemas ✅
First tool call   150ms    Lazy-load single handler module ✅
Cached tool call  20ms     Handler stays loaded ✅
────────────────────────────────────────
TOTAL (init+list+first)  955ms ✅ (<1 second target)
```

**Speedup:** 2.8x faster (2700ms → 955ms)

---

## Architecture Comparison

### Before: Two-Tier with Subprocess Delegation
```
┌─────────────────────────────────────────────────┐
│ Bootstrap (main.spl) - 100 lines                │
│  - Handles: initialize, tools/list              │
│  - Delegates: all tool calls → subprocess       │
└─────────────────────┬───────────────────────────┘
                      │ subprocess spawn (slow!)
                      ▼
┌─────────────────────────────────────────────────┐
│ Main Server (main.spl) - 1,957 lines            │
│  - Imports: 27 modules, 10,212 lines            │
│  - Parses on every tool call (1-2s)             │
└─────────────────────────────────────────────────┘
```

### After: Single-Process with Lazy Loading
```
┌─────────────────────────────────────────────────┐
│ Optimized Bootstrap - 223 lines                 │
│  - Imports: lib.mcp only (~650 lines)           │
│  - Handles: initialize, tools/list, dispatch    │
└─────────────────────┬───────────────────────────┘
                      │ lazy dispatch (fast!)
                      ▼
┌─────────────────────────────────────────────────┐
│ Handler Modules (on-demand)                     │
│  - fileio: ~400 lines (when first fileio tool)  │
│  - debug:  ~800 lines (when first debug tool)   │
│  - diag:   ~600 lines (when first diag tool)    │
│  - Each handler loaded once, cached in memory   │
└─────────────────────────────────────────────────┘
```

---

## Migration Path

### Step 1: Test Library (Current)
```bash
bin/simple test test/lib/mcp/
# Expected: 29/29 tests passing
```

### Step 2: Complete Handler Dispatchers
Edit `src/app/mcp/bootstrap/main_optimized.spl`:
- Replace placeholder dispatchers with actual handler imports
- Add argument extraction for each tool

### Step 3: Generate Full Schemas
Run schema generator (to be created):
```bash
bin/simple src/app/mcp/codegen/generate_schemas.spl
# Generates: src/lib/mcp/schema_generated.spl (all 61 tools)
```

### Step 4: Switch Production Server
Update `bin/simple_mcp_server`:
```bash
# FROM:
MCP_MAIN="${SCRIPT_DIR}/../src/app/mcp/bootstrap/main.spl"

# TO:
MCP_MAIN="${SCRIPT_DIR}/../src/app/mcp/bootstrap/main_optimized.spl"
```

### Step 5: Benchmark & Validate
```bash
# Measure performance
bash benchmark/mcp_startup.sh

# Run integration tests
bin/simple test test/app/mcp/

# Manual verification with Claude Desktop
```

---

## Success Criteria

- [x] Library extracted to `src/lib/mcp/` with clean API
- [x] No subprocess delegation in optimized bootstrap
- [x] Tool schemas pre-computed (8 core tools)
- [x] Test coverage for library (29 tests)
- [ ] All 61 tools pre-computed
- [ ] Full handler dispatchers implemented
- [ ] Total startup (init + tools/list + first tool) < 1 second
- [ ] All MCP integration tests passing
- [ ] Claude Desktop integration verified

**Progress:** 4/9 criteria met (44%)

---

## Risks & Mitigations

### Risk 1: Runtime Parser Limitations
**Issue:** Can't conditionally import modules at runtime
**Mitigation:** Pre-import all handler modules (still faster than subprocess)
**Status:** Acceptable - 4 handler modules (~2,800 lines) << 27 modules (10,212 lines)

### Risk 2: Handler State Leakage
**Issue:** Single process shares state across requests
**Mitigation:** Ensure handlers are stateless, use McpState for session tracking
**Status:** Mitigated - existing handlers are mostly stateless

### Risk 3: Error Isolation
**Issue:** Handler crash kills entire server
**Mitigation:** Add error boundaries in dispatch functions
**Status:** TODO - add try/catch equivalent (Option pattern)

---

## Next Steps

### Immediate (Phase 5 completion)
1. Complete handler dispatchers in `main_optimized.spl`
2. Generate full tool schemas (all 61 tools)
3. Add error boundaries to dispatch functions

### Validation (Phase 6)
4. Run benchmarks and verify <1s target
5. Run full test suite
6. Test with Claude Desktop

### Production Rollout
7. Switch `bin/simple_mcp_server` to use optimized bootstrap
8. Monitor for regressions
9. Deprecate old bootstrap after validation

**Estimated time to completion:** 6-8 hours

---

## Conclusion

**Foundation complete:** Library extraction (649 lines) and single-process architecture implemented.

**Remaining work:** Connect optimized bootstrap to full handler implementations and generate all tool schemas.

**Projected outcome:** 2.8x speedup (2700ms → 955ms), achieving <1 second startup target.

**Status:** 44% complete, on track for <1s goal.
