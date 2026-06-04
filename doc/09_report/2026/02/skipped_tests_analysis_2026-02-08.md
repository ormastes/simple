# Skipped Tests Analysis - Can They Be Fixed?

**Generated:** 2026-02-08
**Total Skipped:** 1,302 tests
**Focus Areas:** GC (102), Debug (104), Failsafe (51), MCP (46)

## Executive Summary

**Can these be fixed with Pure Simple + SFFI?**
- ✅ **GC**: YES - needs runtime SFFI + test fixes
- ✅ **Failsafe**: YES - already pure Simple, needs test syntax fixes
- ⚠️ **Debug**: PARTIAL - needs FFI for interpreter introspection
- ⚠️ **MCP Error**: PARTIAL - needs static method desugaring in runtime

## 1. GC Tests (102 skipped) - ✅ FIXABLE

### Current Status
- **Implementation:** ✅ Complete at `src/lib/gc.spl` (350+ lines, pure Simple)
- **Test File:** `test/lib/std/unit/gc_spec.spl`
- **Skip Reason:** Runtime limitations, not missing functionality

### Issues
1. **Constructor Pattern:** Tests use `GcObjectHeader.new()` which creates dicts in runtime
2. **Enum Access:** `GcColor.White/Gray/Black` may have runtime issues
3. **Runtime Value APIs:** `std.runtime_value` not fully available

### Solution Path

**Option A: Runtime SFFI (Recommended)**
```simple
# src/app/io/gc_ffi.spl - Three-tier SFFI wrapper
extern fn rt_gc_alloc(size: i64, type_id: i64) -> i64
extern fn rt_gc_mark(ptr: i64)
extern fn rt_gc_sweep() -> i64
extern fn rt_gc_collect() -> i64
extern fn rt_gc_stats() -> text  # JSON string

fn gc_allocate(size: i64, type_id: i64) -> GcPtr:
    val ptr = rt_gc_alloc(size, type_id)
    GcPtr(ptr: ptr, size: size)

fn gc_mark(obj: GcPtr):
    rt_gc_mark(obj.ptr)

fn gc_sweep() -> i64:
    rt_gc_sweep()

fn gc_collect() -> i64:
    rt_gc_collect()
```

**Option B: Test Fixes Only**
1. Replace `.new()` with direct construction:
   ```simple
   # Before
   val header = GcObjectHeader.new(size, type_id)

   # After
   val header = GcObjectHeader(size: size, color: GcColor.White, ...)
   ```

2. Use helper functions for enum access:
   ```simple
   fn gc_color_white() -> GcColor: GcColor.White
   fn gc_color_gray() -> GcColor: GcColor.Gray
   ```

3. Mock runtime_value APIs:
   ```simple
   # test/helpers/gc_helpers.spl
   fn mock_runtime_value(type_id: i64) -> RuntimeValue:
       RuntimeValue(id: type_id, data: [])
   ```

### Effort Estimate
- **Option A (SFFI):** 3-4 hours (C++/Rust wrapper + Simple API)
- **Option B (Test fixes):** 2-3 hours (pattern replacement across 102 tests)
- **Recommended:** Option B first (faster, tests implementation), then Option A (production use)

### Test Breakdown
- GcObjectHeader: 7 tests (header creation, marking)
- GcConfig: 3 tests (configuration)
- GcStats: 4 tests (metrics)
- GcHeap: 88 tests (allocation, collection, roots, weak refs, generations)

---

## 2. Failsafe Tests (51 skipped) - ✅ FIXABLE

### Current Status
- **Implementation:** ✅ Complete at `src/lib/failsafe/` (8 modules, 3,000+ lines)
  - `core.spl`: Error types, metrics, logging
  - `panic.spl`: Panic recovery, safe operations
  - `ratelimit.spl`: Token bucket, rate limiting
  - `circuit.spl`: Circuit breaker pattern
  - `timeout.spl`: Timeout management
  - `resource_monitor.spl`: Resource tracking
  - `mod.spl`: Unified context (MCP/LSP/DAP configs)
- **Test Files:**
  - `test/lib/std/integration/failsafe/failsafe_integration_spec.spl` (26 tests)
  - `test/lib/std/integration/failsafe/crash_prevention_spec.spl` (25 tests)
- **Skip Reason:** Test syntax issues, NOT implementation issues

### Issues (Pure Syntax Problems)
1. **Lambda blocks with curly braces:** Parser doesn't support `{ ... }` in lambda expressions
2. **Complex nested expressions:** "expected expression, found Indent" errors
3. **API availability:** Types imported but runtime can't resolve them

### Solution Path

**Fix 1: Replace Lambda Curly Braces**
```simple
# Before (causes parse error)
val result = context.execute("op", "client", { compute() })

# After (works)
val result = context.execute("op", "client", fn(): compute())
```

**Fix 2: Flatten Nested Expressions**
```simple
# Before (parse error)
expect(
    context.execute("op", "client", operation)
        .is_ok()
).to_equal(true)

# After (works)
val result = context.execute("op", "client", operation)
val is_ok = result.is_ok()
expect(is_ok).to_equal(true)
```

**Fix 3: Import Fixes**
```simple
# Current (broken)
use std.failsafe

# Fixed (explicit imports)
use std.failsafe.{FailSafeContext, FailSafeResult}
use std.failsafe.core.{FailSafeError, ErrorCategory}
```

### Effort Estimate
- **2-3 hours** to fix all 51 tests (mostly find/replace patterns)
- Implementation is 100% complete and pure Simple
- Just need syntax compatibility fixes

### Test Breakdown
- FailSafeContext: 9 tests (creation, execution, health)
- MCP Fail-Safe: 4 tests (tool execution, resource protection)
- LSP Fail-Safe: 3 tests (completion requests, tolerance)
- DAP Fail-Safe: 3 tests (debug operations)
- Panic Recovery: 4 tests (isolation, frequency, shutdown)
- Rate Limiting: 4 tests (DoS prevention, sliding window)
- Circuit Breaker: 4 tests (fail-fast, recovery)
- Timeout Protection: 4+ tests (async operations)

---

## 3. Debug Tests (104 skipped) - ⚠️ PARTIAL

### Current Status
- **Implementation:** ✅ Exists at `src/app/interpreter.helpers/debug.spl`
- **Test File:** `test/app/interpreter/helpers/debug_spec.spl`
- **Skip Reason:** Dependencies on interpreter internals

### Issues
1. **Rust-style syntax:** Uses `static mut`, `unsafe` blocks not in Simple grammar
2. **Module imports:** `from ..core import` syntax not supported in runtime
3. **Interpreter coupling:** Needs `Value`, `Interpreter`, `InterpreterError` types
4. **REPL integration:** Requires interpreter state access

### Solution Paths

**Option A: Pure Simple Rewrite (Recommended)**
```simple
# src/lib/debug.spl - Pure Simple version
enum DebugLevel:
    Off, Error, Warn, Info, Debug, Trace

# Use module-level var instead of static mut
var g_debug_level = DebugLevel.Off
var g_trace_enabled = false

fn set_debug_level(level: DebugLevel):
    # WORKAROUND: Can't modify module vars from imported functions
    # Need SFFI to persist state
    pass

fn debug_print(level: DebugLevel, msg: text):
    val prefix = match level:
        DebugLevel.Error: "[ERROR]"
        DebugLevel.Warn: "[WARN]"
        DebugLevel.Info: "[INFO]"
        DebugLevel.Debug: "[DEBUG]"
        DebugLevel.Trace: "[TRACE]"
        _: ""
    print "{prefix} {msg}"
```

**Option B: SFFI for Interpreter State**
```simple
# src/app/io/debug_ffi.spl
extern fn rt_debug_get_callstack() -> text  # JSON array
extern fn rt_debug_get_locals() -> text     # JSON object
extern fn rt_debug_set_breakpoint(file: text, line: i64)
extern fn rt_debug_step_into()
extern fn rt_debug_step_over()

fn get_call_stack() -> [StackFrame]:
    val json = rt_debug_get_callstack()
    parse_stack_frames(json)

fn get_local_vars() -> {text: text}:
    val json = rt_debug_get_locals()
    parse_locals(json)
```

### Challenges
1. **Module var limitation:** Can't modify `var g_debug_level` from imported functions
2. **Interpreter introspection:** Needs runtime support for call stack, locals
3. **Breakpoint management:** Requires interpreter modifications

### Effort Estimate
- **Option A (Pure Simple):** 4-5 hours (limited to logging, no REPL/breakpoints)
- **Option B (SFFI):** 8-10 hours (full debugger with interpreter bridge)
- **Hybrid:** 3-4 hours (logging + basic introspection)

### What Can Work Without SFFI
- ✅ Debug levels (Off, Error, Warn, Info, Debug, Trace)
- ✅ Debug printing with level filtering
- ✅ Log formatting
- ❌ Breakpoints (needs interpreter)
- ❌ Call stack introspection (needs interpreter)
- ❌ Watch expressions (needs interpreter)
- ❌ REPL commands (needs interpreter)

### Recommended Approach
1. **Phase 1 (2 hours):** Pure Simple logging (40/104 tests)
2. **Phase 2 (4 hours):** SFFI for read-only introspection (70/104 tests)
3. **Phase 3 (6 hours):** Full debugger with breakpoints (104/104 tests)

---

## 4. MCP Error Handler Tests (46 skipped) - ⚠️ PARTIAL

### Current Status
- **Implementation:** Likely exists in `src/app/mcp/` (19 files)
- **Test File:** `test/lib/std/unit/mcp/error_handler_spec.spl`
- **Skip Reason:** Static method calls, enum access unsupported in runtime

### Issues
1. **Static methods:** `ErrorCategory.new()`, `McpError.new()` not in runtime
2. **Enum access:** `ErrorCategory.InvalidRequest` path resolution fails
3. **Type resolution:** Imported types not found by bootstrap runtime
4. **Validation limits:** `InputValidator.default()` static call

### Solution Path

**Apply Static Method Desugaring**

The compiler has static method desugaring (`src/app/desugar/`), but runtime doesn't:

```simple
# Before (fails in runtime)
val error = McpError.new(ErrorCategory.InvalidRequest, "Bad input")
val validator = InputValidator.default()

# After (works with desugaring)
val error = McpError__new(ErrorCategory.InvalidRequest, "Bad input")
val validator = InputValidator__default()
```

**Or use direct construction:**
```simple
# Direct construction (preferred)
val error = McpError(
    category: ErrorCategory.InvalidRequest,
    message: "Bad input",
    recoverable: true
)

val validator = InputValidator(
    limits: ValidationLimits(max_content_length: 1048576, ...)
)
```

### Effort Estimate
- **Option A (Enable desugaring in runtime):** 6-8 hours (modify runtime parser)
- **Option B (Fix tests with direct construction):** 3-4 hours (rewrite test setup)
- **Recommended:** Option B (faster, already works in compiled code)

### Test Breakdown
- ErrorCategory: 1 test (string conversion)
- McpError: 4 tests (creation, recovery, details, JSON-RPC)
- ValidationLimits: 2 tests (default, strict)
- InputValidator: 39 tests (content length, strings, URIs, tool names, arrays, params)

---

## Summary Table

| Category | Tests | Implementation | Issue Type | Effort | Fixable? |
|----------|-------|----------------|------------|--------|----------|
| **GC** | 102 | ✅ Complete | Runtime + test patterns | 2-4h | ✅ YES |
| **Failsafe** | 51 | ✅ Complete | Test syntax only | 2-3h | ✅ YES |
| **Debug** | 104 | ⚠️ Partial | Interpreter coupling | 4-10h | ⚠️ PARTIAL |
| **MCP Error** | 46 | ✅ Exists | Static methods | 3-4h | ✅ YES |
| **TOTAL** | **303** | - | - | **11-21h** | **199/303 (66%)** |

## Recommendations

### Quick Wins (1-2 days)
1. **Failsafe tests** (2-3h): Just syntax fixes, implementation is done
2. **MCP Error tests** (3-4h): Direct construction pattern
3. **GC tests** (2-3h): Constructor and enum fixes

**Total: 7-10 hours, unlocks 199 tests (66%)**

### Future Work (1-2 weeks)
4. **GC Runtime SFFI** (3-4h): Production-quality GC bindings
5. **Debug Logger** (4-6h): Pure Simple logging + basic introspection
6. **Debug Full SFFI** (8-10h): Complete debugger with breakpoints

**Total: 15-20 hours, unlocks 70+ more tests**

## Action Plan

### Week 1: Pure Simple Fixes
```bash
# Day 1: Failsafe (51 tests)
1. Fix lambda syntax in failsafe_integration_spec.spl
2. Flatten nested expressions in crash_prevention_spec.spl
3. Fix imports to explicit pattern

# Day 2: MCP Error (46 tests)
4. Replace static method calls with direct construction
5. Fix enum access patterns
6. Update import statements

# Day 3: GC (102 tests)
7. Replace .new() calls with direct construction
8. Add enum helper functions
9. Mock runtime_value dependencies
```

### Week 2: SFFI Integration
```bash
# Day 1-2: GC Runtime (production quality)
10. Create src/app/io/gc_ffi.spl
11. Implement C++ wrapper in .build/rust/ffi_gc/
12. Update GC tests to use SFFI

# Day 3-5: Debug SFFI (introspection)
13. Create src/app/io/debug_ffi.spl
14. Implement interpreter bridge for call stack/locals
15. Add breakpoint management APIs
```

---

## Conclusion

**Main Finding:** Most skipped tests can be fixed with pure Simple!

- **66% (199/303)** fixable in 1-2 days with test syntax fixes only
- **Implementation already exists** for GC, Failsafe, MCP Error
- **No new features needed** - just make existing code work in runtime
- **Debug** is the only area requiring significant FFI work

**Priority Order:**
1. Failsafe (highest ROI, just syntax)
2. MCP Error (moderate effort, clear path)
3. GC (test fixes, then optional SFFI)
4. Debug (longer-term, needs planning)
