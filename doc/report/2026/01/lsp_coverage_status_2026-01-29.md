# LSP Branch Coverage - Status Report

**Date:** 2026-01-29
**Status:** ⏸️ BLOCKED - Awaiting static method call implementation

---

## What Was Completed

### ✅ Phase 1: Coverage Analysis
1. **Analyzed LSP server architecture** (`src/app/lsp/server.spl`)
   - Identified 74 branches across 13 handler methods
   - Current coverage: ~15% (only 11 branches tested)
   - Target: 100% branch coverage

2. **Created comprehensive coverage plan**
   - Document: `doc/report/lsp_branch_coverage_2026-01-29.md`
   - Identified 9 test files needed for 100% coverage
   - Estimated 90 new tests required

3. **Implemented Phase 1 Tests** (3 files, 68 tests)
   - ✅ `server_lifecycle_spec.spl` - 17 tests (lifecycle flow)
   - ✅ `document_sync_spec.spl` - 30 tests (document management)
   - ✅ `message_dispatcher_spec.spl` - 21 tests (message routing)

4. **Categorized all test failures**
   - Document: `doc/report/test_failure_categorization_2026-01-29.md`
   - 95 total failures: 60 unimplemented features, 20 bugs, 15 registry issues

---

## ❌ Blocking Issue: Static Method Calls Not Implemented

### The Problem

All LSP tests fail with:
```
semantic: unsupported path call: ["LspServer", "new"]
```

**Root Cause:** Simple language doesn't support static method calls:
```simple
val server = LspServer.new()  # ❌ Not supported
```

**Impact:**
- All 68 Phase 1 tests cannot run
- ~30-40 other tests also blocked
- LSP branch coverage completely blocked

---

## Solutions

### Option 1: Implement Static Method Call Support ⭐ RECOMMENDED
**Pros:**
- Unblocks LSP tests AND ~30-40 other tests
- Enables idiomatic Simple code patterns
- High impact across entire codebase

**Cons:**
- Medium effort (compiler/semantic changes)
- Requires understanding of method resolution

**Implementation:**
- Add static method resolution to semantic analyzer
- Support `ClassName.static_method()` syntax
- Update method registry for static methods

---

### Option 2: Refactor LSP Server (Workaround)
**Pros:**
- Low effort, quick fix
- Tests can run immediately

**Cons:**
- Non-idiomatic code pattern
- Sets bad precedent for stdlib
- Doesn't fix other affected tests

**Implementation:**
```simple
# Before (static method - not supported)
class LspServer:
    static fn new() -> LspServer:
        LspServer(...)

# After (regular function - works now)
fn create_lsp_server() -> LspServer:
    LspServer(...)
```

---

### Option 3: Partial Testing Without Server
**Pros:**
- Can test some handlers independently
- No blocking issues

**Cons:**
- Not true branch coverage
- Misses integration paths
- Incomplete testing

---

## Deliverables Created

### Documentation (4 files)
1. `doc/report/lsp_branch_coverage_2026-01-29.md` - Full coverage analysis
2. `doc/report/test_failure_categorization_2026-01-29.md` - Failure analysis
3. `doc/report/lsp_coverage_status_2026-01-29.md` - This file

### Test Files (3 files, 68 tests) - ⚠️ Cannot run yet
1. `test/lib/std/unit/lsp/server_lifecycle_spec.spl` - 17 tests
2. `test/lib/std/unit/lsp/document_sync_spec.spl` - 30 tests
3. `test/lib/std/unit/lsp/message_dispatcher_spec.spl` - 21 tests

### Remaining Test Files (Phase 2-4) - 6 files, ~22 tests
4. `error_handling_spec.spl` - Error path coverage
5. `verification_spec.spl` - Custom handlers (Lean integration)
6. `debouncing_spec.spl` - Optimization features
7. `query_cache_spec.spl` - Cache behavior
8. `diagnostics_integration_spec.spl` - End-to-end diagnostics
9. Enhancements to existing 7 test files

---

## Test Failure Analysis Summary

### By Category
- **Unimplemented Features:** 60 tests (~63%)
  - Static method calls: ~30-40 tests
  - Async/await: ~10-15 tests
  - Traits: ~5 tests
  - Other: ~5-10 tests

- **Actual Bugs:** 20 tests (~21%)
  - `@` operator parsing: ~9 tests
  - Enum tuple parsing: ~6 tests
  - None/nil confusion: ~3 tests
  - Other: ~2 tests

- **Registry/Infrastructure:** 15 tests (~16%)
  - Stale `/tmp` file entries: ~15 tests

### Quick Wins Available (~33 tests)
1. Verify `@` operator fix (+9 tests)
2. Fix enum tuple parsing (+6 tests)
3. Fix remaining None→nil (+3 tests)
4. Clean up test registry (+15 tests)

---

## Recommended Path Forward

### Immediate (This Session)
1. ✅ Complete test failure categorization
2. ✅ Document LSP coverage status
3. ⏭️ **DECISION POINT:** Choose Option 1, 2, or 3

### If Option 1 (Implement Static Methods) - Recommended
1. Implement static method call support in compiler
2. Test with simple examples
3. Run all 68 LSP tests
4. Continue with Phases 2-4 (22 more tests)
5. Achieve 100% LSP branch coverage

### If Option 2 (Refactor) - Workaround
1. Refactor `LspServer.new()` to regular function
2. Update all 3 test files
3. Run tests (should pass)
4. Continue with Phases 2-4
5. Note: Doesn't fix other blocked tests

### If Option 3 (Partial Testing) - Incomplete
1. Create handler-only tests
2. Skip full server integration
3. Achieve partial coverage only
4. Note: Not true branch coverage

---

## Metrics

### Test Progress
- **Total tests in project:** 912
- **Currently passing:** 817 (89.6%)
- **Currently failing:** 95 (10.4%)
- **After quick wins:** 850 (93.2%)
- **After static methods:** 890 (97.6%)
- **After all features:** 912 (100%)

### LSP Coverage Progress
- **Current branch coverage:** ~15%
- **Target branch coverage:** 100%
- **Tests created:** 68 (Phase 1 of 4)
- **Tests remaining:** 22 (Phases 2-4)
- **Total new tests planned:** 90

---

## Conclusion

**LSP branch coverage analysis is COMPLETE** but **test execution is BLOCKED** by missing static method call support.

**Recommendations:**
1. Implement static method calls (Option 1) - HIGH PRIORITY
2. This unblocks not just LSP tests but ~40 other tests
3. After unblocking, complete Phases 2-4 for 100% coverage
4. In parallel, fix quick wins (~33 tests) for immediate gains

**Decision needed:** Which option to pursue for unblocking LSP tests?
