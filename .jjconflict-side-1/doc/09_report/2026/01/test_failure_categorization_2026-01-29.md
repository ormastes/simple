# Test Failure Categorization Analysis

**Generated:** 2026-01-29
**Purpose:** Categorize which test failures are due to unimplemented features vs actual bugs

---

## Executive Summary

Analysis of 95 failing tests reveals:
- **~60 tests** fail due to unimplemented language features
- **~20 tests** fail due to actual bugs (parser issues, semantic errors)
- **~15 tests** fail due to missing/stale test files

---

## Category 1: Unimplemented Language Features (~60 tests)

### Static Method Calls (HIGH PRIORITY)
**Feature:** `ClassName.static_method()` syntax
**Status:** ❌ Not implemented
**Error:** `semantic: unsupported path call: ["ClassName", "method_name"]`

**Affected Tests:**
- All LSP server tests (lifecycle, document_sync, message_dispatcher)
- MCP server tests
- Game engine tests
- Any test using `.new()` factory methods

**Example:**
```simple
val server = LspServer.new()  # ❌ Not supported yet
# ERROR: semantic: unsupported path call: ["LspServer", "new"]
```

**Workaround:** Use direct construction `LspServer(field: value, ...)` but this requires:
1. All fields to be public OR
2. Constructor functions to be regular functions not static methods

**Impact:** ~30-40 tests blocked

---

### Async/Await (HIGH PRIORITY)
**Feature:** `async fn`, `await` expressions
**Status:** ❌ Not implemented
**Error:** Various parse/semantic errors

**Affected Tests:**
- Async file I/O tests
- Network tests
- Concurrent operation tests

**Impact:** ~10-15 tests blocked

---

### Traits/Interfaces (MEDIUM PRIORITY)
**Feature:** `trait` definitions and implementations
**Status:** ❌ Parser accepts, runtime not implemented
**Error:** Parse errors or runtime failures

**Affected Tests:**
- `trait_coherence_spec`
- Polymorphism tests

**Impact:** ~5 tests blocked

---

### Generators/Yield (LOW PRIORITY)
**Feature:** `yield` keyword, generator functions
**Status:** ❌ Not implemented
**Error:** Parse errors

**Affected Tests:**
- Generator/iterator tests
- Lazy evaluation tests

**Impact:** ~2-3 tests blocked

---

### Advanced Pattern Matching (LOW PRIORITY)
**Feature:** Complex destructuring patterns
**Status:** ❌ Partially implemented
**Error:** Parse errors

**Affected Tests:**
- Advanced pattern matching tests

**Impact:** ~2-3 tests blocked

---

## Category 2: Actual Bugs (~20 tests)

### Parser Bug: `@` Operator Conflict
**Issue:** `@` operator used for both FFI calls and matrix multiplication
**Status:** ⚠️ Fix merged but needs verification
**Error:** `parse: Unexpected token: expected expression, found At`

**Affected Tests:**
- `activation_spec` (ML/torch)
- Other matrix multiplication tests

**Impact:** ~9 tests
**Fix:** Verify parser changes work correctly

---

### Parser Bug: Enum Tuple Field Parsing
**Issue:** Enum variants with tuple types fail to parse
**Example:** `Spawn((f32, f32, f32))`
**Status:** ❌ Bug identified, needs fix
**Error:** `parse: Unexpected token: expected Comma, found Colon`

**Affected Tests:**
- `assets_spec` (game_engine)
- Other enum tests with tuple fields

**Impact:** ~6 tests
**Fix:** Fix enum parsing backtrack logic

---

### Semantic Bug: None vs nil Confusion
**Issue:** Tests use Python-style `None` instead of Simple's `nil`
**Status:** ✅ Partially fixed, more cases remain
**Error:** `semantic: variable None not found`

**Affected Tests:**
- Various tests using `None`

**Impact:** ~3 tests
**Fix:** Replace `None` with `nil` throughout codebase

---

### Import/Module Resolution Issues
**Issue:** Missing imports, wildcard import syntax not supported
**Status:** ✅ Mostly fixed
**Error:** `semantic: variable X not found` or `expected identifier, found Star`

**Affected Tests:**
- Tests with `use module.*`
- Tests missing explicit imports

**Impact:** ~2 tests (mostly fixed)
**Fix:** Add explicit imports, remove wildcards

---

## Category 3: Missing/Stale Test Files (~15 tests)

### Temporary Test Files
**Issue:** Test database references `/tmp/*.spl` files that don't exist
**Status:** ⚠️ Registry cleanup needed
**Error:** `failed to read /tmp/test_*.spl: No such file or directory`

**Affected Tests:**
- `test_inject_spec`
- `actor_model_spec`
- `test_spec`
- Other `/tmp/*_spec.spl` entries

**Impact:** ~15 tests
**Fix:** Clean up `doc/test/test_db.sdn` to remove stale entries

---

## Category 4: Test Infrastructure Issues (~3 tests)

### Test Timeouts
**Issue:** Tests hang for 30+ seconds
**Status:** ⚠️ Investigation needed
**Error:** Process timeout

**Affected Tests:**
- `cli_spec`
- `spec_framework_spec`
- `fixture_spec`

**Impact:** 3 tests
**Possible causes:**
- Infinite loop in test code
- Import/module loading deadlock
- Blocking I/O without timeout

**Fix:** Add debug logging, investigate hang location

---

## Unimplemented Features Priority

| Feature | Tests Blocked | Priority | Effort | Impact |
|---------|---------------|----------|--------|--------|
| Static method calls | 30-40 | HIGH | Medium | CRITICAL |
| Async/await | 10-15 | HIGH | High | High |
| Enum tuple parsing bug | 6 | HIGH | Low | Quick win |
| `@` operator fix verification | 9 | MEDIUM | Low | Quick win |
| Traits/interfaces | 5 | MEDIUM | High | Medium |
| None→nil cleanup | 3 | LOW | Low | Quick win |
| Generators/yield | 2-3 | LOW | High | Low |
| Advanced patterns | 2-3 | LOW | Medium | Low |
| Registry cleanup | 15 | LOW | Trivial | Cosmetic |

---

## Recommendations

### Immediate Actions (Quick Wins)
1. ✅ **Fix None→nil issues** - Already in progress, ~3 tests fixed
2. **Verify `@` operator fix** - Rebuild parser and test (~9 tests)
3. **Fix enum tuple parsing** - Fix backtrack logic (~6 tests)
4. **Clean up test registry** - Remove stale `/tmp` entries (~15 tests)

**Total quick wins:** ~33 tests fixed with low effort

### Short-term (Medium Effort)
5. **Implement static method call support** - Enables ~30-40 tests
   - Alternative: Refactor LSP/MCP servers to use regular functions
   - This is CRITICAL for LSP branch coverage testing

### Long-term (High Effort)
6. **Implement async/await** - Enables ~10-15 tests
7. **Complete trait implementation** - Enables ~5 tests
8. **Implement generators/yield** - Enables ~2-3 tests

---

## LSP Branch Coverage Impact

**Critical Finding:** The LSP branch coverage plan is **BLOCKED** by missing static method call support.

**The Problem:**
- LSP server uses `LspServer.new()` pattern
- Static method calls not implemented: `semantic: unsupported path call`
- Cannot create server instances in tests
- **All 90 new LSP tests** created for branch coverage **cannot run**

**Solutions:**

### Option 1: Implement Static Method Call Support (Recommended)
- Implement `ClassName.static_method()` syntax in compiler
- Enables not just LSP tests but ~30-40 other tests
- High impact, medium effort
- Required for idiomatic Simple code

### Option 2: Refactor LSP Server (Workaround)
- Convert `static fn new()` to regular factory function:
  ```simple
  fn create_lsp_server() -> LspServer:
      LspServer(...)
  ```
- Allows tests to run immediately
- Low effort, but non-idiomatic
- Sets bad precedent for stdlib design

### Option 3: Test Alternative Approach
- Test handlers independently without full server
- Mock server state
- Partial coverage only
- Not true branch coverage

**Recommendation:** Implement Option 1 (static method calls) as it unblocks multiple test suites and enables idiomatic code patterns.

---

## Test Coverage After Fixes

| Category | Current Passing | After Quick Wins | After Static Methods | After All Features |
|----------|----------------|------------------|---------------------|-------------------|
| Parser fixes | 817 | 850 (+33) | 850 | 850 |
| Static methods | 817 | 850 | 890 (+40) | 890 |
| Async/await | 817 | 850 | 890 | 905 (+15) |
| Other features | 817 | 850 | 890 | 912 (+7) |
| **Total** | **817/912** | **850/912** | **890/912** | **912/912** |
| **Pass Rate** | **89.6%** | **93.2%** | **97.6%** | **100%** |

---

## Conclusion

1. **~65% of failures** are due to missing language features (not bugs)
2. **~21% are actual bugs** (parser issues, mostly fixable)
3. **~16% are registry/infrastructure** issues (cosmetic)

**Immediate Focus:**
- Fix parser bugs (~15 tests)
- Clean up registry (~15 tests)
- **Then implement static method calls** to unblock LSP coverage (~40 tests)

**LSP Branch Coverage Status:**
- ⏸️ **PAUSED** - Blocked by missing static method call support
- 📝 **Tests Created** - 90 comprehensive tests ready to run
- 🎯 **Path Forward** - Implement static method calls OR refactor LSP server

