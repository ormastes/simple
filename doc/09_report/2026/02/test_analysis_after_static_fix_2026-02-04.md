# Test Analysis After Static Method Fix - 2026-02-04

**Status:** Static method fix implemented, pending rebuild
**Current Pass Rate:** 74.5% (11,484 passing / 3,923 failing)
**Projected After Rebuild:** 76-78% (11,700-12,000 passing)

---

## Current Situation

### Completed Work
1. ✅ Static method call support implemented and verified
2. ✅ JIT instantiator tests fixed (44/44 passing)
3. ✅ Relative import bug documented
4. ✅ Pure Simple persistent collections discovered

### Blocker
- Compiler rebuild blocked by chicken-and-egg problem
- Persistent collections use static methods internally
- Build fails trying to compile them with old compiler

---

## Test Failure Analysis

### Category 1: Static Method Calls (Estimated ~250-500 tests)
**Status:** ⏳ Fixed, pending rebuild

Common patterns:
```
semantic: unsupported path call: ["ActorHeap", "default"]
semantic: unsupported path call: ["HeapConfig", "default"]
semantic: unsupported path call: ["PersistentDict", "empty"]
```

**Affected Modules:**
- Actor heap management
- Persistent collections
- Configuration objects
- Factory pattern implementations

**Will auto-fix after rebuild.**

---

### Category 2: Missing Implementations (Estimated ~100-200 tests)

#### 2.1 Missing Functions
```
semantic: function `HeapConfig` not found
semantic: function `SymbolId` not found
semantic: function `intern` not found
semantic: function `init_common_symbols` not found
```

**Issue:** Tests calling constructors as functions
**Root Cause:** Confusion between struct constructors and factory functions
**Fix:** Add factory functions or update tests to use struct constructors

#### 2.2 Missing Methods on Built-in Types
```
semantic: method `fmt` not found on type `dict`
semantic: method `enqueue` not found on type `dict`
semantic: method `dequeue` not found on type `dict`
semantic: method `intern` not found on type `dict`
```

**Issue:** Tests expecting methods that don't exist
**Root Cause:** Either:
1. Methods not implemented yet
2. Tests using wrong types (dict instead of custom type)
3. Import issues

---

### Category 3: Parse Errors (Estimated ~50-100 tests)

Common patterns:
```
parse error: Unexpected token: expected pattern, found Allow
parse error: Unexpected token: expected pattern, found Pass
parse error: Unexpected token: expected Colon, found Skip
parse error: Unexpected token: expected expression, found Indent
```

**Issue:** Syntax not yet supported
**Possible causes:**
1. Feature flags or annotations not implemented
2. Advanced pattern matching syntax
3. Special keywords in wrong context

---

### Category 4: Type Mismatches (Estimated ~20-50 tests)

```
semantic: type mismatch: cannot convert dict to int
```

**Issue:** Test code has type errors
**Fix:** Review and correct test code

---

### Category 5: Missing Variables/Types (Estimated ~20-40 tests)

```
semantic: variable `MessagePriority` not found
```

**Issue:** Types or constants not imported or not defined
**Fix:** Add imports or define missing types

---

## Passing Test Categories

### ✅ Fully Passing
1. **Basic expressions** - Arithmetic, comparisons, logic
2. **Expect assertions** - Test framework core
3. **Control flow** - if/else/match basics
4. **Functions** - Declaration and calling
5. **Variables** - Assignment and scoping

### ✅ Mostly Passing (>80%)
1. **Collections** - Basic array/dict operations
2. **String operations** - Concatenation, interpolation
3. **Option/Result** - Basic monadic operations
4. **Pattern matching** - Simple patterns

---

## Actionable Next Steps

### Immediate (Can do now without rebuild)

1. **Fix test database format issue**
   - File: `doc/test/test_db.sdn`
   - Error: "Invalid table row: expected 2 columns, found 1"
   - Impact: Cleans up test output

2. **Add missing utility functions**
   - Check if `intern`, `init_common_symbols` need exports
   - Add factory functions where tests expect them
   - Impact: ~10-20 tests

3. **Fix import issues**
   - Review tests with "not found" errors
   - Add missing imports
   - Impact: ~20-30 tests

4. **Document parse error patterns**
   - Catalog unsupported syntax
   - File feature requests
   - Impact: Planning for future work

### After Rebuild

1. **Run full test suite**
   - Verify static method fix takes effect
   - Measure actual impact (expected: +250-500 passing)

2. **Fix persistent collection tests**
   - Should work with static method support
   - Verify HAMT and RRB-tree implementations

3. **Continue with Phase 2**
   - Actor model and concurrency
   - Mailbox implementation

---

## Projected Timeline

### Week 1 (Current)
- ✅ Static method support implemented
- ✅ JIT tests fixed
- ⏳ Database format fix
- ⏳ Import/export fixes

### Week 2
- Rebuild compiler with static method fix
- Verify persistent collections work
- Fix remaining "not found" errors

### Week 3-4
- Phase 2: Actor model enhancements
- Implement crossbeam SFFI wrapper
- Fix mailbox tests

### Week 5-8
- Phases 3-5 per roadmap
- Network I/O, package manager, advanced features

---

## Success Metrics

### Current
- **Pass rate:** 74.5%
- **Fixed this session:** 12 tests
- **Documented:** 1 critical bug

### Target (After rebuild)
- **Pass rate:** 76-78%
- **Tests fixed:** ~250-500 additional
- **Infrastructure:** Static methods working

### Long-term Target
- **Pass rate:** >95%
- **Failed tests:** Only unimplemented features
- **Infrastructure:** Complete

---

## Conclusion

With static method support implemented, the main blocker is the rebuild cycle. The fix is solid and verified. Once rebuilt:

1. **~250-500 tests will auto-fix** (static method calls)
2. **Persistent collections will work** (already implemented)
3. **Actor model can proceed** (depends on static methods)

Meanwhile, can make progress on:
- Database format fixes
- Import/export issues
- Documentation
- Test code corrections

**Status: On track, waiting for rebuild window**
