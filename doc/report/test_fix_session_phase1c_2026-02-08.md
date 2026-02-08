# Test Fix Session - Phase 1c: Concurrent Tests (2026-02-08)

## Summary

**Goal:** Fix concurrent_spec.spl tests (Phase 1c of test repair plan)
**Result:** ✅ **33/33 tests passing (100%)**
**Time:** ~2 hours

## Fixes Applied

### 1. Module Parse Error - Reserved Keyword

**File:** `src/std/concurrent.spl`
**Issue:** Variable `gen` is a reserved keyword in Simple
**Line:** 234 in `Barrier.wait()` method

**Before:**
```simple
fn wait():
    val gen = rt_atomic_int_load(self._generation)
    # ... rest using gen
```

**After:**
```simple
fn wait():
    val current_gen = rt_atomic_int_load(self._generation)
    # ... rest using current_gen
```

### 2. Test Parse Error - Lambda Body Syntax

**File:** `test/lib/std/unit/concurrent_spec.spl`
**Issue:** Cannot use assignment statements in single-line lambda syntax
**Lines:** 205-206 in "should run callback once" test

**Problem:** `fn(): count = count + 1` causes "expected Comma, found Assign"
- Parser interprets assignment as parameter default
- Single-line lambda body must be expression, not statement

**Before:**
```simple
once.call_once(fn(): count = count + 1)
once.call_once(fn(): count = count + 1)
```

**After:**
```simple
val increment = fn():
    count = count + 1
once.call_once(increment)
once.call_once(increment)
```

### 3. Lambda Empty Body Syntax

**File:** `test/lib/std/unit/concurrent_spec.spl`
**Issue:** `pass` keyword not allowed in lambda body
**Line:** 213 in "should mark as completed" test

**Before:**
```simple
once.call_once(fn(): pass)
```

**After:**
```simple
once.call_once(fn(): ())
```

**Reason:** Use unit value `()` instead of `pass` in expression contexts

## Test Results

| Component | Tests | Status |
|-----------|-------|--------|
| MpscQueue | 9 | ✅ All passing |
| MpmcQueue | 8 | ✅ All passing |
| ConcurrentMap | 7 | ✅ All passing |
| AtomicFlag | 4 | ✅ All passing |
| Once | 3 | ✅ All passing |
| Barrier | 2 | ✅ All passing |
| **Total** | **33** | **✅ 100%** |

## Key Learnings

### Simple Language Syntax Rules

1. **Reserved Keywords:**
   - `gen` is reserved (likely for generators)
   - Always check keyword list when naming variables

2. **Lambda Syntax:**
   - Single-line: `fn(): expression` (must be expression)
   - Multi-line: Define separately then pass:
     ```simple
     val my_fn = fn():
         statement1
         statement2
     other_func(my_fn)
     ```
   - Trailing block syntax doesn't work for all cases

3. **Empty Bodies:**
   - Use `()` (unit value) not `pass` in expression contexts
   - `pass` is statement-only

## Files Modified

- `src/std/concurrent.spl` - Fixed reserved keyword
- `test/lib/std/unit/concurrent_spec.spl` - Fixed lambda syntax (2 tests)

## Next Steps

Phase 1c complete. Ready for Phase 2 (module completion) or other phases.

Total tests fixed so far:
- Phase 1a: cli_dispatch (7/25 passing)
- Phase 1b: coverage_ffi (18/29 passing)
- Phase 1c: concurrent (33/33 passing) ✅
- **Total:** 58 tests fixed/verified
