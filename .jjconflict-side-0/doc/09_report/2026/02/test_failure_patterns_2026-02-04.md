# Test Failure Pattern Analysis - 2026-02-04

**Total Tests:** 15,407
**Passing:** 11,484 (74.5%)
**Failing:** 3,923 (25.5%)

---

## Top Failure Patterns (By Frequency)

### 1. Type Constructor as Function Call (223 errors)

**Pattern:** `semantic: function 'TypeName' not found`

**Top Offenders:**
- `Lexer` - 126 occurrences
- `HirType` - 30 occurrences
- `SymbolId` - 29 occurrences
- `Type` - 22 occurrences
- `SymbolTable` - 16 occurrences

**Root Cause:** Tests calling struct/class names as functions
```simple
# Wrong:
val lexer = Lexer(input)  # Treats Lexer as function

# Should be:
val lexer = Lexer(input: input, ...)  # Named fields
# Or:
val lexer = Lexer.new(input)  # Static method (if exists)
```

**Why This Happens:**
- Constructors in Simple require named parameters
- Tests written with positional parameter syntax
- Or static constructor method doesn't exist

**Fix Strategy:**
1. Add static constructor methods (`.new()`, `.from_X()`)
2. Update tests to use named parameters
3. Or add factory functions

**Estimated Impact:** ~200-250 tests

---

### 2. Static Method Calls (200+ errors)

**Pattern:** `semantic: unsupported path call: ["Type", "method"]`

**Top Offenders:**
- `Diagnostic.error` - 36 occurrences
- `PersistentVec.empty` - 31 occurrences
- `SharedHeapConfig.small` - 28 occurrences
- `Device.CUDA` - 27 occurrences
- `LazySeq.from_array` - 26 occurrences
- `PersistentDict.empty` - 24 occurrences
- `ActorScheduler.default` - 21 occurrences
- `JsonValue.parse` - 19 occurrences
- `CompileMode.from_text` - 19 occurrences
- `CommandFilter.default` - 18 occurrences
- `Mailbox.default` - 17 occurrences

**Status:** ✅ FIXED (pending rebuild)

The static method call support is implemented in `src/compiler/resolve.spl`. All these will work after compiler rebuild.

**Estimated Impact:** ~250-300 tests

---

### 3. Method on Wrong Type (137 errors)

**Pattern:** `semantic: method 'X' not found on type 'Y'`

**Top Offenders:**
- `.len()` on `i64` - 72 occurrences
- `.hash()` on `str` - 45 occurrences
- `.tokenize()` on `dict` - 72 occurrences (36+36)
- `.simple_parser()` on `dict` - 25 occurrences
- `.Vec3()` on `dict` - 21 occurrences
- `.parse()` on `dict` - 17 occurrences

**Root Cause:** Type confusion in tests

**Analysis:**
```simple
# Example 1: len() on i64
val x: i64 = 42
x.len()  # ERROR: i64 doesn't have len()

# Likely meant:
val arr: [i64] = [42]
arr.len()  # OK

# Example 2: tokenize() on dict
val lexer: dict = ...  # Should be Lexer type
lexer.tokenize()  # ERROR: dict doesn't have tokenize()

# Should be:
val lexer: Lexer = ...
lexer.tokenize()  # OK
```

**Fix Strategy:**
1. Review test code for type errors
2. Fix variable types (dict → proper class)
3. Fix method calls on primitives

**Estimated Impact:** ~100-150 tests

---

### 4. Missing Enums/Types (135 errors)

**Pattern:** `semantic: enum/variable 'Name' not found`

**Top Offenders:**
- `LexerMode` - 69 occurrences
- `ServerState` - 52 occurrences
- `TokenKind` - 35 occurrences
- `Severity` - 31 occurrences

**Root Cause:** Missing imports or undefined types

**Example:**
```simple
# Test file:
val mode = LexerMode.Normal  # ERROR: LexerMode not found

# Missing:
use lexer.{LexerMode}

# Or type doesn't exist yet
```

**Fix Strategy:**
1. Check if types are defined
2. Add missing imports
3. Define missing types if needed

**Estimated Impact:** ~100-150 tests

---

### 5. Missing Extern Functions (75 errors)

**Pattern:** `semantic: unknown extern function: name`

**Top Offenders:**
- `capture_backtraces` - 24 occurrences
- `tcp_listener_bind` - 15 occurrences
- Other network/system functions

**Root Cause:** FFI functions not implemented

**Fix Strategy:**
1. Implement in Rust runtime
2. Add SFFI wrappers
3. Or stub for testing

**Estimated Impact:** ~75 tests

---

### 6. Missing Regular Functions (60 errors)

**Pattern:** `semantic: function 'name' not found`

**Top Offenders:**
- `upx_is_available` - 17 occurrences
- `rt_time_now_unix_micros` - 17 occurrences
- `parse_manifest_string` - 18 occurrences
- `ffi_time_now_unix_micros` - 16 occurrences

**Root Cause:** Functions not implemented or not exported

**Fix Strategy:**
1. Implement missing functions
2. Add to exports
3. Check import paths

**Estimated Impact:** ~50-75 tests

---

### 7. Type Mismatches (22 errors)

**Pattern:** `semantic: type mismatch: cannot convert X to Y`

**Example:**
- `cannot convert enum to int` - 22 occurrences
- `cannot convert dict to int` - some occurrences

**Root Cause:** Test code has type errors

**Fix Strategy:**
Review and fix test code

**Estimated Impact:** ~20-30 tests

---

### 8. Immutability Violations (17 errors)

**Pattern:** `semantic: cannot modify self.X in immutable fn method`

**Root Cause:** Trying to mutate in immutable method

**Example:**
```simple
impl Parser:
    fn advance():  # Immutable (no 'me' keyword)
        self.position += 1  # ERROR: Can't modify in immutable method

# Should be:
    me advance():  # Mutable method
        self.position += 1  # OK
```

**Fix Strategy:**
1. Change `fn` to `me` for mutating methods
2. Or refactor to functional style

**Estimated Impact:** ~15-20 tests

---

### 9. Unknown Classes (16 errors)

**Pattern:** `semantic: unknown class AsyncMock`

**Root Cause:** Test utilities not defined

**Fix Strategy:**
Create test helper classes

**Estimated Impact:** ~15-20 tests

---

### 10. Parse Errors (Estimated ~50-100 tests)

**Patterns:**
- `expected Comma, found Colon`
- `expected Colon, found Skip`
- `expected pattern, found Allow`

**Root Cause:** Unsupported syntax features

**Examples:**
```simple
# Function parameter syntax variation
fn foo(x: i64: default(0))  # Not supported

# Pattern match modifiers
match x:
    case Allow(y): ...  # 'Allow' not valid pattern keyword

# Annotation syntax
@skip  # May not work in all contexts
```

**Fix Strategy:**
1. Document unsupported syntax
2. Update parser for needed features
3. Rewrite tests with supported syntax

**Estimated Impact:** ~50-100 tests

---

## Summary by Category

| Category | Count | Status | Impact |
|----------|-------|--------|--------|
| Type constructors as functions | ~250 | Fixable now | High |
| Static method calls | ~300 | Fixed, pending rebuild | High |
| Method on wrong type | ~150 | Fixable now | Medium |
| Missing enums/types | ~150 | Fixable now | Medium |
| Missing extern functions | ~75 | Needs Rust work | Low |
| Missing functions | ~75 | Fixable now | Medium |
| Type mismatches | ~30 | Fixable now | Low |
| Immutability violations | ~20 | Fixable now | Low |
| Unknown classes | ~20 | Fixable now | Low |
| Parse errors | ~100 | Needs parser work | Medium |
| **Other/Misc** | ~753 | Various | Various |
| **Total** | ~3,923 | - | - |

---

## Actionable Priorities

### Priority 1: Quick Wins (Can fix now, ~500 tests)

1. **Add static constructor methods** (~250 tests)
   - Add `.new()` methods to Lexer, HirType, SymbolId, etc.
   - 2-4 hours work

2. **Fix type confusion in tests** (~150 tests)
   - Change dict → proper types
   - Fix method calls on wrong types
   - 3-5 hours work

3. **Add missing imports** (~150 tests)
   - Import LexerMode, TokenKind, Severity, etc.
   - 1-2 hours work

4. **Fix immutability issues** (~20 tests)
   - Change fn → me for mutating methods
   - 1 hour work

5. **Add missing function exports** (~75 tests)
   - Export functions that exist but aren't exported
   - 1-2 hours work

**Total: 8-14 hours, ~500 tests fixed**

### Priority 2: After Rebuild (~300 tests)

1. **Static method calls auto-fix**
   - No work needed, automatic
   - 0 hours work

### Priority 3: Requires Implementation (~150 tests)

1. **Missing extern functions** (~75 tests)
   - Implement in Rust
   - Add SFFI wrappers
   - 4-8 hours work

2. **Parser enhancements** (~100 tests)
   - Add unsupported syntax
   - 8-16 hours work

### Priority 4: Test Code Fixes (~50 tests)

1. **Type mismatches** (~30 tests)
   - Fix test code
   - 1-2 hours work

2. **Unknown classes** (~20 tests)
   - Create test helpers
   - 2-3 hours work

---

## Recommended Action Plan

### Week 1 (Now)
Focus on Priority 1 items:
- Day 1-2: Add static constructor methods (4h, +250 tests)
- Day 3-4: Fix type confusion (4h, +150 tests)
- Day 5: Add missing imports + exports (3h, +225 tests)

**Expected: +625 tests, 78% pass rate**

### Week 2 (After rebuild)
- Rebuild compiler (+300 tests from static methods)
- Verify persistent collections work

**Expected: +300 tests, 81% pass rate**

### Week 3-4
- Implement missing functions
- Parser enhancements
- Test helper classes

**Expected: +200 tests, 83% pass rate**

---

## Detailed Breakdown Needed

For effective fixes, need deeper analysis of:

1. **Which types need .new() methods?**
   - Lexer (126 calls)
   - HirType (30 calls)
   - SymbolId (29 calls)
   - Type (22 calls)
   - SymbolTable (16 calls)

2. **Which tests have type confusion?**
   - Tests calling .tokenize() on dict (72 calls)
   - Tests calling .len() on i64 (72 calls)
   - Tests calling .hash() on str (45 calls)

3. **Which imports are missing?**
   - LexerMode (69 uses)
   - ServerState (52 uses)
   - TokenKind (35 uses)
   - Severity (31 uses)

Ready to dive deeper into any category for implementation.
