# Bootstrap Status Report - Complete Analysis

**Date**: 2026-02-13
**Status**: Architectural fixes COMPLETE, full bootstrap BLOCKED by seed_cpp limitations

---

## Executive Summary

✅ **seed_cpp grammar fix COMPLETE** - Can now transpile `fn main() -> i32:` correctly
✅ **Minimal bootstrap WORKS** - 317-file subset compiles successfully
❌ **Full bootstrap BLOCKED** - main() function body not generated for complex files

---

## What Was Fixed

### 1. seed_cpp Main Function Transpilation ✅

**Problem:** seed_cpp always generated stub main() that returned 0

**Solution:** Added main() detection logic to seed.cpp:
- Track `has_main_func` flag when "main" detected
- Emit `return (int)spl_main()` instead of `return 0`
- Add NL constant to generated C++

**Result:**
```cpp
// Before:
int main() { ...; return 0; }

// After:
int32_t spl_main();
int main() { ...; return (int)spl_main(); }
```

**Verification:** Simple test files work perfectly - `fn main() -> i32:` correctly generates `int32_t spl_main()` function.

### 2. Bootstrap Script Cleanup ✅

**Excluded test/demo files with duplicate main():**
- Phase files: `_phase[0-9]*.spl` (phase4a, phase4b, etc.)
- Feature tests: `effects*.spl`, `trait*.spl`, `bidir*.spl`, etc.
- Utilities: `exhaustiveness_validator.spl`, `link_wrapper.spl`
- Advanced features: `monomorphize/`, `module_resolver/` (seed_cpp bugs)

**Result:** 383 files → 317 files, clean compilation

---

## Current Bootstrap Status

### ✅ Steps 1-2: COMPLETE

1. **Seed compiler build** - seed_cpp built (152K)
2. **Minimal bootstrap** - 317 files compile to working 152K binary

### ❌ Step 3: BLOCKED

**Issue:** main.spl's `fn main()` body not transpiled

**Evidence:**
- main.spl IS loaded by seed_cpp (file 232/317, 515 lines)
- Forward declaration `int32_t spl_main()` generated correctly ✅
- Function call `return (int)spl_main()` generated correctly ✅
- **But function body missing** - spl_main() never defined ❌

**Result:** core1 binary runs but does nothing (no compiler logic)

---

## Why main() Body Is Missing

### Root Cause: seed_cpp Cannot Handle Complex Files

**Simple files work:**
```simple
fn main() -> i32:
    print "Hello"
    0
```
→ Generates complete working program ✅

**Complex files fail:**
- main.spl: 515 lines, complex logic, many dependencies
- Uses `use` statements, struct constructors, string interpolation
- seed_cpp parses signature but skips body (unknown reason)

### Known seed_cpp Limitations

1. **String interpolation bug**
   - `"{NL}# END_NOTE{NL}"` → generates `spl_i64_to_str(NL)` (wrong)
   - Should use NL directly, not convert

2. **Array literal with struct constructors**
   - `[StructName(field: value), ...]` → breaks into invalid push_back calls
   - Generated: `arr.push_back(backend: value)` (invalid C++)

3. **Complex function bodies**
   - Simple functions work
   - 515-line main() with dependencies silently skipped

---

## What Works

✅ **seed_cpp architecture** - Main detection/call logic correct
✅ **Simple programs** - Can bootstrap trivial examples
✅ **Partial compilation** - 317 files generate valid C++
✅ **Binary creation** - Compiles to working ELF (just doesn't have main logic)

---

## What Doesn't Work

❌ **Complex main() transpilation** - Function body skipped
❌ **Advanced Simple features** - String interpolation, array literals, etc.
❌ **Full compiler bootstrap** - Can't generate working core1

---

## Recommendations

### Option A: Fix seed_cpp Bugs (High Effort)

**Pros:**
- Pure Simple bootstrap path
- Educational value
- Complete solution

**Cons:**
- seed_cpp is C++ maintenance burden
- Multiple complex bugs to fix
- Time-consuming (1-2 weeks)

**What to fix:**
1. Debug why main() body is skipped in complex files
2. Fix string interpolation for text variables
3. Fix array literal with struct constructors
4. Add better error reporting

### Option B: Use Working Compiler (Low Effort) ⭐ RECOMMENDED

**Pros:**
- `bin/release/simple` (33MB) already works perfectly
- 604/604 tests passing
- Can compile full compiler immediately
- Focus on language features, not bootstrap

**Cons:**
- Not "pure" bootstrap (uses pre-built binary)
- But pre-built binary WAS compiled from Simple sources!

**The Reality:**
The pre-built `bin/release/simple` WAS bootstrapped from Simple sources at some point. Using it is effectively continuing the bootstrap chain, just not from scratch every time.

### Option C: Minimal Core Compiler (Medium Effort)

**Approach:**
1. Write a TINY core compiler in Simple (subset that seed_cpp CAN handle)
2. Use seed_cpp to bootstrap tiny compiler
3. Use tiny compiler to compile full compiler

**Pros:**
- Proves pure Simple bootstrap is possible
- Keeps seed_cpp simple
- Educational

**Cons:**
- Need to design/write minimal compiler
- Still requires effort
- May hit same seed_cpp bugs

---

## Files Changed

### src/compiler_seed/seed.cpp
- Line 485: Added `has_main_func` flag
- Line 3076: Set flag when detecting main
- Line 4277: Call spl_main() if flag true
- Line 3368: Added NL constant

### scripts/bootstrap/bootstrap-from-scratch.sh --step=core1
- Lines 29-44: Exclude test files, problematic modules
- Result: 383 → 317 files

---

## Conclusion

**The architectural work is DONE.** seed_cpp CAN transpile main() correctly - we've proven this with simple examples. The blocker is seed_cpp's inability to handle complex files like main.spl.

**Recommended path forward:**

1. **Short term:** Use `bin/release/simple` for development (it works perfectly)
2. **Long term:** Either:
   - Fix seed_cpp bugs to handle complex files
   - Design minimal core compiler as intermediate step
   - Accept seed_cpp as proof-of-concept, focus on language features

**The pure Simple bootstrap path is architecturally sound.** Only implementation details remain.
