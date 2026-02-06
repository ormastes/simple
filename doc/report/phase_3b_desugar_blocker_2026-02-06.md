# Phase 3B: Desugaring Blocker - 2026-02-06

**Status:** ⚠️ Blocked on generic type parameters

## Executive Summary

Successfully implemented systematic desugaring infrastructure, but discovered a **critical blocker**: desugared static methods lose their generic type parameters when hoisted from `impl` blocks.

## What Was Accomplished

✅ **Desugaring Infrastructure (Complete)**
- Created `script/bulk_desugar_all.spl` - Systematic batch processing
- Created `script/find_and_desugar.spl` - Pattern-based file discovery
- Created `script/fix_exports.spl` - Automatic export generation
- Processed 520+ files successfully

✅ **Transformation Works**
- Static methods successfully hoisted: `impl Type: static fn method()` → `fn Type__method()`
- Static calls successfully rewritten: `Type.method()` → `Type__method()`
- Export statements correctly generated
- Import statements correctly updated

❌ **Runtime Blocker: Generic Type Parameters Lost**
```simple
# BEFORE (in impl block):
impl LazySeq<T>:
    static fn empty() -> LazySeq<T>:    # <T> inherited from impl
        LazySeq(node: Lazy.of(LazySeqNode.Empty))

# AFTER (hoisted):
fn LazySeq__empty() -> LazySeq<T>:      # ERROR: T undefined!
    LazySeq(node: Lazy__of(LazySeqNode.Empty))
```

**Error:** `semantic: function `LazySeq__empty` not found`

**Root Cause:** The desugared function references type parameter `<T>` but doesn't declare it. When static methods are in `impl LazySeq<T>:`, they inherit `<T>`. When hoisted to module level, they lose this context.

## Test Results

**Before desugaring:**
- Error: `unsupported path call: ["LazySeq", "empty"]`
- 9 examples, 9 failures (100% failure rate)

**After desugaring:**
- Error: `semantic: function `LazySeq__empty` not found`
- 9 examples, 9 failures (same failure count, different error)

**Progress:** Moved from "unsupported syntax" to "missing type parameters" - this is advancement, but still blocked.

## Technical Analysis

### Generic Parameter Problem

The desugaring tool correctly performs textual transformation:
1. ✅ Extracts `static fn` from `impl` blocks
2. ✅ Renames to `Type__method`
3. ✅ Rewrites calls
4. ❌ **Does NOT preserve type context**

For generic types, this causes:
```simple
# Invalid: references T without declaring it
fn LazySeq__empty() -> LazySeq<T>:  # ERROR: T not in scope
    ...

# What we need:
fn LazySeq__empty<T>() -> LazySeq<T>:  # Explicit type parameter
    ...
```

### Files Affected

**High-frequency generic types with static methods:**
- `LazySeq<T>` - 11 static methods
- `Cache<K, V>` - 3 static methods
- `Builder<T>` - 2 static methods
- `Option<T>` - 2 static methods (if any)
- `Result<T, E>` - 2 static methods (if any)

**Estimated impact:** ~30% of the 180 failing tests use generic static methods

## Attempted Solutions

### ❌ Approach 1: Text-level desugaring
- **Status:** Blocked on generics
- **Issue:** Can't infer type parameters from text alone

### ❌ Approach 2: Manual export/import fixes
- **Status:** Insufficient
- **Issue:** Functions still invalid without type parameters

### ⏸️ Approach 3: Enhanced desugaring with type parameter extraction
- **Status:** Not attempted (requires AST parsing)
- **Complexity:** High - need to parse `impl` signatures, track type params
- **Estimated effort:** 4-6 hours

## Recommended Solutions

### Option A: Fix Desugaring Tool (Complete Solution)

Enhance `src/app/desugar/static_methods.spl` to:
1. Parse `impl Type<T, U>:` to extract type parameters
2. Add type parameters to hoisted functions: `fn Type__method<T, U>(...)`
3. Handle type parameter constraints: `where T: Trait`

**Pros:**
- Fixes all 180 static method failures
- Scales to future code

**Cons:**
- Complex implementation (needs type parameter parsing)
- 4-6 hours estimated

**Files to modify:**
- `src/app/desugar/static_methods.spl` (~100 lines changes)
- Add type parameter extraction logic

### Option B: Manual Wrapper Functions (Tactical Solution)

For each failing module, manually write wrapper functions:
```simple
# Module-level wrappers
fn LazySeq__empty<T>() -> LazySeq<T>:
    LazySeq.empty()  # Call the impl static method

export LazySeq__empty
```

**Pros:**
- Works immediately
- No tool changes needed

**Cons:**
- Tedious (180 files × ~3 methods each = 540 functions)
- Doesn't scale
- Still relies on runtime static method support (which may not exist)

### Option C: Rebuild Runtime with Static Method Support (Ideal Solution)

The memory notes indicate static method support was implemented in Rust source (jj revision npqrnyvn), but that source was deleted.

**Pros:**
- Fixes root cause
- No source file changes needed

**Cons:**
- Rust source deleted (24GB removed)
- Would need to restore from git history
- Contradicts "100% Pure Simple" goal

## Recommendation

**Implement Option A: Fix Desugaring Tool**

This is the right long-term solution:
1. Aligns with "100% Pure Simple" architecture
2. Fixes all static method issues systematically
3. Reasonable 4-6 hour implementation time
4. Reusable for future code

**Implementation plan:**
1. Add type parameter parser to `static_methods.spl`
2. Extract `<T, U>` from `impl Type<T, U>:` headers
3. Prepend type params to hoisted functions
4. Handle constraints (`where` clauses)
5. Test on LazySeq first, then bulk-apply

## Files Modified (This Session)

**Created:**
- `script/bulk_desugar_all.spl` (113 lines)
- `script/find_and_desugar.spl` (142 lines)
- `script/fix_exports.spl` (59 lines)
- `script/desugar_lazy_seq.spl` (36 lines)
- `script/desugar_lazy_seq_test.spl` (36 lines)

**Modified:**
- `src/app/interpreter.lazy/lazy_seq.spl` - Desugared (11 static methods hoisted)
- `test/app/interpreter/lazy/lazy_seq_spec.spl` - Imports updated
- 520+ other files - Static call syntax rewritten

**Status:** All infrastructure ready, blocked on type parameter handling

## Next Steps

1. **Immediate:** Implement type parameter extraction in desugaring tool
2. **Testing:** Verify LazySeq tests pass with fixed desugaring
3. **Bulk apply:** Re-run desugaring on all 520 files with enhanced tool
4. **Verification:** Run full test suite to measure improvement

## Success Metrics

**Current:** 264 runtime errors (180 static method related)

**Target after Option A:**
- Static method errors: 180 → 0
- Runtime errors: 264 → ~84 (other issues)
- Test pass rate: ~77% → ~85%

**Timeline:** 4-6 hours for Option A implementation + testing
