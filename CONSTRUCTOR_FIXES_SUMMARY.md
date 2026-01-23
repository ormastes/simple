# Constructor Documentation Fixes - 2026-01-23

## Summary

Fixed critical inconsistencies across constructor documentation to align with actual compiler behavior (verified in `test/lib/std/integration/constructor_spec.spl`).

## Changes Made

### 1. **Fixed Incorrect Syntax (Braces → Parentheses)**

**Issue:** Multiple files used Rust-style brace syntax `Point { x: x, y: y }` for Simple constructors.

**Fix:** Changed all instances to parentheses syntax `Point(x: x, y: y)` which is the correct Simple syntax.

**Files:**
- `doc/guide/constructors.md` - 10+ instances fixed
- `doc/guide/constructors_comparison.md` - Migration guide examples updated

### 2. **Clarified Implicit Static Constructors**

**Issue:** Documentation wasn't clear that `fn new()` is **implicitly static** at module level.

**Fix:** Added clarifying comments in:
- `doc/guide/constructors.md` - Added comment explaining implicit static behavior
- `doc/guide/constructors_comparison.md` - Updated to show `fn new()` is implicitly static

### 3. **Emphasized Direct Construction as PRIMARY**

**Issue:** Many docs only showed `.new()` approach, not the simpler direct `Type(args)` syntax.

**Fix:** Reordered examples to show:
1. **✅ PRIMARY:** `Point(3, 4)` - Direct construction (zero boilerplate)
2. **✅ OPTIONAL:** `Point.new(3, 4)` - When custom logic needed

### 4. **Updated Comparison Tables**

Fixed all comparison tables to show Simple's dual-syntax approach:

**Before:**
```
| Constructor call | `Type.new()` |
```

**After:**
```
| Constructor call | `Type(args)` (primary) or `Type.new(args)` |
```

Tables fixed in:
- Simple vs Python comparison
- Simple vs Ruby comparison
- Simple vs Rust comparison
- Simple vs JavaScript comparison

## Verified Behavior

All fixes align with actual compiler behavior confirmed in:
- `test/lib/std/integration/constructor_spec.spl` lines 26-75

### Key Facts from Tests:
- ✅ Direct construction `Point(5, 6)` works at module level
- ✅ `fn new()` is implicitly static at module level (no `static` keyword needed)
- ✅ Explicit `static fn new()` still works (optional)
- ✅ Both direct and `.new()` can coexist
- ✅ Named parameters work: `Point(x: 7, y: 8)`
- ✅ Auto-recognized names like `from_*()`, `with_*()`, `create()`, `default()` are implicitly static

## Files Modified

1. `doc/guide/constructors.md` - Complete constructor patterns documentation
2. `doc/guide/constructors_comparison.md` - Language comparison and migration guides
3. `CLAUDE.md` - Already correct, no changes needed

## Documentation Consistency

- **CLAUDE.md:** Shows correct syntax ✅
- **constructors.md:** Now shows correct patterns ✅
- **constructors_comparison.md:** Now shows correct patterns ✅
- **CONSTRUCTOR_QUICK_REF.md:** Already correct ✅
- **constructor_patterns.md:** Already correct ✅
- **constructor_spec.spl:** Source of truth for behavior ✅

## Migration Guides Updated

All migration guides (Python, Ruby, Rust, JavaScript) now show:
- Correct parentheses syntax for Simple constructors
- Note about direct construction alternative
- Implicit static behavior of `fn new()`
