# Decorator Module Failure Analysis
**Date:** 2026-01-30
**Tests:** 0/7 passing

## Failure Categories

### Category 1: Mutability Issues (5/7 failures)

**Classes affected:**
- CachedFunction (3 tests)
- DeprecatedFunction (2 tests)

**Error:** `cannot modify self.X in immutable fn method`

**Root cause:** Methods declared as `fn` cannot modify instance fields

**Solution:** Change `fn` to `me` for methods that modify state

**Files to fix:**
- `src/lib/std/src/compiler_core/decorators.spl`

**Specific methods:**
1. CachedFunction.__call__ - modifies `self.misses`
2. Deprecated Function.__call__ - modifies `self.warned`

---

### Category 2: Field Access Issues (2/7 failures)

**Class affected:**
- LoggedFunction (2 tests)

**Error:** `method 'func' not found on type 'LoggedFunction'`

**Root cause:** Field access syntax issue or missing field

**Investigation needed:** Check LoggedFunction class definition

---

## Fix Plan

### Step 1: Fix Mutability (5 tests)
Change immutable `fn` to mutable `me` in:
- `CachedFunction.__call__`
- `DeprecatedFunction.__call__`

### Step 2: Fix Field Access (2 tests)
Investigate and fix `LoggedFunction.func` access

---

**Expected outcome:** 7/7 tests passing after fixes
