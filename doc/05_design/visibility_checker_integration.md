# Visibility Checker Integration Guide

**Status:** Framework Complete, Integration Pending
**Date:** 2026-02-05

---

## Overview

The visibility checker framework (`src/compiler/visibility_checker.spl`) is complete and ready for integration. This document describes how to integrate it into the compiler's symbol resolution system.

---

## What's Complete

✅ **Visibility Checker Module** (`visibility_checker.spl`)
- `VisibilityWarning` struct - Warning data structure
- `VisibilityChecker` class - Checks cross-module access
- `check_and_warn()` helper - Integration point
- Warning formatting (W0401 code)

✅ **Filename Matching** (`visibility.spl`)
- `effective_visibility()` - Computes final visibility
- Already integrated into HIR lowering

✅ **HIR Visibility Tracking**
- All HIR types have `is_public: bool`
- Computed during lowering using filename matching

---

## What Remains

### Challenge: Module Context Tracking

**Problem:** The current `SymbolTable` doesn't track which module each symbol belongs to.

**Current Structure:**
```simple
struct Symbol:
    id: SymbolId
    name: text
    kind: SymbolKind
    type_: HirType?
    scope: ScopeId
    span: Span
    is_public: bool      # ✅ We have this
    is_mutable: bool
    # ❌ Missing: module_path or module_id
```

**Needed:**
```simple
struct Symbol:
    # ... existing fields ...
    defining_module: text?   # Which module defined this symbol
```

### Integration Points

There are three main places where cross-module symbol access happens:

#### 1. Import Resolution

**File:** `src/compiler/hir_lowering/items.spl` (or import resolver)

**Current:**
```simple
# When resolving imports
use module.SomeType
```

**Needed:**
```simple
# After resolving import
val symbol = resolve_imported_symbol("module", "SomeType")
if symbol.?:
    val sym = symbol.unwrap()
    # ⚠️ Check visibility here
    check_and_warn(visibility_checker, sym, "module.spl", current_span)
```

#### 2. Qualified Name Resolution

**File:** Symbol resolution during type checking

**Current:**
```simple
# Using qualified names
val x: other_module.TypeName = ...
```

**Needed:**
```simple
# After looking up qualified name
val symbol = lookup_qualified("other_module", "TypeName")
if symbol.?:
    # ⚠️ Check visibility here
    check_and_warn(visibility_checker, symbol.unwrap(), "other_module.spl", span)
```

#### 3. Method Resolution

**File:** `src/compiler/resolve.spl`

**Current:**
```simple
# Method calls on types from other modules
val obj: OtherType = ...
obj.method()  # method defined in other module
```

**Needed:**
```simple
# After resolving method
if method_symbol.is_from_other_module():
    # ⚠️ Check visibility here
    check_and_warn(visibility_checker, method_symbol, source_module, span)
```

---

## Implementation Strategy

### Phase 1: Add Module Tracking to Symbol (2-3 hours)

1. **Update `Symbol` struct** in `src/compiler/hir_types.spl`:
   ```simple
   struct Symbol:
       # ... existing fields ...
       defining_module: text?   # NEW: Which module defined this
   ```

2. **Update `define()` method** in `SymbolTable`:
   ```simple
   fn define(
       name: text,
       kind: SymbolKind,
       type_: HirType?,
       span: Span,
       is_public: bool,
       is_mutable: bool,
       module: text?   # NEW parameter
   ) -> SymbolId
   ```

3. **Update all call sites** of `define()` to pass module name:
   - In HIR lowering: pass `self.module_filename`
   - In other places: pass appropriate module path

### Phase 2: Integrate Visibility Checker (2-3 hours)

1. **Add `VisibilityChecker` to compilation context**:
   ```simple
   # In driver.spl or compilation_context.spl
   struct CompilationContext:
       # ... existing fields ...
       visibility_checker: VisibilityChecker
   ```

2. **Initialize checker** with current module:
   ```simple
   val context = CompilationContext(
       # ...
       visibility_checker: VisibilityChecker.new(module_filename)
   )
   ```

3. **Add checks at resolution points** (see Integration Points above)

### Phase 3: Wire Up Diagnostics (1-2 hours)

1. **Add warnings to diagnostic output**:
   ```simple
   # After compilation
   for warning in context.visibility_checker.get_warnings():
       print warning.format()
   ```

2. **Add warning counts to compilation stats**

3. **Test warning output** with sample files

---

## Testing Plan

### Unit Tests

Create test cases in `test/compiler/visibility_checker_spec.spl`:

```simple
describe "VisibilityChecker":
    it "allows same-module access":
        val checker = VisibilityChecker.new("test.spl")
        val symbol = Symbol(/* ... is_public: false ... */)
        val warning = checker.check_symbol_access(symbol, "test.spl", span)
        expect not warning.?

    it "allows cross-module public access":
        val checker = VisibilityChecker.new("test.spl")
        val symbol = Symbol(/* ... is_public: true ... */)
        val warning = checker.check_symbol_access(symbol, "other.spl", span)
        expect not warning.?

    it "warns on cross-module private access":
        val checker = VisibilityChecker.new("test.spl")
        val symbol = Symbol(/* ... is_public: false ... */)
        val warning = checker.check_symbol_access(symbol, "other.spl", span)
        expect warning.?
        expect warning.unwrap().code == "W0401"
```

### Integration Tests

Use test fixtures from `test/system/features/module_visibility/`:

```
test/fixtures/
  visibility_test/
    test_case.spl      # Has TestCase (auto-public) and Helper (private)
    other.spl          # Tries to use Helper
```

**Expected behavior:**
```bash
$ simple compile test/fixtures/visibility_test/other.spl

WARNING[W0401]: Accessing private type 'Helper' from module 'other.spl'
  --> test_case.spl
   |
   | Symbol 'Helper' is not exported
   |
   = note: Type doesn't match filename and lacks 'pub' modifier
   = help: Add 'pub class Helper' in test_case.spl to export it
   = note: This will become an error in a future release

Compilation successful (1 warning)
```

---

## Example Integration

### Before (Current):

```simple
# In symbol resolution code
val sym_id = symbol_table.lookup(name)
if sym_id.?:
    val symbol = symbol_table.get(sym_id.unwrap())
    # Use symbol...
```

### After (With Visibility Check):

```simple
# In symbol resolution code
val sym_id = symbol_table.lookup(name)
if sym_id.?:
    val symbol = symbol_table.get(sym_id.unwrap()).unwrap()

    # ⚠️ NEW: Check visibility if cross-module access
    if symbol.defining_module.? and symbol.defining_module.unwrap() != current_module:
        check_and_warn(
            context.visibility_checker,
            symbol,
            symbol.defining_module.unwrap(),
            current_span
        )

    # Use symbol...
```

---

## Estimated Effort

| Phase | Task | Effort |
|-------|------|--------|
| 1 | Add module tracking to Symbol | 2-3h |
| 2 | Integrate VisibilityChecker | 2-3h |
| 3 | Wire up diagnostics | 1-2h |
| **Total** | | **5-8h** |

---

## Alternative: Simplified Approach

If full module tracking is too complex, we can use a **simpler heuristic**:

1. **Track imports**: Keep a set of imported symbols
2. **Check on use**: If symbol is used and not imported, warn
3. **Assumption**: Non-imported symbols are from current module

**Pros:**
- Much simpler to implement (2-3 hours total)
- Doesn't require Symbol struct changes
- Still catches most visibility violations

**Cons:**
- May miss some edge cases
- Less accurate than full tracking

**Implementation:**
```simple
class SimpleVisibilityChecker:
    imported_symbols: Set<text>     # Track what was imported
    public_symbols: Set<text>       # Track public symbols

    fn check_use(symbol_name: text) -> bool:
        # If not imported and not in public set -> warn
        not self.imported_symbols.contains(symbol_name) and
        not self.public_symbols.contains(symbol_name)
```

---

## Decision

**Recommendation:** Start with simplified approach for MVP, then enhance with full module tracking if needed.

**Rationale:**
- Gets warnings working quickly (2-3 hours)
- Can iterate based on real usage
- Full tracking can be added incrementally

---

## Next Steps

1. **Choose approach** (full vs. simplified)
2. **Implement chosen strategy**
3. **Add unit tests**
4. **Test with real code**
5. **Gather feedback**
6. **Iterate**

---

**Status:** Ready for implementation
**Blocker:** None (framework complete)
**Owner:** TBD
