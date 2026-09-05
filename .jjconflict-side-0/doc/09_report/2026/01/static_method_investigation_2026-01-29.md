# Static Method Call Investigation - Session Report
**Date:** 2026-01-29
**Status:** Root Cause Found, Fix Implemented, Testing Blocked

---

## Summary

Identified and fixed the root cause of "unsupported path call" errors when calling static methods like `LspServer.new()`. The issue was that freshly loaded modules weren't merging their class definitions into the caller's scope, only caching them for future use.

---

## Root Cause Analysis

### The Bug

In `src/rust/compiler/src/interpreter_module/module_loader.rs`, function `load_and_merge_module`:

**When loading from cache (line 264):**
```rust
// Merge cached definitions (classes, functions, enums) into caller's HashMaps
// This ensures that static method calls work on imported classes
merge_cached_module_definitions(&module_path, classes, functions, enums);
```

**When loading fresh (lines 327-398):**
```rust
// Evaluate the module
let (module_env, module_exports, module_functions, module_classes, module_enums) =
    evaluate_module_exports(&module.items, Some(&module_path), functions, classes, enums)?;

// Cache the definitions
cache_module_definitions(&module_path, &module_classes, &module_functions, &module_enums);

// ❌ BUG: Definitions are cached but NOT merged into caller's scope!
// Return exports without merging classes/functions/enums
```

### Impact

- **First import of a module:** Classes are cached but NOT available for static method calls
- **Subsequent imports:** Classes ARE available (loaded from cache via `merge_cached_module_definitions`)
- **Result:** Inconsistent behavior - static methods work after the first import in a different module, but not on first use

### Error Manifestation

When calling `LspServer.new()` from a test:
1. Module `app.lsp.server` is loaded for the first time
2. `LspServer` class is evaluated and cached
3. **BUT** `LspServer` is NOT added to the `classes` HashMap in caller's scope
4. When `evaluate_call` tries to resolve `LspServer.new()`, it checks the `classes` HashMap (line 346)
5. `LspServer` is not found → falls through to error (line 368-374)
6. Error: "unsupported path call: ["LspServer", "new"]"

---

## The Fix

**File:** `src/rust/compiler/src/interpreter_module/module_loader.rs`
**Location:** After line 373 (after `cache_module_definitions`)

```rust
// Also cache the module definitions (classes, functions, enums) for future imports
cache_module_definitions(&module_path, &module_classes, &module_functions, &module_enums);

// Merge freshly loaded definitions into caller's scope (same as cache case on line 264)
// This ensures static method calls work on imported classes
for (name, class_def) in &module_classes {
    classes.insert(name.clone(), class_def.clone());
}
for (name, func_def) in &module_functions {
    if name != "main" {  // Don't add "main" from imported modules
        functions.insert(name.clone(), func_def.clone());
    }
}
for (name, enum_def) in &module_enums {
    enums.insert(name.clone(), enum_def.clone());
}

// Clear partial exports now that full exports are available
clear_partial_module_exports(&module_path);
```

### Why This Works

1. **Mirrors cache behavior:** Uses same logic as `merge_cached_module_definitions` (lines 177-211 in `module_cache.rs`)
2. **Makes behavior consistent:** Both fresh and cached loads now merge definitions
3. **Enables static method resolution:** Classes are in the `classes` HashMap that `evaluate_call` checks
4. **Zero breaking changes:** Only adds missing functionality, doesn't change existing behavior

---

## Testing Status

### Fix Applied

✅ Fix implemented in `src/rust/compiler/src/interpreter_module/module_loader.rs`

### Testing Blocked

❌ Cannot rebuild due to pre-existing build errors (207 errors)

The codebase has pre-existing compilation errors unrelated to this fix:

```
error[E0308]: mismatched types
   --> src/rust/compiler/src/interpreter_call/block_execution.rs:425:105
    |
425 |             block_execution::exec_block_closure(&nodes, &mut captured_clone, functions, classes, enums, impl_methods)
    |                                                                                                    ^^^^^^^^^^^^ types differ in mutability
    |
    = note: expected mutable reference `&mut std::collections::HashMap<_, _>`
                       found reference `&std::collections::HashMap<_, _>`
```

**Root cause of build errors:** Recent changes to `block_execution.rs` added a `Node::Impl` case that needs to mutate `impl_methods`, but function signatures throughout the codebase pass `impl_methods` as immutable (`&ImplMethods` instead of `&mut ImplMethods`).

**Scope:** Affects 207+ call sites across the entire codebase

---

## Code Paths Involved

### Import Flow

1. **User code:** `use app.lsp.server.{LspServer, ServerState}`
2. **Parser:** Creates `UseStmt` node
3. **evaluate_module_impl:** Encounters `Node::UseStmt` (line 745 in `interpreter_eval.rs`)
4. **load_and_merge_module:** Resolves module path, loads file, evaluates it
   - **Before fix:** Caches but doesn't merge definitions
   - **After fix:** Caches AND merges definitions
5. **evaluate_call:** Resolves `LspServer.new()` by checking `classes` HashMap
   - **Before fix:** `LspServer` not in HashMap → error
   - **After fix:** `LspServer` in HashMap → finds static method → success

### Static Method Resolution

Path in `evaluate_call` (lines 294-375 in `interpreter_call/mod.rs`):

1. Check if callee is a Path expression (line 295)
2. Check if it has 2 segments (line 296): `["LspServer", "new"]`
3. Check enum variants (lines 301-327) - not a match
4. **Check impl methods** (lines 330-343) - looks in `impl_methods` HashMap
5. **Check class static methods** (lines 345-359) - looks in `classes` HashMap ← **Fix makes this work**
6. Legacy fallbacks (lines 362-366)
7. Error if nothing matches (lines 368-374)

---

## Files Modified

1. `src/rust/compiler/src/interpreter_module/module_loader.rs` - Added definition merging after line 373

---

## Next Steps

### To Test the Fix

1. **Fix pre-existing build errors:** Update all function signatures to accept `&mut ImplMethods` instead of `&ImplMethods`
   - Affects ~207 call sites
   - Or: Revert the `Node::Impl` case in `block_execution.rs` temporarily

2. **Rebuild:** `cargo build --release`

3. **Test static method calls:**
   ```bash
   ./target/release/simple_old /tmp/test_lsp_import.spl
   ```

   Expected output:
   ```
   LspServer imported successfully!
   Server state: Uninitialized
   ```

4. **Run LSP tests:**
   ```bash
   ./target/release/simple_old test test/lib/std/unit/lsp
   ```

   Expected: 390/390 tests passing (up from 310/390)

### Alternative: Minimal Test

Create a simpler test case that doesn't depend on LSP:

```simple
# test_static_methods.spl
class Point:
    x: i64
    y: i64

    static fn origin() -> Point:
        Point(x: 0, y: 0)

# In another file that imports Point:
use test_static_methods.Point

val p = Point.origin()  # Should work after fix
print("Point: ({p.x}, {p.y})")
```

---

## Related Issues

### Stdlib Parse Errors (Fixed)

This investigation began with 80 failing LSP tests. The parse errors in 4 stdlib modules have been fixed:
- ✅ sys.spl - Attribute syntax
- ✅ dsl.spl - Variadic parameter
- ✅ resource_registry.spl - Pass keyword
- ✅ leak_tracked.spl - Var in mixin

However, fixing parse errors revealed the deeper static method call issue.

### Pre-existing Build Issues

The codebase currently has compilation errors unrelated to this investigation:
- 207 errors related to `impl_methods` mutability
- Recent addition of `Node::Impl` handling in `block_execution.rs`
- Needs systematic update of function signatures OR revert of recent changes

---

## Verification Strategy

Once build issues are resolved:

1. **Unit test:** Static method calls in isolated module
2. **Integration test:** LSP server initialization
3. **Regression test:** All existing tests still pass
4. **LSP test suite:** 390/390 passing

---

## Confidence Level

**High** - The fix is:
- ✅ Minimal (14 lines added)
- ✅ Mirrors existing working code (`merge_cached_module_definitions`)
- ✅ Addresses exact root cause (missing merge step)
- ✅ No API changes
- ✅ Consistent with cache behavior

**Blocked by:** Pre-existing build errors preventing compilation and testing.
