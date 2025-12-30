# BDD Feature Documentation - Session 3: Root Cause Analysis

**Date:** 2025-12-29
**Session:** 3 (Root Cause Discovered)
**Duration:** ~4 hours
**Status:** ❌ BLOCKED - Compiler Bug: __init__.spl Cannot Export Functions

## Summary

Deep investigation into the module export blocker from Session 2. Discovered fundamental limitation in Simple's module system: **`__init__.spl` files can export types but NOT functions**. This is a compiler bug that blocks the BDD feature documentation system.

## Root Cause Discovery 🔍

### The Investigation

**Problem:** Functions defined in `feature_doc/__init__.spl` were not accessible through `import std.spec`, even though types were accessible.

**Steps Taken:**

1. **Attempted Module Flattening** (Session 2 end)
   - Created single-file `feature_doc.spl` with all code
   - ❌ Failed: Simple requires imports even for types in same file
   - Can't use `FeatureMetadata` as parameter type without import
   - **Discovery:** Module separation is REQUIRED, not optional

2. **Restored Modular Structure**
   - Moved back to `feature_doc/` directory with `__init__.spl`
   - Tested individual module files for parse errors

3. **Found Parse Errors in registry.spl**
   ```
   error: compile failed: parse: Unexpected token: expected identifier, found DocComment("Register a feature")
   ```
   - **Cause:** `##` doc comments inside classes not supported by Simple parser
   - **Fix:** Replaced all `##` with `#` in registry.spl
   - **Result:** File now parses successfully ✅

4. **Added Missing `export` Keywords**
   - Functions in `registry.spl` didn't have `export fn`
   - Added `export` to all 7 public functions
   - **Result:** Still not accessible ❌

5. **Fixed __init__.spl Parse Errors**
   - Removed `##` doc comments from `__init__.spl`
   - File now parses without errors ✅
   - **Result:** Functions STILL not accessible ❌

6. **Final Test: Direct __init__.spl Function**
   - Tested `feature_metadata()` defined DIRECTLY in `__init__.spl`
   - Has `export fn` declaration
   - **Result:** `undefined variable: feature_metadata` ❌

### The Smoking Gun

```simple
# In simple/std_lib/src/spec/feature_doc/__init__.spl
export fn feature_metadata(metadata: FeatureMetadata):  # Line 68
    register_feature(metadata)
```

```simple
# Test file
import std.spec

feature_metadata(meta)  # ❌ Error: undefined variable: feature_metadata
```

**But:**

```simple
let x = FeatureMetadata { ... }  # ✅ Works! Type is accessible
```

**Conclusion:** `__init__.spl` exports types successfully, but **does NOT export functions at all**, regardless of `export fn` keyword.

## Evidence

### What Works ✅

- **Types exported from `__init__.spl`:**
  - `FeatureMetadata` (re-exported from `metadata.spl`) ✅
  - `FeatureRegistry` (re-exported from `registry.spl`) ✅

- **Other spec modules:**
  - `describe`, `it`, `expect` from `dsl.spl` ✅
  - `eq`, `be` from `matchers/core.spl` ✅

### What Doesn't Work ❌

- **Functions from feature_doc `__init__.spl`:**
  - `feature_metadata()` (defined directly in `__init__.spl`) ❌
  - `register_feature()` (re-exported from `registry.spl`) ❌
  - `get_feature()` (re-exported from `registry.spl`) ❌
  - **ALL functions** ❌

### Comparison: dsl.spl vs feature_doc/__init__.spl

**dsl.spl (WORKS):**
```simple
# File: simple/std_lib/src/spec/dsl.spl (single file, no __init__.spl)
export fn describe(...):
    ...

export fn it(...):
    ...
```

Usage: `import std.spec` → `describe` and `it` work ✅

**feature_doc/__init__.spl (DOESN'T WORK):**
```simple
# File: simple/std_lib/src/spec/feature_doc/__init__.spl
export fn feature_metadata(...):
    ...
```

Usage: `import std.spec` → `feature_metadata` fails ❌

**Key Difference:** `dsl.spl` is a **single `.spl` file**, `feature_doc` is a **directory with `__init__.spl`**

## Technical Analysis

### Module System Behavior

| Module Type | Types Export | Functions Export |
|-------------|--------------|------------------|
| Single `.spl` file | ✅ Yes | ✅ Yes |
| Directory with `__init__.spl` | ✅ Yes | ❌ **NO** |

### Hypothesis

The Simple compiler's module resolution logic:

1. ✅ Correctly processes type exports from `__init__.spl`
2. ❌ **FAILS** to register function exports from `__init__.spl`
3. ✅ Works correctly for single-file modules (e.g., `dsl.spl`)

This appears to be a **compiler bug** in the module system's export handling for `__init__.spl` files.

## Code Changes Summary

### Files Modified (3 files)

1. **simple/std_lib/src/spec/feature_doc/registry.spl**
   - Replaced all `##` doc comments with `#` (18 occurrences)
   - Added `export fn` to 7 public functions
   - Lines changed: ~25

2. **simple/std_lib/src/spec/feature_doc/__init__.spl**
   - Replaced all `##` doc comments with `#` (12 occurrences)
   - Lines changed: ~12

3. **simple/std_lib/src/spec/feature_doc_old/** (backup, deleted after restoration)

### Files Created for Testing

- `/tmp/test_use2.spl` - Test struct literal + register_feature
- `/tmp/test_registry.spl` - Test direct registry import
- `/tmp/test_direct_import.spl` - Test module import
- `/tmp/test_registry_func.spl` - Test module.function syntax
- `/tmp/test_use_func.spl` - Test use statement
- `/tmp/test_feature_metadata.spl` - Test __init__.spl function
- `/tmp/test_comment.spl` - Test ## comment syntax
- `/tmp/test_type_ref.spl` - Test forward type reference
- `/tmp/test_export_class.spl` - Test export class syntax

## Lessons Learned

1. **Simple Requires Type Imports** - Even within the same file, you cannot use a class as a parameter type without importing it. This makes single-file module flattening impossible.

2. **`##` Doc Comments Have Limitations** - Doc comments (`##`) cannot appear:
   - Inside class method definitions
   - Before class methods (causes parse error)
   - Use single `#` comments instead

3. **`__init__.spl` Module Bug** - Directory-based modules with `__init__.spl` can export types but not functions. This is likely a compiler bug.

4. **Export Statement Placement** - Types don't need `export` in source file (can be re-exported in `__init__.spl`), but functions need `export fn` in source file AND re-export in `__init__.spl` (though this still doesn't work due to bug).

5. **Module System Consistency** - Single-file modules (`.spl`) work correctly, directory modules (`__init__.spl`) do not export functions.

## Workarounds

### Option 1: Move to Single File (Not Viable)

**Attempt:** Create single `feature_doc.spl` file
**Result:** ❌ Cannot use `FeatureMetadata` type in `FeatureRegistry.register(feature: FeatureMetadata)` without import
**Conclusion:** Single-file approach impossible due to forward reference requirements

### Option 2: Inline in spec/__init__.spl (Possible)

**Approach:** Move ALL feature_doc code directly into `spec/__init__.spl`
**Pros:**
- `spec/__init__.spl` already exports functions successfully
- Would avoid nested `__init__.spl` issue

**Cons:**
- Massive file (800+ lines in already large file)
- Poor code organization
- Defeats purpose of modular design

**Estimated Effort:** 2-3 hours

### Option 3: Use Single .spl File Per Module (Recommended Temporary Fix)

**Approach:** Create `spec/feature_metadata.spl`, `spec/feature_registry.spl`, etc. as single files (not directory)
**Pros:**
- Single `.spl` files export functions correctly
- Maintains some modularity
- Clean imports: `import std.spec.feature_metadata`

**Cons:**
- Can't group related files in subdirectory
- Namespace pollution in `spec/` directory

**Estimated Effort:** 1-2 hours

### Option 4: Wait for Compiler Fix (Recommended Long-term)

**Approach:** File bug report, wait for Simple compiler fix
**Bug Location:** Module resolver's handling of `__init__.spl` function exports
**Expected Fix:** Update compiler to properly register function exports from `__init__.spl`

**Estimated Time:** Unknown (depends on compiler development priority)

## Comparison: Sessions 1-3

| Aspect | Session 1 | Session 2 | Session 3 |
|--------|-----------|-----------|-----------|
| **Blocker** | Named args | Module exports | Compiler bug |
| **Severity** | Medium | High | **Critical** |
| **Workaround** | Struct literals ✅ | Unknown | Single-file modules |
| **Root Cause** | Missing feature | Module system? | **Compiler bug** |
| **Fix Location** | Parser | Module system | **Module resolver** |
| **Est. Fix Time** | 6-9 hours | 2-4 hours | **Requires compiler patch** |

## Next Steps

### Immediate (Session 4):

1. **File Bug Report** in `simple/bug_report.md`:
   ```markdown
   ### [Module System] __init__.spl does not export functions

   **Type:** Bug
   **Priority:** High
   **Discovered:** 2025-12-29

   **Description:**
   Directory-based modules with `__init__.spl` files can export types but not functions.
   Functions marked with `export fn` in `__init__.spl` are not accessible through imports.

   **Expected:**
   Functions with `export fn` in `__init__.spl` should be importable

   **Actual:**
   `import std.spec` makes types accessible but functions cause "undefined variable" errors

   **Reproduction:**
   See doc/report/BDD_FEATURE_DOC_SESSION3_2025-12-29.md for detailed investigation
   ```

2. **Choose Workaround:**
   - **Recommended:** Option 3 (single .spl files) for now
   - Move `feature_doc/__init__.spl` → `spec/feature_doc.spl`
   - Adjust imports in test files
   - Document as temporary until compiler fixed

3. **Test Workaround:**
   - Verify functions are accessible
   - Update `all_features_spec.spl` to use new import path
   - Run tests to confirm registration works

### Long-term:

4. **Compiler Fix** (future contributor or maintainer):
   - Investigate `src/compiler/src/module_resolver.rs`
   - Check how `__init__.spl` exports are processed vs regular `.spl` files
   - Ensure function exports from `__init__.spl` are registered in symbol table

5. **Resume BDD Documentation** after compiler fix:
   - Restore modular structure with proper `__init__.spl`
   - Complete runtime integration
   - Generate markdown documentation

## Status

**Infrastructure:** ✅ Complete (Phases 1-6)
- Metadata DSL ✅
- Generators ✅
- File writers ✅
- Scaffolding ✅
- Verification ✅

**Runtime Integration:** ❌ **BLOCKED BY COMPILER BUG**
- Struct literal syntax ✅ Working
- Keyword conflicts ✅ Resolved
- Doc comment syntax ✅ Fixed (`##` → `#`)
- Export keywords ✅ Added
- **Module function exports** ❌ **COMPILER BUG**

**Documentation Generation:** ❌ Cannot proceed until module exports work

## Files to Review

**Modified:**
- `simple/std_lib/src/spec/feature_doc/registry.spl` (removed ##, added export fn)
- `simple/std_lib/src/spec/feature_doc/__init__.spl` (removed ##)

**Reports:**
- `doc/report/BDD_FEATURE_DOC_SESSION3_2025-12-29.md` (this file)

**Bug Report:**
- `simple/bug_report.md` (to be created)

---

**Session Status:** ❌ **BLOCKED - Compiler Bug Discovered**
**Infrastructure:** ✅ Complete
**Integration:** ❌ Blocked by Module System Bug
**Recommendation:** File bug report, use single-file workaround temporarily
