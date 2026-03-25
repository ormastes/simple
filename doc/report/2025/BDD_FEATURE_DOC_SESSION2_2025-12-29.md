# BDD Feature Documentation - Session 2: Solving Blockers

**Date:** 2025-12-29
**Session:** 2 (Partial Success - New Blocker Discovered)
**Duration:** ~3 hours
**Status:** ⚠️ New Blocker - Module System Export Issue

## Summary

Attempted to solve the named argument syntax blocker from Session 1. Successfully implemented struct literal workaround, but discovered a deeper blocker: the Simple module system doesn't properly export functions from nested modules.

## Achievements ✅

### 1. Named Arguments Workaround - Struct Literals
**Discovered:** Simple supports struct literal syntax with `{ field: value }`

**Proof:**
```simple
class Point:
    x: Int
    y: Int

let p = Point { x: 10, y: 20 }  # ✅ This works!
```

### 2. API Refactoring
**Changed:** `feature_metadata()` to accept `FeatureMetadata` object instead of individual parameters

**Before:**
```simple
# ❌ Didn't work - named args in function calls not supported
feature_metadata(
    id: 1,
    name: "Lexer",
    ...
)
```

**After:**
```simple
# ✅ Struct literals work!
register_feature(FeatureMetadata {
    id: 1,
    name: "Lexer",
    category: "Infrastructure",
    difficulty: 3,
    status: "✅ Complete",
    impl_type: "Rust",
    spec_ref: "spec/lexer_parser.md",
    files: ["src/parser/src/lexer/mod.rs"],
    tests: ["src/parser/tests/lexer_tests.rs"],
    description: "Tokenizes Simple language source code into tokens",
    code_examples: [],
    dependencies: [],
    required_by: [2],
    notes: "First stage of compilation pipeline"
})
```

### 3. Keyword Conflict Resolution
**Problem:** `examples` field conflicted with `examples` function from `std.spec.gherkin`

**Solution:** Renamed field to `code_examples` throughout codebase

**Files Modified:**
- `simple/std_lib/src/spec/feature_doc/metadata.spl`
- `simple/std_lib/src/spec/feature_doc.spl`
- `simple/std_lib/test/features/all_features_spec.spl`

### 4. Module Structure Fixes
**Actions Taken:**
- Moved `feature_doc.spl` content into `feature_doc/__init__.spl`
- Fixed import paths from `feature_doc.X` to just `X`
- Added `export fn` for all public functions
- Created proper module initialization

**Files Created/Modified:**
- `simple/std_lib/src/spec/feature_doc/__init__.spl` (moved from feature_doc.spl)
- Updated imports: `from metadata` instead of `from feature_doc.metadata`

## New Blocker Discovered ❌

### Module System Function Export Issue

**Problem:** Functions defined in `feature_doc/__init__.spl` are NOT accessible through imports, even though types ARE accessible.

**Evidence:**

**✅ Types Work:**
```simple
import std.spec

let meta = FeatureMetadata {  # ✅ This works!
    id: 1,
    ...
}
```

**❌ Functions Don't Work:**
```simple
import std.spec

feature_metadata(...)  # ❌ Error: undefined variable: feature_metadata
register_feature(...)  # ❌ Error: undefined variable: register_feature
```

**Export Attempts (All Failed):**
1. Separate `export` statements at end of file
2. Inline `export fn` declarations
3. Re-export in `spec/__init__.spl` with `export feature_metadata from feature_doc`
4. Direct import: `use std.spec.feature_doc.registry.register_feature`

**None of these make the functions accessible!**

### Investigation Results

**What Works:**
- ✅ `FeatureMetadata` type is accessible
- ✅ `FeatureRegistry` type is accessible
- ✅ Sub-module imports work: `import std.spec.feature_doc.registry`
- ✅ Functions from other spec modules work: `describe`, `expect`, `it`

**What Doesn't Work:**
- ❌ `feature_metadata()` function
- ❌ `register_feature()` function
- ❌ `get_global_registry()` function
- ❌ ANY function from `feature_doc` module

**Hypothesis:** The `feature_doc` module has a compilation error that prevents its functions from being registered, but allows its types to be accessible. OR the module system doesn't properly handle function exports from nested modules with `__init__.spl` files.

## Code Changes Summary

### Files Modified (8 files)
1. **simple/std_lib/src/spec/feature_doc/metadata.spl**
   - Changed `examples: List[String]` → `code_examples: List[String]`
   - Changed constructor to use `{ }` instead of `( )`

2. **simple/std_lib/src/spec/feature_doc/__init__.spl** (moved from feature_doc.spl)
   - Moved entire content from `feature_doc.spl`
   - Updated imports: `from metadata` instead of `from feature_doc.metadata`
   - Added `export fn` for all public functions
   - Fixed paths in `use` statements

3. **simple/std_lib/src/spec/feature_doc.spl**
   - Deleted (moved to `__init__.spl`)

4. **simple/std_lib/test/features/all_features_spec.spl**
   - Changed `examples: []` → `code_examples: []` (4 occurrences)
   - Changed `feature_metadata(...)` → `register_feature(...)`
   - Added `FeatureMetadata { }` struct literal syntax

5. **doc/report/BDD_FEATURE_DOC_BLOCKER_2025-12-29.md**
   - Created comprehensive blocker analysis
   - Documented 3 solution options

6. **doc/features/feature.md**
   - Updated with BDD system documentation

### Lines Changed
- ~50 lines modified across metadata, __init__, test files
- ~100 lines in new documentation

## Technical Details

### Struct Literal Discovery
Tested and confirmed that Simple supports:
```simple
ClassName { field1: value1, field2: value2, ... }
```

This works for:
- Multi-line struct literals ✅
- Empty list fields `[]` ✅
- Nested struct construction ✅
- Fields with same name as exported functions ✅ (after rename)

### Module System Behavior

**Working Pattern (from `dsl.spl`):**
```simple
export fn describe(desc: String, block: Fn() -> Void):
    # function body
```

**Our Pattern (NOT working):**
```simple
# In feature_doc/__init__.spl
export fn feature_metadata(metadata: FeatureMetadata):
    register_feature(metadata)
```

**Difference:** `dsl.spl` is a single file, `feature_doc/__init__.spl` is inside a directory with submodules.

## Next Steps

### Option 1: Debug Module System (Recommended)
**Investigation needed:**
1. Check if `__init__.spl` files can export functions at all
2. Test with minimal example: single function in `__init__.spl`
3. Compare working modules (dsl, matchers) vs non-working (feature_doc)
4. Check for compilation errors in feature_doc modules

**Estimated Time:** 2-4 hours

### Option 2: Inline Everything (Workaround)
**Flatten the module structure:**
- Move all code from `metadata.spl`, `registry.spl`, etc. into single file
- Remove `__init__.spl` and subdirectories
- Define everything in `feature_doc.spl` as single module

**Pros:** Might work if issue is with `__init__.spl` exports
**Cons:** Loses modular organization, ~800 lines in one file

**Estimated Time:** 1-2 hours

### Option 3: Rust Implementation (Long-term)
**Implement feature documentation in Rust:**
- Parse .spl test files in Rust
- Extract metadata from comments/annotations
- Generate markdown from Rust

**Pros:** Avoids Simple module system entirely
**Cons:** Defeats purpose of self-hosted Simple tools

**Estimated Time:** 8-12 hours

## Comparison: Session 1 vs Session 2

| Aspect | Session 1 | Session 2 |
|--------|-----------|-----------|
| **Blocker** | Named argument syntax | Module function exports |
| **Severity** | Medium | High |
| **Workaround Available** | Yes (struct literals) | Unknown |
| **Root Cause** | Missing language feature | Module system bug? |
| **Files Affected** | API design | Runtime behavior |
| **Est. Fix Time** | 6-9 hours | 2-4 hours (investigation) + fix |

## Lessons Learned

1. **Struct Literals Work:** Simple DOES support `{ field: value }` syntax for class construction - this is valuable!

2. **Keyword Conflicts Are Real:** Be careful with field names that might conflict with exported functions

3. **Module System Is Complex:** Function exports from `__init__.spl` don't work the same as from regular `.spl` files

4. **Types vs Functions:** The module system treats type exports differently from function exports

5. **Testing is Critical:** Can't assume module exports work without testing import paths

## Status

**Infrastructure:** ✅ Complete (Phases 1-6)
- Metadata DSL ✅
- Generators ✅
- File writers ✅
- Scaffolding ✅
- Verification ✅

**Runtime Integration:** ❌ Blocked
- Struct literal syntax ✅ Working
- Keyword conflicts ✅ Resolved
- Module exports ❌ **NEW BLOCKER**

**Documentation Generation:** ❌ Cannot proceed until module exports work

## Files to Review

**Modified:**
- `simple/std_lib/src/spec/feature_doc/__init__.spl`
- `simple/std_lib/src/spec/feature_doc/metadata.spl`
- `simple/std_lib/test/features/all_features_spec.spl`

**Reports:**
- `doc/report/BDD_FEATURE_DOC_BLOCKER_2025-12-29.md`
- `doc/report/BDD_FEATURE_DOC_SESSION2_2025-12-29.md` (this file)

---

**Session Status:** ⚠️ Partial Progress - New Blocker
**Infrastructure:** ✅ Complete
**Integration:** ❌ Blocked by Module System
**Recommendation:** Investigate `__init__.spl` function export behavior before proceeding
