# Module Export Fixes - 2026-02-03

## Executive Summary

Fixed missing module declarations causing "Export statement references undefined symbol" warnings across the codebase. All modules now properly declare their submodules before exporting them.

## Root Cause

Several `__init__.spl` files were exporting submodules without declaring them with `mod` statements. This caused the module loader to fail finding the exported symbols.

**Pattern:**
```simple
# ❌ BROKEN - Export without declaration
export treesitter

# ✅ FIXED - Declare then export
mod treesitter
export treesitter
```

## Fixes Applied

### 1. Parser Module ✅ FIXED

**File:** `rust/lib/std/src/parser/__init__.spl`

**Issue:** Exported `treesitter` and `error_recovery.CommonMistake` without mod declarations

**Fix:**
```simple
# Before
mod parser
# ... (missing mod declarations)
export error_recovery.CommonMistake
export treesitter

# After
mod parser
mod treesitter
mod error_recovery

export error_recovery.CommonMistake
export treesitter
```

**Impact:** Parser tests no longer show "undefined symbol name=treesitter" warning

### 2. TreeSitter Module ✅ FIXED

**File:** `rust/lib/std/src/parser/treesitter/__init__.spl`

**Issue:** Exported `edits` without mod declaration

**Fix:**
```simple
# Before
mod treesitter
# ... (missing mod edits)
export edits

# After
mod treesitter
mod edits

export edits
```

**Impact:** TreeSitter incremental parsing tests no longer show "undefined symbol name=edits" warning

### 3. ML Module ✅ FIXED

**File:** `rust/lib/std/src/ml/__init__.spl`

**Issue:** Exported `torch` without mod declaration

**Fix:**
```simple
# Before
mod ml
export torch

# After
mod ml
mod torch

export torch
```

**Impact:** ML/tensor tests no longer fail to load torch module

### 4. Torch Module ✅ FIXED

**File:** `rust/lib/std/src/ml/torch/__init__.spl`

**Issue:** Exported `device`, `dtype`, and `tensor_ffi` without mod declarations

**Fix:**
```simple
# Before
mod torch
use device.{Device}
use dtype.{DType}
export device
export dtype
export tensor_ffi

# After
mod torch
mod device
mod dtype
mod tensor_ffi

use device.{Device}
use dtype.{DType}

export device
export dtype
export tensor_ffi
```

**Impact:** ML tests no longer show "undefined symbol name=tensor_ffi" warning

## Pattern Applied

For all module `__init__.spl` files:

```simple
# Step 1: Declare all submodules
mod submodule1
mod submodule2
mod submodule3

# Step 2: Import from submodules if needed
use submodule1.{Type1}
use submodule2.{Type2}

# Step 3: Export submodules
export submodule1
export submodule2
export submodule3

# Step 4: Re-export types from submodules if needed
export submodule1.Type1
```

## Test Results

### Before Fixes

```
[WARN] Export statement references undefined symbol name=treesitter
[WARN] Export statement references undefined symbol name=edits
[WARN] Export statement references undefined symbol name=tensor_ffi
```

### After Fixes

No warnings about undefined symbols for:
- ✅ `treesitter` - Parser module loads correctly
- ✅ `edits` - TreeSitter edits module loads correctly
- ✅ `tensor_ffi` - ML tensor FFI module loads correctly
- ✅ `error_recovery` - Parser error recovery module loads correctly
- ✅ `device`, `dtype` - Torch device/dtype modules load correctly

## Summary of Changes

| File | Modules Added | Exports Fixed |
|------|---------------|---------------|
| `rust/lib/std/src/parser/__init__.spl` | `treesitter`, `error_recovery` | 2 |
| `rust/lib/std/src/parser/treesitter/__init__.spl` | `edits` | 1 |
| `rust/lib/std/src/ml/__init__.spl` | `torch` | 1 |
| `rust/lib/std/src/ml/torch/__init__.spl` | `device`, `dtype`, `tensor_ffi` | 3 |

**Total:** 7 module declarations added, 7 export issues resolved

## Module Structure Validated

### Parser Module
```
rust/lib/std/src/parser/
├── __init__.spl          (✅ Fixed: added mod declarations)
├── error_recovery.spl
└── treesitter/
    ├── __init__.spl      (✅ Fixed: added mod edits)
    └── edits/
        └── __init__.spl
```

### ML Module
```
rust/lib/std/src/ml/
├── __init__.spl          (✅ Fixed: added mod torch)
└── torch/
    ├── __init__.spl      (✅ Fixed: added mod device, dtype, tensor_ffi)
    ├── device/
    │   └── __init__.spl
    ├── dtype/
    │   └── __init__.spl
    └── tensor_ffi/
        └── __init__.spl
```

## Recommendations

### For Development

1. ✅ **Always declare submodules** - Use `mod submodule` before exporting
2. ✅ **Match directory structure** - Every subdirectory needs a `mod` declaration
3. ✅ **Check exports** - Verify all exports reference declared symbols
4. ⚠️ **Test module loading** - Run tests to catch missing mod declarations

### For Future Module Work

When creating a new submodule:

```simple
# 1. Create directory and __init__.spl
mkdir -p rust/lib/std/src/mymodule/submodule
touch rust/lib/std/src/mymodule/submodule/__init__.spl

# 2. Declare in parent __init__.spl
mod submodule

# 3. Export if needed
export submodule
```

### Validation Script

Add to CI/build process:

```bash
# Check for exports without matching mod declarations
grep -r "^export" rust/lib/std/src/ | \
  while IFS=: read file export; do
    module=$(echo "$export" | sed 's/export //' | cut -d. -f1)
    if ! grep -q "^mod $module" "$file"; then
      echo "WARNING: $file exports $module without mod declaration"
    fi
  done
```

## Files Modified This Session

**Module Structure:**
- `rust/lib/std/src/parser/__init__.spl` - Added mod declarations
- `rust/lib/std/src/parser/treesitter/__init__.spl` - Added mod edits
- `rust/lib/std/src/ml/__init__.spl` - Added mod torch
- `rust/lib/std/src/ml/torch/__init__.spl` - Added mod device, dtype, tensor_ffi

**Documentation:**
- `doc/report/module_export_fixes_2026-02-03.md` (this file)

## Related Fixes

These fixes are related to earlier FFI wrapper export fixes:
- `doc/report/ffi_wrapper_audit_2026-02-03.md` - FFI wrapper exports
- `doc/report/parser_compiler_test_summary_2026-02-03.md` - Parser/compiler status

## Conclusion

✅ **All module export issues resolved**
✅ **Consistent pattern applied across all modules**
✅ **No more "undefined symbol" warnings for modules**
✅ **Module structure matches directory structure**

The module system now properly declares all submodules before exporting them, following Simple's module system requirements.
