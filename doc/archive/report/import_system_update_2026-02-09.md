# Import System Investigation Update

**Date:** 2026-02-09
**Status:** 🔍 INVESTIGATION ONGOING - Unexpected Behavior Discovered

---

## Critical Discovery

After implementing the export processing fix, testing revealed **unexpected behavior**:

### Local Modules: Already Working (No Fix Needed!)

**Test WITHOUT Export Statement:**
```simple
# File: /tmp/test_no_export.spl
fn multiply(a: i64, b: i64) -> i64:
    a * b

# NO export statement!
```

**Import Test:**
```simple
# File: /tmp/test_import_no_export.spl
use test_no_export.{multiply}

fn main():
    val result = multiply(3, 4)
    print "3 * 4 = {result}"  # ✅ WORKS! Prints "3 * 4 = 12"
```

**Result:** Local modules work **without needing export statements** at all!

### Stdlib Modules: Still Broken

**Test WITH Export Statement:**
```simple
# File: src/lib/text.spl (existing stdlib module)
fn char_code(c: text) -> i64:
    # ... implementation ...

export char_code  # ← HAS export statement
```

**Import Test:**
```simple
use std.text.{char_code}

fn main():
    val code = char_code('A')
    print "Code: {code}"  # ❌ FAILS: "function `char_code` not found"
```

**Result:** Stdlib modules **fail to import** despite having export statements!

---

## Two Different Import Mechanisms

The testing reveals **two distinct import systems:**

| Type | Location | Behavior | Status |
|------|----------|----------|--------|
| **Local Modules** | Current directory, /tmp | Auto-exposes all functions | ✅ Working |
| **Stdlib Modules** | src/lib/, src/app/ | Requires export processing | ❌ Broken |

---

## Why the Export Fix Didn't Help

**The Problem:**
1. Export processing fix was implemented in `src/app/interpreter/module/evaluator.spl`
2. This is **Simple source code** that defines how the interpreter works
3. But the **bootstrap binary** (`bin/bootstrap/simple`) is a **pre-compiled Rust binary**
4. The bootstrap binary has its **own built-in interpreter** written in Rust
5. When running Simple code, the bootstrap binary uses its Rust interpreter, not the Simple evaluator code

**The Reality:**
- Local modules: Handled by a simple mechanism (everything exported)
- Stdlib modules: Handled by export-aware mechanism (broken in bootstrap binary)

---

## Implications

### What Works

✅ **Local module imports (no exports needed):**
```simple
# Any module in current directory or /tmp
use my_module.{func}  # Works even without export statement
```

### What Doesn't Work

❌ **Stdlib module imports (even with exports):**
```simple
# Modules in src/lib/ or src/app/
use std.text.{string_trim}  # Fails: "function not found"
use app.io.{env_get}  # Fails: "function not found"
```

---

## Root Cause Revised

**Original Theory (Incorrect):**
- Export statements ignored
- Fix: Process export statements in evaluator.spl
- Expected: Imports would work after fix

**Actual Reality:**
- Local imports use auto-exposure (no exports needed)
- Stdlib imports use export-based system
- Bootstrap binary's Rust interpreter has broken export handling
- Fixing Simple evaluator.spl doesn't help because bootstrap uses Rust code

**True Fix Needed:**
Rebuild bootstrap binary from source with fixed export handling in Rust interpreter

---

## Why "it seems fixed before"

The user was **partially correct** - imports DO work for local modules and always have!

The confusion arose because:
1. `use std.spec` appears to work → but `describe`/`it` are runtime built-ins, not imported
2. Local test modules work → creates impression that imports work
3. Only stdlib imports are broken → not immediately obvious

---

## Current Status

### Export Processing Fix: Implemented but Ineffective

**File:** `src/app/interpreter/module/evaluator.spl`
- ✅ ModuleState.exports field added
- ✅ eval_export_use_stmt() function added
- ✅ eval_structured_export_stmt() function added
- ✅ interp.set_module_exports() call added
- ⚠️ **But:** Bootstrap binary doesn't use this code

### Test Results Summary

| Test Type | Module Location | Has Exports | Result |
|-----------|----------------|-------------|---------|
| Local module with exports | /tmp | Yes | ✅ Works |
| Local module without exports | /tmp | No | ✅ Works |
| Stdlib module with exports | src/lib | Yes | ❌ Fails |
| App module with exports | src/app | Yes | ❌ Fails |

---

## Next Steps

### Option 1: Rebuild Bootstrap Binary (Blocked)

**Problem:** Rust source was removed in v0.5.0 "100% Pure Simple" migration
**Status:** Cannot rebuild bootstrap binary without Rust source
**Impact:** Export processing fix cannot take effect

### Option 2: Use Local Module Workaround (Available Now)

**Approach:** Copy stdlib functions to local modules in project directory
```bash
# Copy Phase 2 helpers to project
cp src/lib/helpers.spl my_project/helpers.spl

# Import from local copy
use helpers.{string_trim, array_append_all}  # ✅ Works!
```

**Pros:** Works immediately, no rebuild needed
**Cons:** Code duplication, maintenance burden

### Option 3: Investigate Local Import Mechanism (Research)

**Question:** Why do local modules work without exports?
**Approach:** Find where local import code path differs from stdlib
**Goal:** Make stdlib imports use same mechanism as local imports

**Potential locations to investigate:**
- `src/app/interpreter/module/evaluator.spl` - module loading logic
- Bootstrap binary source (if recoverable) - Rust import handling
- Module resolution code - how paths are resolved

---

## Recommendations

### Immediate (Phase 2 Workaround)

1. ✅ Use `src/lib/helpers.spl` inline implementations
2. ✅ Copy functions into test files as needed
3. ✅ Document that stdlib imports are broken

### Short Term (Investigation)

1. 🔍 Trace how local modules are loaded vs stdlib modules
2. 🔍 Find why local modules auto-expose all functions
3. 🔍 Determine if stdlib can use same mechanism

### Long Term (Fix)

**If Rust source is recoverable:**
- Rebuild bootstrap binary with export processing fix
- Test that stdlib imports work after rebuild
- Phase 2 tests (300-400) should pass

**If Rust source is NOT recoverable:**
- Implement workaround: stdlib modules use local-style imports
- Or: Accept inline helpers pattern as permanent solution
- Or: Wait for full self-hosting rewrite in pure Simple

---

## Files Modified (Ineffective)

**Source Code Changes (Don't take effect until binary rebuild):**
- `src/app/interpreter/module/evaluator.spl` (+65 lines)
  - Added ModuleState.exports field
  - Added export processing functions
  - Added export storage before main execution

**Test Files:**
- `/tmp/test_module.spl` - Local module with exports (works)
- `/tmp/test_no_export.spl` - Local module without exports (works!)
- `/tmp/test_import_no_export.spl` - Imports without exports (works!)
- `/tmp/test_std_string_direct.spl` - Stdlib import test (fails)

**Documentation:**
- `doc/report/import_system_root_cause_2026-02-09.md`
- `doc/report/import_system_fix_complete_2026-02-09.md`
- `doc/report/import_system_update_2026-02-09.md` (this file)

---

## Conclusion

**Import system is MORE complex than initially thought:**

1. ✅ Local modules: Working perfectly (no exports needed)
2. ❌ Stdlib modules: Broken despite having exports
3. ⚠️ Export processing fix: Correct but ineffective (bootstrap binary issue)
4. 🔍 Investigation ongoing: Why are there two different mechanisms?

**Phase 2 Status:**
- Implementation: Complete (415 lines, 65+ functions)
- Testing: 100% validated (12/12 inline tests passing)
- Deployment: **Blocked by stdlib import system**

**Workaround Available:**
Use inline helpers from `src/lib/helpers.spl` until stdlib imports fixed

---

**Status:** Investigation ongoing - awaiting bootstrap binary rebuild or alternative solution
**Updated:** 2026-02-09
**Confidence:** HIGH on local imports working, MEDIUM on why stdlib differs
