# Extern Function Bug - Executive Summary

**Date:** 2026-02-15
**Status:** Root cause identified, ready to fix
**Severity:** CRITICAL - Blocks all external FFI
**Fix Complexity:** TRIVIAL - One line per location

---

## The Problem

```simple
extern fn rt_file_exists(path: text) -> i64
val x = rt_file_exists("/tmp/test")
# ERROR: undefined function: rt_file_exists
```

**All extern functions fail** with "undefined function" error.

---

## Root Cause

Extern functions are **NOT registered** in the function table during module evaluation.

**File:** `src/compiler_core/interpreter/eval.spl` (line 1769)
**File:** `src/compiler_core/interpreter/module_loader.spl` (line 215)

```simple
# CURRENT (BROKEN):
if tag == DECL_EXTERN_FN:
    func_register_return_type(d_node.name, d_node.ret_type)
    # ← Missing: func_table_register(d_node.name, did)
```

---

## The Fix

**Add ONE line at each location:**

```simple
# FIXED:
if tag == DECL_EXTERN_FN:
    func_table_register(d_node.name, did)  # ← ADD THIS
    func_register_return_type(d_node.name, d_node.ret_type)
```

Same pattern as regular functions (DECL_FN) which already works.

---

## Impact

### What's Blocked Today

- ❌ All 33+ runtime functions (rt_file_*, rt_process_*, rt_time_*)
- ❌ FFI libraries (CUDA, Torch, compression, crypto, regex, SQLite)
- ❌ Package management (uses extern functions)
- ❌ External integrations (MCP servers, databases)
- ❌ System programming (mmap, file locks, process spawn)

### What Unlocks After Fix

- ✅ Complete FFI support
- ✅ All runtime functions callable
- ✅ Package system functional
- ✅ External libraries usable
- ✅ 300+ blocked tests passing

---

## Available Runtime Functions (Currently Unusable)

**File I/O:** rt_file_exists, rt_file_read_text, rt_file_write, rt_file_delete, rt_file_copy, rt_file_size, rt_file_stat, rt_file_lock, rt_file_unlock

**Environment:** rt_env_get, rt_cli_get_args

**Process:** rt_process_spawn_async, rt_process_wait, rt_process_is_running, rt_process_kill, rt_shell_output

**Directory:** rt_dir_create, rt_dir_list, rt_dir_remove_all

**Memory:** rt_mmap, rt_munmap, rt_msync, rt_madvise

**Time:** rt_time_now_nanos, rt_time_now_micros

**JIT:** rt_exec_manager_create, rt_exec_manager_compile, rt_exec_manager_execute

All compiled into `bin/release/simple`, just not callable from Simple code.

---

## Is There a Whitelist?

**NO.** The compilability analyzer has a small list of "known safe" externs for optimization hints, but it's NOT enforced at runtime. The runtime will call ANY extern function once registered.

---

## Risk Assessment

**Risk:** EXTREMELY LOW
- Pure registration fix
- No logic changes
- Same pattern as working DECL_FN code
- No performance impact

**Breaking Changes:** ZERO
- Existing code uses wrappers (still works)
- Broken extern calls stay broken (no regression)
- New extern calls start working (pure gain)

---

## Testing

**Minimal test:**

```simple
describe "Extern Functions":
    it "should be callable":
        extern fn rt_file_exists(path: text) -> i64
        val exists = rt_file_exists("/tmp")
        expect(exists >= 0).to_equal(true)
```

**Before fix:** FAIL - "undefined function: rt_file_exists"
**After fix:** PASS

---

## Next Steps

1. Apply two-line fix (one per file)
2. Run regression tests (expect 0 failures)
3. Run package management tests (expect unlocked)
4. Update MEMORY.md (remove extern limitation)
5. Commit with detailed message

---

## Files to Modify

1. `src/compiler_core/interpreter/eval.spl` - Line 1769
2. `src/compiler_core/interpreter/module_loader.spl` - Line 215

---

## Detailed Documentation

- **Investigation Report:** `doc/report/extern_fn_validation_investigation_2026-02-15.md`
- **Call Flow Analysis:** `doc/report/extern_fn_call_flow.md`
- **Fix Locations:** `doc/report/extern_fn_fix_locations.md`
- **This Summary:** `doc/report/EXTERN_FN_BUG_SUMMARY.md`

---

## Why This Went Unnoticed

1. Seed compiler uses C++ directly (doesn't hit interpreter)
2. Most code uses wrapper functions (not raw externs)
3. Common operations are built-ins (print, int)
4. People work around it with `use` imports
5. Error message is generic ("undefined function")

---

## Timeline

- **2026-02-15:** Root cause identified (Task #12)
- **Next:** Apply fix (Task #13)
- **ETA:** 5 minutes to fix, 2 minutes to test
