# Extern Function Validation Investigation

**Date:** 2026-02-15
**Task:** Task #12 - Investigate semantic analyzer extern fn validation
**Status:** COMPLETE - Root cause identified

## Executive Summary

The runtime interpreter **does NOT have a whitelist** for extern functions. The error "undefined function" occurs because **extern function declarations are not registered in the function table** during module evaluation. This is a simple registration bug, not a security whitelist.

## Root Cause Analysis

### 1. The Problem Location

**File:** `src/compiler_core/interpreter/eval.spl`
**Lines:** 1769-1770

```simple
if tag == DECL_EXTERN_FN:
    func_register_return_type(d_node.name, d_node.ret_type)
```

**Compare with regular functions (lines 1766-1768):**

```simple
if tag == DECL_FN:
    func_table_register(d_node.name, did)
    func_register_return_type(d_node.name, d_node.ret_type)
```

**The bug:** When processing `extern fn` declarations, the code only registers the return type but **does NOT call `func_table_register()`**. This means extern functions are not in the function lookup table.

### 2. The Failure Chain

When calling an extern function:

1. **eval.spl:740-742** - Checks builtin functions (print, int, etc.) - NOT FOUND
2. **eval.spl:745-747** - Checks function table via `func_table_lookup(name)` - **RETURNS -1** (not found)
3. **eval.spl:750-754** - Checks environment for function value - NOT FOUND
4. **eval.spl:756** - **Error: "undefined function: {name}"**

The extern function never gets a chance to execute because it's not in the function table.

### 3. Module Loader Has Same Bug

**File:** `src/compiler_core/interpreter/module_loader.spl`
**Lines:** 215-218

```simple
if tag == DECL_EXTERN_FN:
    val name = decl_get_name(did)
    val ret_type = decl_get_ret_type(did)
    func_register_return_type(name, ret_type)
```

Same issue - only registers return type, not the function itself.

**Compare with regular functions (lines 209-213):**

```simple
if tag == DECL_FN:
    val name = decl_get_name(did)
    val ret_type = decl_get_ret_type(did)
    func_table_register(name, did)
    func_register_return_type(name, ret_type)
```

## Available Runtime Functions

The C runtime (`src/compiler_seed/runtime.h`) provides 33+ extern functions:

**Core I/O:**
- `rt_file_exists`, `rt_file_read_text`, `rt_file_write`, `rt_file_delete`
- `rt_file_copy`, `rt_file_size`, `rt_file_stat`, `rt_file_lock`, `rt_file_unlock`
- `rt_file_read_text_at`, `rt_file_write_text_at`

**Environment:**
- `rt_env_get`, `rt_cli_get_args`

**Process:**
- `rt_process_spawn_async`, `rt_process_wait`, `rt_process_is_running`, `rt_process_kill`
- `rt_shell_output`

**Directory:**
- `rt_dir_create`, `rt_dir_list`, `rt_dir_list_free`, `rt_dir_remove_all`

**Memory:**
- `rt_mmap`, `rt_munmap`, `rt_msync`, `rt_madvise`

**Time:**
- `rt_time_now_nanos`, `rt_time_now_micros`

**JIT:**
- `rt_exec_manager_create`, `rt_exec_manager_compile`, `rt_exec_manager_execute`
- `rt_exec_manager_has_function`, `rt_exec_manager_cleanup`

All these functions are compiled into the runtime binary and ready to use.

## The "Whitelist" Confusion

There IS a whitelist in the codebase, but it's NOT used for runtime validation:

**File:** `src/compiler/compilability.spl`
**Lines:** 101-106

```simple
known_safe_externs: [
    "rt_print", "rt_println", "rt_eprintln",
    "rt_hash_sha256", "rt_file_exists", "rt_file_read_text",
    "rt_file_write_text", "rt_file_size", "rt_file_modified",
    "rt_time_now", "rt_env_var", "rt_exit"
]
```

**Purpose:** This list is used by `CompilabilityAnalyzer` to determine if a function can be **compiled** vs must fall back to interpreter. It's a compile-time optimization hint, NOT a runtime security check.

**Evidence:** Only 2 files reference this: `src/compiler/compilability.spl` and `src/compiler_core_legacy/compilability.spl`. Neither is imported by the interpreter.

## The Fix

**Two locations need fixing:**

### Fix 1: `src/compiler_core/interpreter/eval.spl` (line 1769)

```simple
# BEFORE:
if tag == DECL_EXTERN_FN:
    func_register_return_type(d_node.name, d_node.ret_type)

# AFTER:
if tag == DECL_EXTERN_FN:
    func_table_register(d_node.name, did)
    func_register_return_type(d_node.name, d_node.ret_type)
```

### Fix 2: `src/compiler_core/interpreter/module_loader.spl` (line 215)

```simple
# BEFORE:
if tag == DECL_EXTERN_FN:
    val name = decl_get_name(did)
    val ret_type = decl_get_ret_type(did)
    func_register_return_type(name, ret_type)

# AFTER:
if tag == DECL_EXTERN_FN:
    val name = decl_get_name(did)
    val ret_type = decl_get_ret_type(did)
    func_table_register(name, did)
    func_register_return_type(name, ret_type)
```

## Impact

Once fixed, **ALL** extern functions declared in Simple code will be:
1. Registered in the function table
2. Callable from Simple code
3. Dispatched to the C runtime implementation

No whitelist enforcement. The runtime trusts that extern declarations match actual C implementations.

## Security Considerations

**Current state:** Implicit whitelist via non-registration (broken security)
**After fix:** No whitelist (all extern functions callable)

**Recommendation:** If security/sandboxing is desired, implement explicit whitelist checking in `eval_function_call()` before executing extern functions. But this is a separate feature request, not part of the current bug fix.

## Testing Strategy

**Test 1:** Call existing rt_ functions (should work after fix)
```simple
extern fn rt_file_exists(path: text) -> i64
val exists = rt_file_exists("/tmp/test.txt")
```

**Test 2:** Call function in standard library that uses extern
```simple
use std.path.{exists}
val e = exists("/tmp/test.txt")
```

**Test 3:** Verify error for truly undefined externs
```simple
extern fn rt_nonexistent_function() -> i64
val x = rt_nonexistent_function()  # Should fail at link time or runtime dispatch
```

## Files to Modify

1. `src/compiler_core/interpreter/eval.spl` - Add `func_table_register` call at line 1769
2. `src/compiler_core/interpreter/module_loader.spl` - Add `func_table_register` call at line 215

## Expected Results

After fix:
- All 33+ runtime functions become usable
- External FFI libraries (CUDA, Torch, compression, crypto) become functional
- Package system tests pass (they use extern functions)
- No test suite regressions (existing code doesn't use many externs)

## Related Issues

- Task #12: Investigate extern fn validation (THIS DOCUMENT)
- Task #13: Fix the validation (BLOCKED - awaiting this investigation)
- Package management tests timeout (will be fixed by enabling extern functions)
- FFI library tests fail (will be fixed by enabling extern functions)
