# Phase 1 Investigation - String FFI Reality Check

**Date:** 2026-02-09
**Status:** 🔍 Pending Investigation

## Problem

Planned to add FFI functions that **don't exist**:
```simple
extern fn rt_string_from_ptr_len(ptr: i64, len: i64) -> text  # ❌ NOT IN RUNTIME
extern fn rt_string_to_ptr(s: text) -> i64                     # ❌ NOT IN RUNTIME
```

## Investigation Steps

### 1. Create Test File

```simple
# test/investigation/string_ffi_test.spl
use compiler.ffi_minimal as ffi

describe "String FFI Investigation":
    it "tests file_exists with placeholder pointer":
        val path = "README.md"
        # Current broken pattern
        val result = ffi.file_exists_ptr(0, path.len())
        print "Result with (0, len): {result}"

    it "tests with actual string (if auto-conversion exists)":
        # Try passing string directly?
        # val result = ffi.file_exists(path)  # Does this exist?
        pass
```

Run: `bin/simple test test/investigation/string_ffi_test.spl`

### 2. Search for Working Patterns

```bash
# Find how FFI is actually used successfully
grep -r "ffi\.file_" src test | grep -v TODO | head -20

# Check for string conversion utilities
grep -r "string.*ptr\|str.*data" src/std src/app | grep "fn "
```

### 3. Check ffi_minimal Wrappers

Look at `src/compiler/ffi_minimal.spl` - are there high-level wrappers?

### 4. Test Runtime Behavior

Create minimal reproducer:
```simple
extern fn rt_file_exists(path_ptr: i64, path_len: i64) -> bool

fn main():
    val s = "test.txt"
    val result = rt_file_exists(0, s.len())  # What happens?
    print "Result: {result}"
```

Does it:
- Crash?
- Return random result?
- Auto-convert string?

## Possible Findings

**A) Auto-Conversion Exists**
Simple automatically extracts ptr+len from strings.
→ TODOs are just about documentation/clarity

**B) Broken Implementation**
Using `0` as pointer is a bug.
→ Features don't work, need runtime fix

**C) Wrong Pattern**
Should use high-level wrappers, not low-level FFI.
→ Refactor to use `file_read(path: text)` not `file_read_ptr(ptr, len)`

**D) Not Implemented**
These interpreter features simply don't work yet.
→ Document limitation, skip these TODOs

## Next Steps After Investigation

Based on findings, update:
1. `TODO_PLAN_REVISED_2026-02-09.md`
2. `memory/MEMORY.md` - Add FFI limitations
3. Task list - Mark interpreter TODOs as blocked or fixable
4. Proceed with Phase 1B (implementable TODOs)
