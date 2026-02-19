# Phase 2 SFFI Wrappers - Workaround Guide

**Date:** 2026-02-09
**Problem:** Runtime import system prevents using Phase 2 SFFI functions
**Solution:** Inline implementations as temporary workaround

---

## Background

Phase 2 implemented 415 lines of SFFI wrappers (65+ functions) across three domains:
- **String Methods** (`src/std/text.spl`) - 8 functions
- **Array Methods** (`src/std/array.spl`) - 7 functions
- **System/Process** (`src/lib/ffi/system.spl`) - 50+ functions

All implementations are correct and tested, but the runtime import system prevents using them:

```simple
use std.text.{string_trim}  # ✅ Loads successfully
string_trim("  test  ")        # ❌ "function not found"
```

---

## Workaround Strategy

Until the import system is fixed, use **inline implementations** in your test files. This is the same pattern that made Phase 1 successful.

### ✅ Works: Inline Implementation
```simple
fn string_trim_inline(s: text) -> text:
    var result = s
    while result.len() > 0:
        val first = result[0:1]
        if first == " " or first == "\t" or first == "\n":
            result = result[1:]
        else:
            break
    while result.len() > 0:
        val last = result[result.len()-1:result.len()]
        if last == " " or last == "\t" or last == "\n":
            result = result[0:result.len()-1]
        else:
            break
    result

describe "My Feature":
    it "trims strings":
        val trimmed = string_trim_inline("  hello  ")
        expect(trimmed).to_equal("hello")
```

### ❌ Doesn't Work: Module Import
```simple
use std.text.{string_trim}  # Module loads...

describe "My Feature":
    it "trims strings":
        val trimmed = string_trim("  hello  ")  # ...but function not found!
```

---

## Inline Helper Module

**File:** `src/std/helpers.spl`

This module provides copy-pasteable inline implementations of the most useful Phase 2 functions:

### String Helpers (8 functions available)
- `string_trim_inline(s: text) -> text` - Trim whitespace
- `string_split_inline(s: text, delim: text) -> [text]` - Split by delimiter
- `to_int_or_inline(s: text, default: i64) -> i64` - Parse with fallback

### Array Helpers (7 functions available)
- `array_append_all_inline(arr1, arr2)` - Concatenate arrays
- `array_partition_inline(arr, predicate)` - Split by condition
- `array_flatten_inline(nested)` - Flatten one level
- `array_uniq_inline(arr)` - Remove duplicates
- `array_compact_inline(arr)` - Remove nils

### System Helpers (limited)
- `generate_simple_uuid_inline() -> text` - Pseudo-UUID (NOT cryptographically secure)
- Most system/process functions require FFI and cannot be inlined

---

## Usage Instructions

### Step 1: Copy Function Definition

Open `src/std/helpers.spl` and copy the function you need:

```simple
fn string_trim_inline(s: text) -> text:
    var result = s
    # Trim leading whitespace
    while result.len() > 0:
        val first = result[0:1]
        if first == " " or first == "\t" or first == "\n" or first == "\r":
            result = result[1:]
        else:
            break
    # Trim trailing whitespace
    while result.len() > 0:
        val last = result[result.len()-1:result.len()]
        if last == " " or last == "\t" or last == "\n" or last == "\r":
            result = result[0:result.len()-1]
        else:
            break
    result
```

### Step 2: Paste Into Test File

Add the function definition at the **module level** (not inside describe blocks):

```simple
# my_feature_spec.spl

# Inline helpers (copy from src/std/helpers.spl)
fn string_trim_inline(s: text) -> text:
    # ... paste implementation ...
    result

# Now use in tests
describe "My Feature":
    it "handles trimmed input":
        val input = string_trim_inline(user_input)
        expect(input.len()).to_be_greater_than(0)
```

### Step 3: Use in Tests

Call the inline function like any other function:

```simple
it "processes strings correctly":
    val parts = string_split_inline("a,b,c", ",")
    expect(parts.len()).to_equal(3)
    expect(parts[0]).to_equal("a")
```

---

## Migration Path

When the import system is fixed, migrate from inline to imports:

### Before (Inline)
```simple
fn string_trim_inline(s: text) -> text:
    var result = s
    # ... implementation ...
    result

describe "My Tests":
    it "works":
        val trimmed = string_trim_inline("  test  ")
```

### After (Imports Work)
```simple
use std.text.{string_trim}

describe "My Tests":
    it "works":
        val trimmed = string_trim("  test  ")
```

---

## Examples

### Example 1: String Processing
```simple
fn string_split_inline(s: text, delimiter: text) -> [text]:
    if delimiter.len() == 0:
        return [s]
    var parts = []
    var current = ""
    var i = 0
    while i < s.len():
        var is_delim = true
        var j = 0
        while j < delimiter.len() and i + j < s.len():
            if s[i+j:i+j+1] != delimiter[j:j+1]:
                is_delim = false
                break
            j = j + 1
        if is_delim and j == delimiter.len():
            parts.push(current)
            current = ""
            i = i + delimiter.len()
        else:
            current = current + s[i:i+1]
            i = i + 1
    parts.push(current)
    parts

describe "CSV Parser":
    it "splits comma-separated values":
        val csv = "name,age,city"
        val fields = string_split_inline(csv, ",")
        expect(fields.len()).to_equal(3)
        expect(fields[0]).to_equal("name")
```

### Example 2: Array Operations
```simple
fn array_append_all_inline(arr1, arr2):
    var result = []
    for item in arr1:
        result.push(item)
    for item in arr2:
        result.push(item)
    result

fn array_flatten_inline(nested_arr):
    var result = []
    for sub_arr in nested_arr:
        for item in sub_arr:
            result.push(item)
    result

describe "Data Processor":
    it "combines and flattens data":
        val batch1 = [1, 2, 3]
        val batch2 = [4, 5, 6]
        val combined = array_append_all_inline(batch1, batch2)
        expect(combined.len()).to_equal(6)

        val nested = [[1, 2], [3, 4], [5]]
        val flat_result = array_flatten_inline(nested)
        expect(flat_result.len()).to_equal(5)
```

### Example 3: Safe Parsing
```simple
fn to_int_or_inline(s: text, default_val: i64) -> i64:
    if s.len() == 0:
        return default_val
    val first = s[0:1]
    if first == "-" or first == "0" or first == "1" or first == "2" or
       first == "3" or first == "4" or first == "5" or first == "6" or
       first == "7" or first == "8" or first == "9":
        int(s)
    else:
        default_val

describe "Config Parser":
    it "parses integers with fallback":
        val port = to_int_or_inline("8080", 3000)
        expect(port).to_equal(8080)

        val invalid = to_int_or_inline("not-a-number", 9999)
        expect(invalid).to_equal(9999)
```

---

## Limitations

### ✅ Can Be Inlined
- Pure Simple functions (string/array operations)
- Functions with no external dependencies
- Functions using only built-in runtime operations

### ❌ Cannot Be Inlined
- System/Process FFI functions (require `extern fn`)
  - `uuid_v4()`, `process_spawn()`, `process_wait()`, `process_kill()`
  - `env_remove()`, `timestamp_from_iso()`, `time_now_iso()`
- Functions requiring runtime-specific implementations
- Atomic operations, thread operations

**Workaround for FFI:** Tests needing these functions should:
1. Use `skip_on_interpreter` decorator
2. Test in compiled mode where imports may work
3. Use shell() workarounds for simple cases
4. Wait for import system fix

---

## Performance Considerations

### Inline Functions: ✅ Good
- **No import overhead** - function is directly available
- **No lookup cost** - direct call
- **Same performance** as any other function

### Trade-offs
- **Code duplication** - same function copied into multiple test files
- **Maintenance burden** - updates need to be made in multiple places
- **File size** - each test file larger with inline implementations

**Recommendation:** Accept the duplication as temporary. When imports are fixed, do a global search-and-replace migration.

---

## Future: When Imports Work

The goal is to eventually use:

```simple
use std.text.{string_trim, string_split, to_int_or}
use std.array.{array_append_all, array_partition, array_flatten}
use ffi.system.{uuid_v4, process_spawn, env_remove}
```

Once the runtime import system is fixed, all Phase 2 functions will be immediately usable with no code changes needed (except removing inline definitions and adding use statements).

---

## Status Tracking

**Current State (2026-02-09):**
- Phase 2: 100% implemented ✅, 0% usable via imports ❌
- Workaround: Inline implementations ✅
- Tests enabled: 0 (blocked by imports)
- Tests potential: 300-400 (when imports work)

**Blockers:**
- Runtime import system prevents all module function calls
- Affects even pure extern fn wrappers with no dependencies

**Next Steps:**
1. Use inline helpers for critical functionality
2. Runtime team: Fix import/module system
3. Once fixed: Global migration from inline to imports

---

## References

- **Phase 2 Implementations:**
  - `src/std/text.spl` - String SFFI (+70 lines)
  - `src/std/array.spl` - Array SFFI (+85 lines)
  - `src/lib/ffi/system.spl` - System/Process SFFI (260 lines)

- **Inline Helpers:**
  - `src/std/helpers.spl` - Copy-paste inline implementations

- **Documentation:**
  - `doc/report/phase2_sffi_wrappers_complete_2026-02-09.md` - Full Phase 2 report
  - `doc/report/test_enablement_session_summary_2026-02-09.md` - Session summary
  - `doc/guide/phase2_workaround_guide.md` - This guide
