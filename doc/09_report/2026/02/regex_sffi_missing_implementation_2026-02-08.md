# Regex SFFI - Missing Runtime Implementation

**Date:** 2026-02-08
**Status:** SFFI wrapper exists, runtime FFI missing
**Severity:** Medium - Blocks ~13 tests

---

## Summary

The regex SFFI wrapper is **complete in Simple** (354 lines in `src/app/io/regex_ffi.spl`) but the **Rust runtime implementation is missing**.

**What exists:**
- ✅ **Tier 2:** Simple SFFI wrapper (`src/app/io/regex_ffi.spl` - 354 lines)
- ✅ **Tier 2:** Interpreter extern wrappers (`src/app/interpreter.extern/regex.spl` - 84 lines)
- ✅ **Test suite:** Integration tests (`test/app/io/regex_sffi_spec.spl` - 25 tests)

**What's missing:**
- ❌ **Tier 1:** Rust FFI implementation (the `rt_regex_*` functions)

---

## Error Message

```
semantic: unknown extern function: rt_regex_new
semantic: unknown extern function: rt_regex_is_match
semantic: unknown extern function: rt_regex_find
... (all 16 extern functions missing)
```

---

## Missing Runtime Functions

### Required Extern Functions (16 total):

**Compilation:**
```rust
extern fn rt_regex_new(pattern: text) -> i64
extern fn rt_regex_destroy(handle: i64)
```

**Matching:**
```rust
extern fn rt_regex_is_match(handle: i64, text: text) -> i64
extern fn rt_regex_find(handle: i64, text: text) -> text
extern fn rt_regex_find_all(handle: i64, text: text) -> text
```

**Captures:**
```rust
extern fn rt_regex_captures(handle: i64, text: text) -> text
extern fn rt_regex_captures_len(handle: i64, text: text) -> i64
```

**Replace:**
```rust
extern fn rt_regex_replace(handle: i64, text: text, replacement: text) -> text
extern fn rt_regex_replace_all(handle: i64, text: text, replacement: text) -> text
```

**Split:**
```rust
extern fn rt_regex_split(handle: i64, text: text) -> text
```

**Quick Functions (no handle):**
```rust
extern fn rt_regex_is_match_quick(pattern: text, text: text) -> i64
extern fn rt_regex_find_quick(pattern: text, text: text) -> text
extern fn rt_regex_replace_quick(pattern: text, text: text, replacement: text) -> text
extern fn rt_regex_replace_all_quick(pattern: text, text: text, replacement: text) -> text
extern fn rt_regex_split_quick(pattern: text, text: text) -> text
```

---

## Implementation Plan

### Option 1: Use Rust `regex` Crate (Recommended)

**Dependency:** Add `regex = "1.10"` to runtime's Cargo.toml

**Implementation estimate:** ~200-250 lines of Rust code

**Rust file location:** `rust/lib/runtime/src/extern_impls/regex.rs` (new file)

**Key implementation:**

```rust
use regex::Regex;
use std::collections::HashMap;
use std::sync::Mutex;

// Global handle table for compiled regexes
lazy_static! {
    static ref REGEX_TABLE: Mutex<HashMap<i64, Regex>> = Mutex::new(HashMap::new());
}

static mut NEXT_HANDLE: i64 = 1;

#[no_mangle]
pub extern "C" fn rt_regex_new(pattern: *const c_char) -> i64 {
    let pattern_str = unsafe { CStr::from_ptr(pattern).to_string_lossy().into_owned() };

    match Regex::new(&pattern_str) {
        Ok(regex) => {
            let handle = unsafe {
                NEXT_HANDLE += 1;
                NEXT_HANDLE
            };
            REGEX_TABLE.lock().unwrap().insert(handle, regex);
            handle
        }
        Err(_) => 0  // Invalid handle on error
    }
}

#[no_mangle]
pub extern "C" fn rt_regex_destroy(handle: i64) {
    REGEX_TABLE.lock().unwrap().remove(&handle);
}

#[no_mangle]
pub extern "C" fn rt_regex_is_match(handle: i64, text: *const c_char) -> i64 {
    let text_str = unsafe { CStr::from_ptr(text).to_string_lossy().into_owned() };

    let table = REGEX_TABLE.lock().unwrap();
    match table.get(&handle) {
        Some(regex) => if regex.is_match(&text_str) { 1 } else { 0 },
        None => 0
    }
}

// ... (implement remaining 13 functions)
```

### Option 2: Wrap PCRE2 C Library

**Dependency:** Link to `libpcre2-8`

**Implementation estimate:** ~300-400 lines (more complex, C FFI)

**Pros:** More features, Perl-compatible
**Cons:** External C dependency, more complex build

---

## Impact

**Unblocks:**
- 25 integration tests in `test/app/io/regex_sffi_spec.spl`
- ~13 skip tests that need regex functionality
- Custom block validation (7 skip tests in `test/compiler/custom_blocks_easy_api_spec.spl`)

**Total:** ~45 tests unblocked

---

## Recommendation

**Implement using Rust `regex` crate** (Option 1):
- ✅ Pure Rust (no C dependencies)
- ✅ Safe, well-tested, widely used
- ✅ ~200 lines of code
- ✅ Can be added to pre-built runtime
- ⏱️ **Estimated time:** 1-2 hours

**Alternative:** If PCRE2 compatibility is needed later, can add as separate module (`pcre2_ffi.spl`)

---

## Next Steps

1. **Add `regex` crate to runtime:** Edit `rust/lib/runtime/Cargo.toml`
2. **Implement Rust FFI:** Create `rust/lib/runtime/src/extern_impls/regex.rs`
3. **Register functions:** Add to runtime's extern function table
4. **Rebuild runtime:** `cd rust/lib/runtime && cargo build --release`
5. **Test:** `bin/simple test test/app/io/regex_sffi_spec.spl`

---

## Status

- **SFFI Wrapper:** ✅ Complete (354 lines)
- **Rust Runtime FFI:** ❌ Not implemented
- **Tests:** ✅ Written (25 tests waiting)
- **Documentation:** ✅ Complete (this report)

**Blocking:** Runtime Rust implementation (~200 lines, 1-2 hours)
