# Bug Report: Parser fails on `*const` pointer types in extern functions

**Bug ID:** PARSER-001
**Date:** 2026-01-17
**Severity:** P0 - Critical (blocks 98+ FFI usages)
**Component:** Parser (`src/parser/src/parser_types.rs:89-95`)
**Status:** Confirmed, root cause identified

## Summary

The parser fails to recognize `*const T` and `*mut T` pointer type syntax in FFI declarations. It treats `const` and `mut` as keyword tokens after `*`, causing a parse error.

## Minimal Reproduction

```simple
extern fn test_func(data: *const u8) -> i32

main = 0
```

**Error:**
```
error: parse error: Unexpected token: expected identifier, found Const
```

**Test file:** `bug_const_pointer.spl`

## Root Cause Analysis

### Token Definition (Working as Intended)

In `src/parser/src/token.rs:187`:
```rust
Const,  // Keyword token for const declarations
```

Lexer correctly tokenizes `"const"` → `TokenKind::Const` (lexer/identifiers.rs:149)

### Parser Bug (Actual Issue)

In `src/parser/src/parser_types.rs:89-95`:

```rust
TokenKind::Star => {
    self.advance();
    let inner = self.parse_single_type()?;  // ❌ BUG: Fails here
    return Ok(Type::Pointer {
        kind: PointerKind::Shared,
        inner: Box::new(inner),
    });
}
```

**Execution flow:**
1. Parser sees `*` (Star token) ✓
2. Advances past `*` ✓
3. Calls `parse_single_type()` expecting a type identifier ✓
4. `parse_single_type()` sees `TokenKind::Const` (keyword) ❌
5. Error: "expected identifier, found Const"

**Problem:** Parser doesn't check for `const` or `mut` modifiers after `*` before parsing the inner type.

### Working Comparison: `&mut T`

The parser correctly handles `&mut T` at lines 64-74:

```rust
TokenKind::Ampersand => {
    self.advance();
    if self.check(&TokenKind::Mut) {  // ✓ Checks for mut keyword
        self.advance();
        let inner = self.parse_single_type()?;
        return Ok(Type::Pointer {
            kind: PointerKind::BorrowMut,
            inner: Box::new(inner),
        });
    }
    // ... handle &T
}
```

## Suggested Fix

### Code Changes

**File:** `src/parser/src/parser_types.rs:89-95`

```rust
TokenKind::Star => {
    self.advance();

    // Check for *const T or *mut T (similar to &mut T handling)
    let kind = if self.check(&TokenKind::Const) {
        self.advance();
        PointerKind::RawConst  // ⚠️ New variant needed
    } else if self.check(&TokenKind::Mut) {
        self.advance();
        PointerKind::RawMut    // ⚠️ New variant needed
    } else {
        PointerKind::Shared
    };

    let inner = self.parse_single_type()?;
    return Ok(Type::Pointer {
        kind,
        inner: Box::new(inner),
    });
}
```

**Additional Changes Needed:**

Add new enum variants in pointer kind definition:
```rust
pub enum PointerKind {
    // Existing
    Unique,       // &T
    Shared,       // *T
    BorrowMut,    // &mut T
    Weak,         // -T
    Handle,       // +T
    Borrow,       // &T_borrow

    // New variants needed
    RawConst,     // *const T (for FFI)
    RawMut,       // *mut T (for FFI)
}
```

## Impact Assessment

### Blocked Modules (98+ usages)

```bash
$ grep -r "\*const" simple/std_lib/src --include="*.spl" | wc -l
98
```

**Critical modules:**
1. **Vulkan FFI** (`ui/gui/vulkan_ffi.spl`) - 11 functions
   - `extern fn rt_vk_buffer_upload(buffer_handle: u64, data: *const u8, size: u64) -> i32`
   - `extern fn rt_vk_kernel_compile(device_handle: u64, spirv: *const u8, spirv_size: u64) -> u64`
   - 9 more functions

2. **Memory Management** (`core_nogc/arena.spl`) - 3 usages
   - `ptr: *const u8`
   - `extern fn native_memcpy(dst: *mut u8, src: *const u8, size: u64)`

3. **Native UI** (`ui/gui/native.spl`) - 2 functions
   - `extern fn native_window_create(title_ptr: *const u8, title_len: u64, width: u32, height: u32) -> WindowHandle`

### Blocked Features
- All Vulkan graphics (9 P1 TODOs waiting on this)
- FFI interop with C libraries
- Low-level memory operations
- Terminal I/O (term_ffi.spl)
- GPU compute kernels

### Current Workaround
**None available** - these modules cannot be imported until parser is fixed.

## Test Coverage

### SSpec Tests Created
1. **Grammar specification:** `simple/std_lib/test/features/syntax/const_vs_val_spec.spl`
   - Documents `const` vs `val` vs pointer types
   - Shows relationship between keywords

2. **Bug reproduction:** `simple/std_lib/test/features/bugs/pointer_const_parsing_bug_spec.spl`
   - Minimal reproduction cases
   - Impact documentation
   - Verification tests (pending fix)

### Test Cases (After Fix)
```simple
# Should all parse successfully after fix
extern fn ptr_const(data: *const u8, len: u64) -> i32
extern fn ptr_mut(data: *mut u8, len: u64) -> i32
extern fn ptr_both(src: *const u8, dst: *mut u8, len: u64) -> i32
extern fn ptr_multi(a: *const u32, b: *const i64) -> void

# In struct fields
struct Buffer:
    data: *const u8
    len: u64

# Mixed with borrows
fn mixed(borrow: &T, raw: *const T) -> bool
```

### Regression Tests
Ensure these still work after fix:
- `const` declarations: `const MAX_SIZE: u64 = 1024`
- `val` declarations: `val x = 42`
- Borrow types: `&T`, `&mut T`
- Plain pointers: `*T`

## Error Message Improvement

### Current (Cryptic)
```
error: parse error: Unexpected token: expected identifier, found Const
```

### Proposed (Helpful)
```
error: parse error at simple/std_lib/src/ui/gui/vulkan_ffi.spl:54:50
Unexpected keyword 'const' in pointer type

   54 | extern fn rt_vk_buffer_upload(buffer_handle: u64, data: *const u8, size: u64) -> i32
      |                                                          ^^^^^ unexpected keyword

Expected: type identifier after '*'
Found: keyword 'const'

Help: Pointer types '*const T' and '*mut T' are not yet supported.
      This is a known parser bug. Track progress in:
      simple/bug_report_const_pointer_parsing.md
```

See: `doc/research/parser_error_improvements.md` for implementation details.

## Documentation

### Created Files
- **Bug report:** `simple/bug_report_const_pointer_parsing.md` (this file)
- **Grammar research:** `doc/research/const_vs_val_grammar.md`
- **Error improvements:** `doc/research/parser_error_improvements.md`
- **SSpec grammar test:** `simple/std_lib/test/features/syntax/const_vs_val_spec.spl`
- **SSpec bug test:** `simple/std_lib/test/features/bugs/pointer_const_parsing_bug_spec.spl`

### Related Issues
- User report: "val x : u64 = 42 cause error" - type annotations not supported in `val` (separate issue, documented)
- This bug specifically affects `*const T` in FFI declarations

## Implementation Checklist

- [ ] Add `PointerKind::RawConst` and `PointerKind::RawMut` enum variants
- [ ] Modify `parser_types.rs:89-95` to check for `const`/`mut` after `*`
- [ ] Update AST/HIR/MIR to handle new pointer kinds
- [ ] Add better error message with context and help
- [ ] Enable SSpec tests in `pointer_const_parsing_bug_spec.spl`
- [ ] Verify all 98+ stdlib usages parse correctly
- [ ] Run regression tests (const declarations, val declarations, borrows)
- [ ] Update language grammar documentation

## Priority Justification

**P0 - Critical** because:
1. Blocks 98+ FFI declarations across stdlib
2. Blocks 9 high-priority Vulkan feature TODOs
3. Prevents FFI interop with C libraries
4. No workaround available
5. Fix is straightforward (10-line change + enum variants)

## Timeline

**Estimated fix time:** 1-2 hours
- Parser change: 15 minutes
- Enum variants: 15 minutes
- AST/HIR/MIR updates: 30 minutes
- Testing: 30 minutes

**Estimated impact:** Unblocks 9 P1 TODOs + enables FFI ecosystem

---

**Discovered by:** Claude Sonnet 4.5
**Session:** TODO implementation, 2026-01-17
**Investigation:** Full root cause analysis complete
**Status:** Ready for implementation
