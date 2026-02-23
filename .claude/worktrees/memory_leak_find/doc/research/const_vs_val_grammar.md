# Simple Grammar: `const` vs `val` vs Pointer Types

**Date:** 2026-01-17
**Status:** Active Research
**Related:** Parser bug for `*const` pointers

## Overview

Simple language has THREE different uses of immutability-related keywords:

1. **`const`** - Compile-time constant declarations
2. **`val`** - Runtime immutable variables (Scala-style)
3. **`*const T`** - Const raw pointers in FFI (currently broken)

## Token Definition

All three are defined in `src/parser/src/token.rs`:

```rust
pub enum TokenKind {
    // Line 132-133
    Val,   // Immutable variable (Scala-style)
    Var,   // Mutable variable (Scala-style)

    // Line 187
    Const, // Compile-time constant keyword

    // Line 131 (legacy, being removed)
    Mut,   // Legacy mutable modifier
}
```

## 1. Const Declarations

### Syntax
```simple
const IDENTIFIER: Type = value
const IDENTIFIER = value  # Type inferred
```

### Naming Convention
- **MUST use ALL_CAPS** (enforced by naming pattern detection)
- Compile-time constant (cannot change)
- Global scope or module scope

### Examples
```simple
const MAX_SIZE: u64 = 1024
const DEFAULT_PORT = 8080
const PI = 3.14159
```

### Parser Implementation
- Lexer: `"const"` → `TokenKind::Const` (lexer/identifiers.rs:149)
- Parser: `parse_const()` (parser_impl/core.rs:304)
- AST: Stored as const declaration statement

### Usage in Stdlib
```bash
$ grep -r "^const " simple/std_lib/src --include="*.spl" | wc -l
24
```

Examples:
- `simple/std_lib/src/units/time.spl`: Time constants
- `simple/std_lib/src/units/size.spl`: Size constants
- `simple/std_lib/src/layout/markers.spl`: Event markers

## 2. Val Declarations (Scala-Style)

### Syntax
```simple
val identifier = value        # Type inferred
val identifier: Type = value  # Type annotation (Scala-style)
```

### Type Annotation Support
✅ **Type annotations ARE supported (Scala-compatible):**
```simple
val x: u64 = 42
val name: String = "Alice"
val count: Int = 100
```

✅ **Suffix literals also work:**
```simple
val x = 42_u64   # Alternative to type annotation
```

**Status:** ✅ FULLY WORKING
- Parser support: `src/parser/src/stmt_parsing/var_decl.rs:111` (`parse_optional_type_annotation()`)
- Verified with: `simple/std_lib/test/features/syntax/val_var_type_annotation_spec.spl`

### Naming Convention
- lowercase (immutable pattern)
- ends with `_` for mutable variables
- PascalCase for types
- ALL_CAPS for constants

### Examples
```simple
val name = "Alice"
val count = 42
val size = 1024_u64  # Type via suffix
```

### Parser Implementation
- Lexer: `"val"` → `TokenKind::Val`
- Parser: Handles variable declarations
- AST: Let statement with immutable flag

## 3. Pointer Types (*const T, *mut T)

### Expected Syntax (FFI)
```simple
extern fn func(data: *const u8) -> i32  # Const pointer
extern fn func(data: *mut u8) -> i32    # Mutable pointer
```

### Current Status: **BROKEN** 🐛

**Error:**
```
error: parse error: Unexpected token: expected identifier, found Const
```

**Root Cause:**

In `src/parser/src/parser_types.rs:89-95`:

```rust
TokenKind::Star => {
    self.advance();
    let inner = self.parse_single_type()?;  // ❌ Fails here
    return Ok(Type::Pointer {
        kind: PointerKind::Shared,
        inner: Box::new(inner),
    });
}
```

The parser:
1. Sees `*` (Star token) ✓
2. Advances ✓
3. Calls `parse_single_type()` ✓
4. `parse_single_type()` expects an identifier
5. Sees `const` keyword token ❌
6. Error: "expected identifier, found Const"

### Comparison: &mut T (Working)

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

### Expected Fix

```rust
TokenKind::Star => {
    self.advance();

    // Check for *const T or *mut T
    let kind = if self.check(&TokenKind::Const) {
        self.advance();
        PointerKind::RawConst  // New variant needed
    } else if self.check(&TokenKind::Mut) {
        self.advance();
        PointerKind::RawMut    // New variant needed
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

### Blocked Usages

```bash
$ grep -r "\*const" simple/std_lib/src --include="*.spl" | wc -l
98
```

Examples:
- **Vulkan FFI** (11 usages):
  - `extern fn rt_vk_buffer_upload(buffer_handle: u64, data: *const u8, size: u64) -> i32`
  - `extern fn rt_vk_kernel_compile(device_handle: u64, spirv: *const u8, spirv_size: u64) -> u64`

- **Memory Management** (3 usages):
  - `extern fn native_memcpy(dst: *mut u8, src: *const u8, size: u64)`
  - `struct Arena { ptr: *const u8 }`

- **Native UI** (2 usages):
  - `extern fn native_window_create(title_ptr: *const u8, title_len: u64, width: u32, height: u32) -> WindowHandle`

## Summary Table

| Feature | Keyword | Type Annotation | Mutability | Naming | Scope | Status |
|---------|---------|-----------------|------------|--------|-------|--------|
| Const declaration | `const` | Required | Immutable | ALL_CAPS | Global/Module | ✅ Working |
| Val variable | `val` | ✅ Optional (Scala-style) | Immutable | lowercase | Local/Global | ✅ Working |
| Const pointer | `*const T` | In type position | N/A (FFI) | N/A | FFI only | ✅ **FIXED** |

## Unified Keyword Reference

Simple uses **4 keywords** for variables and mutability (Scala-compatible where applicable):

| Keyword | Role | Scala Equivalent | Description |
|---------|------|------------------|-------------|
| `val` | Immutable binding | `val` ✅ | Cannot reassign after initialization |
| `var` | Mutable binding | `var` ✅ | Can be reassigned |
| `const` | Compile-time constant | N/A (Simple extension) | Evaluated at compile time, global scope |
| `mut` | Mutable capability/pointer | N/A (Simple extension) | Memory safety reference capability |

### Two Orthogonal Concepts

Simple separates **binding mutability** from **reference capability**:

1. **Binding Mutability** (`val`/`var`) - Can the variable be reassigned?
2. **Reference Capability** (`mut T`/`iso T`/`T`) - What operations are allowed on the value?

```simple
val x: mut T = value    # Cannot reassign x, but x's contents are mutable
var y: T = value        # Can reassign y, but y's contents are read-only
```

### Keyword Comparison

| Feature | `val` | `var` | `const` | `mut` |
|---------|-------|-------|---------|-------|
| Reassignable | ❌ | ✅ | ❌ | N/A |
| Compile-time | ❌ | ❌ | ✅ | N/A |
| Scope | Local/Global | Local/Global | Global/Module | Type modifier |
| Naming | lowercase | lowercase_ | ALL_CAPS | N/A |
| Type annotation | ✅ Optional (Scala) | ✅ Optional (Scala) | Optional | N/A |

### Reference Capabilities (Simple Extension)

```simple
fn read(x: T) -> Unit           # Shared (immutable reference)
fn modify(x: mut T) -> Unit     # Exclusive (mutable reference)
fn transfer(x: iso T) -> Unit   # Isolated (transferable ownership)
```

### Removed/Unused Keywords

| Keyword | Status | Reason |
|---------|--------|--------|
| `immut` | **Not used** | Redundant - absence of `mut` = immutable |
| `let` | **Deprecated** | Use `val`/`var` instead (Scala-style) |

## Recommendations

### For Users

✅ **Parser bug fixed** (2026-01-17):

1. **FFI pointers now work:**
   ```simple
   use ui.gui.vulkan_ffi.*  # ✅ Works now
   extern fn func(data: *const u8, len: u64) -> i32
   extern fn write(data: *mut u8, len: u64) -> i32
   ```

2. **Type annotations fully supported (Scala-style):**
   ```simple
   val x: u64 = 42          # ✅ Preferred (explicit)
   val x = 42_u64           # ✅ Alternative (suffix)
   var count: Int = 0       # ✅ Scala-compatible
   ```

### Implementation Complete

✅ **Parser fix completed** (2026-01-17):

1. Added `PointerKind::RawConst` and `PointerKind::RawMut` enum variants
2. Modified `parser_types.rs:89-106` to check for `const`/`mut` after `*`
3. Updated 10 files across parser, AST, HIR, and codegen
4. Verified all test cases pass, no regressions
5. Unblocked 98+ FFI declarations in stdlib

## Related Files

- **Token definition:** `src/parser/src/token.rs`
- **Lexer:** `src/parser/src/lexer/identifiers.rs`
- **Type parser:** `src/parser/src/parser_types.rs`
- **Const parser:** `src/parser/src/stmt_parsing/var_decl.rs`
- **SSpec tests:**
  - `simple/std_lib/test/features/syntax/const_vs_val_spec.spl`
  - `simple/std_lib/test/features/bugs/pointer_const_parsing_bug_spec.spl`

## References

- Original issue: User reported "val x : u64 = 42 cause error"
- Parser bug discovered during Vulkan FFI implementation
- Bug report: `simple/bug_report_const_pointer_parsing.md`
