# Simple Language FFI/ABI Specification

**Version:** 2025-12
**Status:** Specification

This document defines the Foreign Function Interface (FFI) and Application Binary Interface (ABI) for interoperability between Simple and native code (C, Rust).

---

## 1. Overview

Simple provides a stable, explicit FFI/ABI surface for:

1. **Calling C/Rust functions from Simple**
2. **Exposing Simple functions to C/Rust**
3. **Sharing data structures across language boundaries**
4. **Memory ownership conventions**

All FFI operations require explicit `#[unsafe]` or `#[concurrency_mode(unsafe)]` context.

---

## 2. Extern Function Declarations

### 2.1 Importing C Functions

```simple
#[unsafe]
mod ffi

# Import C function with explicit signature
extern "C" fn malloc(size: usize) -> *mut u8

extern "C" fn free(ptr: *mut u8)

extern "C" fn strlen(s: *const u8) -> usize

# With library specification
extern "C" from "libssl":
    fn SSL_new(ctx: *mut SSLContext) -> *mut SSL
    fn SSL_free(ssl: *mut SSL)
```

### 2.2 Importing Rust Functions

```simple
#[unsafe]
mod rust_interop

# Import Rust function (uses Rust ABI)
extern "Rust" fn rust_helper(data: *const u8, len: usize) -> i64

# From specific crate
extern "Rust" from "my_crate":
    fn process_data(input: Slice[u8]) -> Result[Vec[u8], Error]
```

### 2.3 Exporting Simple Functions

```simple
#[unsafe]
#[export("C")]
fn simple_callback(x: i32, y: i32) -> i32:
    return x + y

#[export("Rust")]
fn simple_rust_api(data: Slice[u8]) -> Vec[u8]:
    return data.to_vec()
```

---

## 3. ABI Conventions

### 3.1 Calling Conventions

| ABI | Convention | Use Case |
|-----|------------|----------|
| `"C"` | C calling convention (cdecl) | C interop, system calls |
| `"Rust"` | Rust calling convention | Rust crate interop |
| `"Simple"` | Simple native (default) | Internal, not stable |

### 3.2 Platform-Specific ABIs

```simple
# Windows-specific
extern "C-stdcall" fn MessageBoxA(hwnd: *mut void, text: *const u8, caption: *const u8, type: u32) -> i32

# System V (Linux/macOS)
extern "C-sysv" fn syscall(num: i64, ...) -> i64
```

---

## 4. Data Layout and repr

### 4.1 repr Attributes

```simple
# C-compatible layout (stable, predictable)
#[repr(C)]
struct CPoint:
    x: f64
    y: f64

# Packed layout (no padding)
#[repr(C, packed)]
struct PackedHeader:
    magic: u32
    version: u16
    flags: u16

# Aligned layout
#[repr(C, align(16))]
struct AlignedData:
    data: [u8; 64]
```

### 4.2 Layout Rules

| repr | Field Order | Padding | Size |
|------|-------------|---------|------|
| (none) | Optimized | Optimized | Minimum |
| `C` | Declaration order | C rules | Predictable |
| `C, packed` | Declaration order | None | Sum of fields |
| `C, align(N)` | Declaration order | C + alignment | Aligned to N |

### 4.3 Primitive Type Mapping

| Simple Type | C Type | Rust Type | Size |
|-------------|--------|-----------|------|
| `i8` | `int8_t` | `i8` | 1 |
| `i16` | `int16_t` | `i16` | 2 |
| `i32` | `int32_t` | `i32` | 4 |
| `i64` | `int64_t` | `i64` | 8 |
| `u8` | `uint8_t` | `u8` | 1 |
| `u16` | `uint16_t` | `u16` | 2 |
| `u32` | `uint32_t` | `u32` | 4 |
| `u64` | `uint64_t` | `u64` | 8 |
| `f32` | `float` | `f32` | 4 |
| `f64` | `double` | `f64` | 8 |
| `bool` | `_Bool` | `bool` | 1 |
| `usize` | `size_t` | `usize` | ptr |
| `isize` | `ptrdiff_t` | `isize` | ptr |

### 4.4 Pointer Type Mapping

| Simple Pointer | C Equivalent | Ownership |
|----------------|--------------|-----------|
| `*const T` | `const T*` | Non-owning |
| `*mut T` | `T*` | Non-owning |
| `&T` (unique) | `T*` (move) | Caller owns |
| `*T` (shared) | N/A | Ref-counted |
| `CStr` | `const char*` | Borrowed |
| `CString` | `char*` | Owned |

---

## 5. String Conventions

### 5.1 C Strings

```simple
#[unsafe]
mod c_strings

use ffi.{CStr, CString}

# Borrowing a C string (null-terminated)
fn use_c_string(s: CStr):
    let len = strlen(s.as_ptr())
    print("Length: {len}")

# Creating a C string
fn create_c_string() -> CString:
    return CString.from_str("hello")

# Converting between Simple string and C string
fn convert():
    let simple_str: str = "hello"
    let c_str: CString = simple_str.to_cstring()  # Allocates
    let back: str = c_str.to_str()                # Borrows
```

### 5.2 Buffer Conventions

```simple
# Slice as pointer + length (common C pattern)
extern "C" fn process_buffer(data: *const u8, len: usize) -> i32

fn call_process(data: Slice[u8]) -> i32:
    unsafe:
        return process_buffer(data.as_ptr(), data.len())

# Output buffer pattern
extern "C" fn fill_buffer(out: *mut u8, capacity: usize) -> usize

fn get_data() -> Vec[u8]:
    let mut buf = Vec.with_capacity(1024)
    unsafe:
        let written = fill_buffer(buf.as_mut_ptr(), buf.capacity())
        buf.set_len(written)
    return buf
```

---

## 6. Ownership Conventions

### 6.1 Ownership Attributes

```simple
# Caller retains ownership, callee borrows
extern "C" fn read_data(#[borrow] data: *const u8, len: usize)

# Caller transfers ownership to callee
extern "C" fn take_ownership(#[owned] data: *mut u8)

# Callee returns owned memory (caller must free)
extern "C" fn create_data() -> #[owned] *mut u8

# Callee returns borrowed reference (valid until X)
extern "C" fn get_static() -> #[static] *const u8
```

### 6.2 Memory Management Contracts

| Attribute | Meaning | Caller Responsibility |
|-----------|---------|----------------------|
| `#[borrow]` | Temporary access | Keep valid during call |
| `#[owned]` | Ownership transfer | None (transferred) |
| `#[static]` | Static lifetime | None |
| `#[out]` | Output parameter | Provide valid pointer |

### 6.3 Allocator Conventions

```simple
# Use specific allocator for FFI memory
#[unsafe]
fn allocate_for_c(size: usize) -> *mut u8:
    return libc.malloc(size)

fn free_from_c(ptr: *mut u8):
    libc.free(ptr)

# Custom allocator interface
trait FFIAllocator:
    fn alloc(size: usize, align: usize) -> *mut u8
    fn dealloc(ptr: *mut u8, size: usize, align: usize)
```

---

## 7. Callback Support

### 7.1 Function Pointers

```simple
# C function pointer type
type CCallback = extern "C" fn(i32, i32) -> i32

# Register callback with C library
extern "C" fn register_callback(cb: CCallback)

# Create callback from Simple closure (no captures)
fn setup_callback():
    let cb: CCallback = \x, y: x + y
    unsafe:
        register_callback(cb)
```

### 7.2 Callbacks with Context

```simple
# C callback with user data
type CCallbackWithData = extern "C" fn(*mut void, i32) -> i32

extern "C" fn register_with_data(cb: CCallbackWithData, user_data: *mut void)

# Wrapper for Simple closure with captures
fn setup_closure_callback(state: MyState):
    let boxed = Box.new(state)
    let ptr = Box.into_raw(boxed)

    extern "C" fn trampoline(user_data: *mut void, x: i32) -> i32:
        unsafe:
            let state = user_data as *mut MyState
            return (*state).process(x)

    unsafe:
        register_with_data(trampoline, ptr as *mut void)
```

---

## 8. Struct and Enum FFI

### 8.1 C-Compatible Structs

```simple
#[repr(C)]
struct FFIResult:
    success: bool
    error_code: i32
    data_ptr: *const u8
    data_len: usize

extern "C" fn process() -> FFIResult
```

### 8.2 C-Compatible Enums

```simple
# Integer-based enum (C-compatible)
#[repr(C)]
enum Status:
    Ok = 0
    Error = 1
    Pending = 2

# With explicit discriminant type
#[repr(C, u8)]
enum SmallStatus:
    Ok = 0
    Error = 1
```

### 8.3 Tagged Unions (Rust-style)

```simple
# Not directly C-compatible, but can be made so
#[repr(C)]
struct CResult:
    tag: u8           # 0 = Ok, 1 = Err
    union:
        ok_value: i64
        err_code: i32
```

---

## 9. Error Handling

### 9.1 C-Style Error Codes

```simple
# Return code convention
extern "C" fn operation() -> i32  # 0 = success, negative = error

fn safe_operation() -> Result[void, i32]:
    unsafe:
        let code = operation()
        if code < 0:
            return Err(code)
        return Ok(())
```

### 9.2 Error Output Parameters

```simple
extern "C" fn parse(input: *const u8, out_error: *mut i32) -> *mut ParsedData

fn safe_parse(input: str) -> Result[ParsedData, i32]:
    let mut error: i32 = 0
    unsafe:
        let result = parse(input.as_ptr(), &mut error)
        if result.is_null():
            return Err(error)
        return Ok(*result)
```

### 9.3 Panic Safety

```simple
# Catch panics at FFI boundary
#[export("C")]
#[catch_panic]
fn exported_function(x: i32) -> i32:
    # If this panics, returns -1 instead of unwinding
    return risky_operation(x)
```

---

## 10. Platform-Specific Declarations

### 10.1 Conditional Compilation

```simple
#[cfg(target_os = "windows")]
extern "C-stdcall" fn WinApi()

#[cfg(target_os = "linux")]
extern "C" fn LinuxApi()

#[cfg(target_arch = "x86_64")]
extern "C" fn x64_specific()
```

### 10.2 Library Linking

```simple
# Link against specific library
#[link(name = "ssl")]
#[link(name = "crypto")]
extern "C" from "openssl":
    fn SSL_library_init() -> i32

# Static vs dynamic linking
#[link(name = "mylib", kind = "static")]
extern "C":
    fn static_function()

#[link(name = "mylib", kind = "dylib")]
extern "C":
    fn dynamic_function()
```

---

## 11. Safety Rules

### 11.1 Unsafe Boundary

All FFI operations MUST be within an unsafe context:

```simple
# Module-level unsafe
#[unsafe]
mod ffi_module

# Block-level unsafe
fn safe_wrapper():
    let result = unsafe:
        dangerous_ffi_call()
    process(result)
```

### 11.2 Invariants

| Rule | Description |
|------|-------------|
| **Null checks** | Raw pointers may be null; must check before deref |
| **Lifetime** | Borrowed pointers must remain valid for call duration |
| **Ownership** | Transferred ownership must not be used after transfer |
| **Alignment** | Pointers must be properly aligned for their type |
| **Initialization** | Memory must be initialized before read |

### 11.3 Forbidden Operations

```simple
# These are NEVER safe, even in unsafe blocks:
# - Dereferencing null pointers without check
# - Creating references to unaligned memory
# - Calling C functions with wrong types
# - Returning borrowed pointers to freed memory
```

---

## 12. Diagnostics

### 12.1 FFI Lints

| Lint | Default | Description |
|------|---------|-------------|
| `ffi_unsafe_missing` | error | FFI without unsafe context |
| `ffi_repr_missing` | warn | Struct in FFI without repr(C) |
| `ffi_ownership_unclear` | warn | Pointer without ownership annotation |
| `ffi_null_unchecked` | warn | Pointer deref without null check |

### 12.2 Error Messages

```
error[E0501]: extern function requires unsafe context
  --> src/ffi.spl:10:5
   |
10 |     malloc(100)
   |     ^^^^^^^^^^^ this call is unsafe
   |
   = help: wrap in `unsafe { ... }` block or mark function as #[unsafe]

warning[W0301]: struct used in FFI should have #[repr(C)]
  --> src/types.spl:5:1
   |
 5 | struct Point:
   | ^^^^^^^^^^^^^ may have unpredictable layout
   |
   = help: add #[repr(C)] for stable C-compatible layout
```

---

## 13. Implementation Checklist

| Feature ID | Feature | Status |
|------------|---------|--------|
| #1116 | `extern "C"` function import | 📋 |
| #1117 | `extern "Rust"` function import | 📋 |
| #1118 | `#[export("C")]` function export | 📋 |
| #1119 | `#[repr(C)]` struct layout | 📋 |
| #1120 | `#[repr(packed)]` layout | 📋 |
| #1121 | `#[repr(align(N))]` layout | 📋 |
| #1122 | C string types (CStr, CString) | 📋 |
| #1123 | Raw pointer types (*const, *mut) | 📋 |
| #1124 | Ownership annotations (#[borrow], #[owned]) | 📋 |
| #1125 | Function pointer types | 📋 |
| #1126 | Callback trampolines | 📋 |
| #1127 | `#[link]` library specification | 📋 |
| #1128 | Platform-specific ABIs | 📋 |
| #1129 | FFI safety lints | 📋 |
| #1130 | `#[catch_panic]` for exports | 📋 |

---

## Related Documents

- [Memory and Ownership](memory.md)
- [Concurrency Modes](language_enhancement.md) - Section 4 (unsafe mode)
- [Types](types.md)
