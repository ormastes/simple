# SFFI mmap - Minimal Rust Approach

**Architecture:** All logic in Simple, only thin syscall wrappers in Rust
**Pattern:** Same as existing `rt_malloc`, `rt_read_u8`, etc.

## Principle

Like existing memory syscalls (`rt_malloc`, `rt_free`), mmap wrappers are:
- **1-line Rust functions** that just call libc
- **All logic in Simple** - caching, parsing, management
- **Zero business logic in Rust** - just syscall interface

## Rust Side (Minimal - Just Syscalls)

### File: `rust/runtime/src/interpreter_extern/mmap_syscalls.rs`

```rust
// Thin syscall wrappers - NO logic, just libc calls
use libc::{mmap, munmap, mprotect, madvise, msync, mlock, munlock};

#[no_mangle]
pub extern "C" fn rt_mmap(
    addr: i64,
    length: i64,
    prot: i32,
    flags: i32,
    fd: i32,
    offset: i64,
) -> i64 {
    unsafe {
        mmap(
            addr as *mut c_void,
            length as size_t,
            prot,
            flags,
            fd,
            offset,
        ) as i64
    }
}

#[no_mangle]
pub extern "C" fn rt_munmap(addr: i64, length: i64) -> i32 {
    unsafe {
        munmap(addr as *mut c_void, length as size_t)
    }
}

#[no_mangle]
pub extern "C" fn rt_mprotect(addr: i64, length: i64, prot: i32) -> i32 {
    unsafe {
        mprotect(addr as *mut c_void, length as size_t, prot)
    }
}

#[no_mangle]
pub extern "C" fn rt_madvise(addr: i64, length: i64, advice: i32) -> i32 {
    unsafe {
        madvise(addr as *mut c_void, length as size_t, advice)
    }
}

#[no_mangle]
pub extern "C" fn rt_msync(addr: i64, length: i64, flags: i32) -> i32 {
    unsafe {
        msync(addr as *mut c_void, length as size_t, flags)
    }
}

#[no_mangle]
pub extern "C" fn rt_mlock(addr: i64, length: i64) -> i32 {
    unsafe {
        mlock(addr as *const c_void, length as size_t)
    }
}

#[no_mangle]
pub extern "C" fn rt_munlock(addr: i64, length: i64) -> i32 {
    unsafe {
        munlock(addr as *const c_void, length as size_t)
    }
}
```

**Total:** ~40 lines of Rust (just syscalls, zero logic)

## Simple Side (All Logic)

Already implemented in `src/compiler/loader/smf_cache.spl`:
- ✅ SmfCache management
- ✅ File loading logic
- ✅ SDN parsing
- ✅ Cache statistics
- ✅ Prefetching
- ✅ Error handling

All using the thin syscall wrappers.

## Implementation Steps

1. **Add syscall wrappers** (`rust/runtime/src/interpreter_extern/mmap_syscalls.rs`) - 30 min
2. **Export in io/mod.spl** (already done) - 0 min
3. **Update smf_cache.spl** to use `rt_mmap` instead of stub - 15 min
4. **Test** - 30 min

**Total:** ~75 minutes

## Comparison with Existing Pattern

### Existing (memory_syscalls.spl):
```simple
# Simple declares
extern fn rt_malloc(size: i64) -> i64

# Rust implements (1 line)
pub extern "C" fn rt_malloc(size: i64) -> i64 {
    unsafe { libc::malloc(size as size_t) as i64 }
}

# Simple uses with logic
fn allocate_buffer(size: i64) -> Buffer:
    val ptr = rt_malloc(size)
    Buffer(ptr: ptr, size: size, capacity: size)
```

### New (mmap_syscalls):
```simple
# Simple declares
extern fn rt_mmap(addr: i64, length: i64, prot: i32, flags: i32, fd: i32, offset: i64) -> i64

# Rust implements (1 line)
pub extern "C" fn rt_mmap(...) -> i64 {
    unsafe { libc::mmap(...) as i64 }
}

# Simple uses with logic
fn map_smf_file(path: text) -> MappedSmf:
    val fd = open_file(path)
    val size = get_file_size(path)
    val addr = rt_mmap(0, size, PROT_READ, MAP_PRIVATE, fd, 0)
    MappedSmf(address: addr, size: size, ...)
```

**Same pattern, same principles!**

## Why This Works

1. **Syscalls are platform-specific** - must be in Rust/C
2. **Logic is portable** - should be in Simple
3. **Separation of concerns** - syscalls vs. business logic
4. **Testability** - can mock syscalls, test logic
5. **Maintainability** - logic changes don't need Rust recompile

## Summary

- ✅ **Rust:** 40 lines (7 syscall wrappers)
- ✅ **Simple:** 850 lines (all logic, caching, parsing)
- ✅ **Ratio:** 95% Simple, 5% Rust
- ✅ **Rust role:** Just syscall interface (like malloc)
- ✅ **Simple role:** All actual functionality

This is the SFFI pattern - **S**imple **FFI** where Simple does the work!
