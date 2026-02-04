# Rust FFI Implementation Plan

**Date:** 2026-02-04
**Status:** 🔄 READY TO IMPLEMENT
**Prerequisites:** ✅ Simple-side complete

## Overview

Implement Rust FFI functions for mmap and executable memory operations to enable the 44 JIT instantiator tests to pass.

## Implementation Tasks

### Task 1: Create mmap FFI Module

**File:** `rust/runtime/src/ffi/mmap.rs` (new)

**Functions to Implement:**

```rust
use libc::{mmap, munmap, mprotect, madvise, msync, mlock, munlock};
use std::ffi::CString;
use std::fs::File;
use std::os::unix::io::AsRawFd;

#[no_mangle]
pub extern "C" fn rt_mmap_file(
    path: *const c_char,
    prot: i32,
    flags: i32,
    offset: i64,
    length: i64,
) -> (i64, i64) {
    // 1. Convert path to Rust string
    let path_str = unsafe { CStr::from_ptr(path).to_str().unwrap() };

    // 2. Open file
    let file = match File::open(path_str) {
        Ok(f) => f,
        Err(_) => return (0, 0),
    };

    // 3. Get file size if length == 0
    let size = if length == 0 {
        file.metadata().map(|m| m.len() as i64).unwrap_or(0)
    } else {
        length
    };

    // 4. Call mmap(2)
    let addr = unsafe {
        mmap(
            std::ptr::null_mut(),
            size as size_t,
            prot,
            flags,
            file.as_raw_fd(),
            offset,
        )
    };

    // 5. Check for error
    if addr == libc::MAP_FAILED {
        return (0, 0);
    }

    (addr as i64, size)
}

#[no_mangle]
pub extern "C" fn rt_munmap(address: i64, size: i64) -> bool {
    let result = unsafe {
        munmap(address as *mut c_void, size as size_t)
    };
    result == 0
}

#[no_mangle]
pub extern "C" fn rt_mmap_read_bytes(
    address: i64,
    offset: i64,
    length: i64,
) -> *mut RuntimeValue {
    // Create byte array from memory
    let slice = unsafe {
        std::slice::from_raw_parts(
            (address + offset) as *const u8,
            length as usize,
        )
    };

    // Convert to RuntimeValue array
    RuntimeValue::from_bytes(slice)
}

#[no_mangle]
pub extern "C" fn rt_mmap_read_string(
    address: i64,
    offset: i64,
    max_length: i64,
) -> *mut RuntimeValue {
    let start = (address + offset) as *const u8;

    let str_slice = if max_length == 0 {
        // Read until null terminator
        unsafe { CStr::from_ptr(start as *const c_char).to_bytes() }
    } else {
        // Read up to max_length
        unsafe {
            std::slice::from_raw_parts(start, max_length as usize)
        }
    };

    let string = String::from_utf8_lossy(str_slice).into_owned();
    RuntimeValue::from_string(string)
}

#[no_mangle]
pub extern "C" fn rt_file_size_for_mmap(path: *const c_char) -> i64 {
    let path_str = unsafe { CStr::from_ptr(path).to_str().unwrap() };
    std::fs::metadata(path_str)
        .map(|m| m.len() as i64)
        .unwrap_or(-1)
}

#[no_mangle]
pub extern "C" fn rt_get_page_size() -> i64 {
    unsafe { libc::sysconf(libc::_SC_PAGESIZE) }
}

#[no_mangle]
pub extern "C" fn rt_msync(address: i64, size: i64, is_async: bool) -> bool {
    let flags = if is_async {
        libc::MS_ASYNC
    } else {
        libc::MS_SYNC
    };

    let result = unsafe {
        msync(address as *mut c_void, size as size_t, flags)
    };
    result == 0
}

#[no_mangle]
pub extern "C" fn rt_mlock(address: i64, size: i64) -> bool {
    let result = unsafe {
        mlock(address as *const c_void, size as size_t)
    };
    result == 0
}

#[no_mangle]
pub extern "C" fn rt_munlock(address: i64, size: i64) -> bool {
    let result = unsafe {
        munlock(address as *const c_void, size as size_t)
    };
    result == 0
}

#[no_mangle]
pub extern "C" fn rt_madvise(address: i64, size: i64, advice: i32) -> bool {
    let result = unsafe {
        madvise(address as *mut c_void, size as size_t, advice)
    };
    result == 0
}
```

**Estimated Time:** 2-3 hours
**Testing:** Use existing mmap system calls, straightforward

---

### Task 2: Create Executable Memory FFI Module

**File:** `rust/runtime/src/ffi/exec_memory.rs` (new)

**Functions to Implement:**

```rust
use libc::{mmap, munmap, mprotect, PROT_READ, PROT_WRITE, PROT_EXEC};
use std::sync::Mutex;

// Track allocated regions for statistics
static EXEC_ALLOCATIONS: Mutex<Vec<(i64, i64)>> = Mutex::new(Vec::new());

#[no_mangle]
pub extern "C" fn rt_alloc_exec_memory(size: i64) -> i64 {
    let prot = PROT_READ | PROT_WRITE | PROT_EXEC;
    let flags = libc::MAP_PRIVATE | libc::MAP_ANONYMOUS;

    let addr = unsafe {
        mmap(
            std::ptr::null_mut(),
            size as size_t,
            prot,
            flags,
            -1,
            0,
        )
    };

    if addr == libc::MAP_FAILED {
        return 0;
    }

    // Track allocation
    EXEC_ALLOCATIONS.lock().unwrap().push((addr as i64, size));

    addr as i64
}

#[no_mangle]
pub extern "C" fn rt_alloc_rw_memory(size: i64) -> i64 {
    let prot = PROT_READ | PROT_WRITE;
    let flags = libc::MAP_PRIVATE | libc::MAP_ANONYMOUS;

    let addr = unsafe {
        mmap(
            std::ptr::null_mut(),
            size as size_t,
            prot,
            flags,
            -1,
            0,
        )
    };

    if addr == libc::MAP_FAILED {
        return 0;
    }

    addr as i64
}

#[no_mangle]
pub extern "C" fn rt_free_exec_memory(address: i64, size: i64) -> bool {
    let result = unsafe {
        munmap(address as *mut c_void, size as size_t)
    };

    if result == 0 {
        // Remove from tracking
        let mut allocs = EXEC_ALLOCATIONS.lock().unwrap();
        allocs.retain(|(addr, _)| *addr != address);
        true
    } else {
        false
    }
}

#[no_mangle]
pub extern "C" fn rt_write_exec_memory(
    address: i64,
    code: *const RuntimeValue,
    offset: i64,
) -> i64 {
    // Extract bytes from RuntimeValue array
    let bytes = RuntimeValue::to_bytes(code);

    // Write to memory
    unsafe {
        let dest = (address + offset) as *mut u8;
        std::ptr::copy_nonoverlapping(
            bytes.as_ptr(),
            dest,
            bytes.len(),
        );
    }

    bytes.len() as i64
}

#[no_mangle]
pub extern "C" fn rt_make_executable(address: i64, size: i64) -> bool {
    let prot = PROT_READ | PROT_EXEC;
    let result = unsafe {
        mprotect(address as *mut c_void, size as size_t, prot)
    };
    result == 0
}

#[no_mangle]
pub extern "C" fn rt_flush_icache(address: i64, size: i64) {
    // x86/x64: No-op (hardware cache coherence)
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    {
        // Nothing to do
    }

    // ARM: Clear cache
    #[cfg(target_arch = "aarch64")]
    {
        unsafe {
            libc::__clear_cache(
                address as *mut c_char,
                (address + size) as *mut c_char,
            );
        }
    }
}

#[no_mangle]
pub extern "C" fn rt_get_function_pointer(address: i64) -> i64 {
    address  // Function pointer is same as address
}

#[no_mangle]
pub extern "C" fn rt_call_function_0(fn_ptr: i64) -> i64 {
    type Fn0 = extern "C" fn() -> i64;
    let func: Fn0 = unsafe { std::mem::transmute(fn_ptr) };
    func()
}

#[no_mangle]
pub extern "C" fn rt_call_function_1(fn_ptr: i64, arg1: i64) -> i64 {
    type Fn1 = extern "C" fn(i64) -> i64;
    let func: Fn1 = unsafe { std::mem::transmute(fn_ptr) };
    func(arg1)
}

#[no_mangle]
pub extern "C" fn rt_call_function_2(fn_ptr: i64, arg1: i64, arg2: i64) -> i64 {
    type Fn2 = extern "C" fn(i64, i64) -> i64;
    let func: Fn2 = unsafe { std::mem::transmute(fn_ptr) };
    func(arg1, arg2)
}

#[no_mangle]
pub extern "C" fn rt_is_executable(address: i64) -> bool {
    // Check if address is in tracked allocations
    EXEC_ALLOCATIONS.lock().unwrap()
        .iter()
        .any(|(addr, size)| address >= *addr && address < *addr + *size)
}

#[no_mangle]
pub extern "C" fn rt_get_protection(address: i64) -> i32 {
    // Query protection via /proc/self/maps or similar
    // Simplified: return -1 for now
    -1
}

#[no_mangle]
pub extern "C" fn rt_set_protection(address: i64, size: i64, prot: i32) -> bool {
    let result = unsafe {
        mprotect(address as *mut c_void, size as size_t, prot)
    };
    result == 0
}

#[no_mangle]
pub extern "C" fn rt_exec_memory_total() -> i64 {
    EXEC_ALLOCATIONS.lock().unwrap()
        .iter()
        .map(|(_, size)| size)
        .sum()
}

#[no_mangle]
pub extern "C" fn rt_exec_memory_count() -> i64 {
    EXEC_ALLOCATIONS.lock().unwrap().len() as i64
}

#[no_mangle]
pub extern "C" fn rt_exec_memory_dump_stats() {
    let allocs = EXEC_ALLOCATIONS.lock().unwrap();
    eprintln!("=== Executable Memory Statistics ===");
    eprintln!("Total allocations: {}", allocs.len());
    eprintln!("Total memory: {} bytes",
        allocs.iter().map(|(_, s)| s).sum::<i64>());
    for (addr, size) in allocs.iter() {
        eprintln!("  {:016x}: {} bytes", addr, size);
    }
}
```

**Estimated Time:** 3-4 hours
**Testing:** More complex, need to test function calling

---

### Task 3: Register FFI Functions

**File:** `rust/runtime/src/ffi/mod.rs`

Add:
```rust
pub mod mmap;
pub mod exec_memory;

pub fn register_all_ffi() {
    // ... existing registrations ...

    // mmap operations
    register_ffi("rt_mmap_file", mmap::rt_mmap_file);
    register_ffi("rt_munmap", mmap::rt_munmap);
    register_ffi("rt_mmap_read_bytes", mmap::rt_mmap_read_bytes);
    register_ffi("rt_mmap_read_string", mmap::rt_mmap_read_string);
    register_ffi("rt_file_size_for_mmap", mmap::rt_file_size_for_mmap);
    register_ffi("rt_get_page_size", mmap::rt_get_page_size);
    register_ffi("rt_msync", mmap::rt_msync);
    register_ffi("rt_mlock", mmap::rt_mlock);
    register_ffi("rt_munlock", mmap::rt_munlock);
    register_ffi("rt_madvise", mmap::rt_madvise);

    // Executable memory
    register_ffi("rt_alloc_exec_memory", exec_memory::rt_alloc_exec_memory);
    register_ffi("rt_alloc_rw_memory", exec_memory::rt_alloc_rw_memory);
    register_ffi("rt_free_exec_memory", exec_memory::rt_free_exec_memory);
    register_ffi("rt_write_exec_memory", exec_memory::rt_write_exec_memory);
    register_ffi("rt_make_executable", exec_memory::rt_make_executable);
    register_ffi("rt_flush_icache", exec_memory::rt_flush_icache);
    register_ffi("rt_get_function_pointer", exec_memory::rt_get_function_pointer);
    register_ffi("rt_call_function_0", exec_memory::rt_call_function_0);
    register_ffi("rt_call_function_1", exec_memory::rt_call_function_1);
    register_ffi("rt_call_function_2", exec_memory::rt_call_function_2);
    register_ffi("rt_is_executable", exec_memory::rt_is_executable);
    register_ffi("rt_get_protection", exec_memory::rt_get_protection);
    register_ffi("rt_set_protection", exec_memory::rt_set_protection);
    register_ffi("rt_exec_memory_total", exec_memory::rt_exec_memory_total);
    register_ffi("rt_exec_memory_count", exec_memory::rt_exec_memory_count);
    register_ffi("rt_exec_memory_dump_stats", exec_memory::rt_exec_memory_dump_stats);
}
```

**Estimated Time:** 30 minutes

---

### Task 4: Add Dependencies

**File:** `rust/runtime/Cargo.toml`

Ensure `libc` dependency:
```toml
[dependencies]
libc = "0.2"
```

**Estimated Time:** 5 minutes

---

### Task 5: Write Unit Tests

**File:** `rust/runtime/src/ffi/mmap_tests.rs` (new)

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use std::fs::File;
    use std::io::Write;

    #[test]
    fn test_mmap_file() {
        // Create temp file
        let mut file = File::create("/tmp/test_mmap.txt").unwrap();
        file.write_all(b"Hello, mmap!").unwrap();
        drop(file);

        // Map file
        let path = CString::new("/tmp/test_mmap.txt").unwrap();
        let (addr, size) = rt_mmap_file(
            path.as_ptr(),
            PROT_READ,
            MAP_PRIVATE,
            0,
            0,
        );

        assert_ne!(addr, 0);
        assert_eq!(size, 12);

        // Read data
        let bytes = rt_mmap_read_bytes(addr, 0, 12);
        // Verify bytes match "Hello, mmap!"

        // Unmap
        assert!(rt_munmap(addr, size));

        // Cleanup
        std::fs::remove_file("/tmp/test_mmap.txt").unwrap();
    }

    #[test]
    fn test_exec_memory() {
        // x86-64: mov rax, 42; ret
        let code: Vec<u8> = vec![0x48, 0xc7, 0xc0, 0x2a, 0x00, 0x00, 0x00, 0xc3];

        // Allocate
        let addr = rt_alloc_exec_memory(4096);
        assert_ne!(addr, 0);

        // Write code
        let written = rt_write_exec_memory(addr, &code, 0);
        assert_eq!(written, code.len() as i64);

        // Flush cache
        rt_flush_icache(addr, code.len() as i64);

        // Call function
        let fn_ptr = rt_get_function_pointer(addr);
        let result = rt_call_function_0(fn_ptr);
        assert_eq!(result, 42);

        // Cleanup
        assert!(rt_free_exec_memory(addr, 4096));
    }
}
```

**Estimated Time:** 1-2 hours

---

## Implementation Order

1. ✅ Task 4: Add dependencies (5 min)
2. ✅ Task 1: Implement mmap FFI (2-3 hours)
3. ✅ Task 2: Implement exec_memory FFI (3-4 hours)
4. ✅ Task 3: Register FFI functions (30 min)
5. ✅ Task 5: Write unit tests (1-2 hours)
6. ✅ Build and test (30 min)
7. ✅ Run JIT instantiator tests (verify 44 tests pass)

**Total Estimated Time:** 8-11 hours

## Testing Strategy

### Phase 1: Unit Tests (Rust)
```bash
cd rust/runtime
cargo test mmap_tests
cargo test exec_memory_tests
```

### Phase 2: Integration Tests (Simple)
```bash
# Run smoke test
./bin/simple test/compiler/jit_infrastructure_smoke_test.spl

# Run full test suite
./bin/simple test test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

### Phase 3: Manual Verification
```bash
# Check stats
./bin/simple -e '
use app.io.mod (alloc_exec_memory, exec_memory_dump_stats)
val addr = alloc_exec_memory(1024)
exec_memory_dump_stats()
'
```

## Success Criteria

- ✅ All Rust unit tests pass
- ✅ 44 JIT instantiator tests pass
- ✅ mmap operations work correctly
- ✅ Executable memory allocation works
- ✅ Function calls from JIT code work
- ✅ No memory leaks

## Potential Issues

### Issue 1: SELinux/AppArmor Restrictions
**Problem:** System may block RWX memory allocation
**Solution:** Use W^X pattern (allocate RW, write, make RX)

### Issue 2: ARM Cache Coherence
**Problem:** Instruction cache not flushed on ARM
**Solution:** Implement `rt_flush_icache` with `__clear_cache`

### Issue 3: RuntimeValue Conversion
**Problem:** Converting between Simple arrays and Rust Vec
**Solution:** Use existing `RuntimeValue::from_bytes` and `to_bytes`

## Rollback Plan

If issues arise:
1. Keep FFI functions as stubs that return errors
2. Tests remain failing but with clear error messages
3. No breaking changes to existing code

## Documentation Updates

After implementation:
- [ ] Update `doc/guide/jit_infrastructure_quick_start.md` with "works!" status
- [ ] Add examples of actual working JIT code
- [ ] Document any platform-specific quirks
- [ ] Add performance benchmarks

---

**Status:** 📋 READY TO IMPLEMENT
**Next Action:** Create `rust/runtime/src/ffi/mmap.rs` and begin Task 1
