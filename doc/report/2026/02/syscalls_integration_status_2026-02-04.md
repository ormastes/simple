# Syscall Integration Status - Gap Analysis

**Date:** 2026-02-04
**Discovery:** Syscall functions exist but are not integrated into runtime

## Problem Summary

The syscall-based FFI functions have been implemented and work correctly, but they are **not actually being used** by the Simple runtime.

### Current Architecture

```
Simple Language Code
       ↓
Runtime FFI (std-based implementations)
       ↓
std::fs, std::env, std::process
       ↓
Rust Standard Library
```

### Expected Architecture

```
Simple Language Code
       ↓
Runtime FFI (syscall-based implementations)
       ↓
ffi_syscalls (direct POSIX syscalls)
       ↓
libc (minimal)
```

## Discovery Details

### What Exists

1. **ffi_syscalls crate** ✅
   - Location: `rust/ffi_syscalls/`
   - Size: 13 KB compiled
   - Functions: 23 syscall implementations
   - Dependencies: Only libc
   - Status: Fully implemented and working

2. **syscalls_ffi.rs** ✅
   - Location: `rust/runtime/src/syscalls_ffi.rs`
   - Purpose: Extern declarations for syscall functions
   - Status: Declarations only, not exported or used

3. **Runtime FFI** ✅
   - Location: `rust/runtime/src/value/ffi/`
   - Implementation: std-based (std::fs, std::env, etc.)
   - Status: Working, currently in use

### What Doesn't Exist

1. **Integration layer** ❌
   - No code connects syscall functions to runtime
   - Runtime doesn't call ffi_syscalls
   - Simple code uses std-based implementations

2. **Conditional compilation** ❌
   - No feature flags to choose syscall vs std
   - Bootstrap profile uses same std code as release

## Verification Results Explained

The manual verification test that showed "13/23 functions working" was actually testing:
- ✅ Runtime's std-based implementations (what Simple currently uses)
- ❌ NOT the syscall-based implementations we created

The syscall functions work (we tested them directly), but Simple code never calls them.

## Why Binary Size Reduction Worked

The bootstrap build is 13M (vs 27M release) due to:
- Symbol stripping (`strip = true`)
- Size optimization (`opt-level = "z"`)
- LTO (`lto = true`)

**NOT** because of syscall usage (syscalls aren't being used yet).

## Integration Options

### Option 1: Replace Runtime FFI (Breaking Change)

**Action:** Replace std-based implementations with syscall calls

**Example:**
```rust
// Before (runtime/src/value/ffi/env_process.rs):
pub fn rt_env_cwd() -> String {
    std::env::current_dir()
        .unwrap()
        .to_string_lossy()
        .into_owned()
}

// After:
pub fn rt_env_cwd() -> String {
    unsafe {
        let ptr = ffi_syscalls::rt_env_cwd();
        // Convert C string to Rust String
        let c_str = CStr::from_ptr(ptr);
        let result = c_str.to_string_lossy().into_owned();
        libc::free(ptr as *mut libc::c_void);
        result
    }
}
```

**Impact:**
- ✅ Reduces dependencies
- ✅ Smaller binary
- ❌ Breaks if syscalls fail
- ❌ More unsafe code
- ❌ Larger change scope

### Option 2: Conditional Compilation (Non-Breaking)

**Action:** Use feature flags to choose implementation

**Example:**
```rust
#[cfg(feature = "syscall-ffi")]
pub fn rt_env_cwd() -> String {
    // Use syscall version
    unsafe { syscall_env_cwd() }
}

#[cfg(not(feature = "syscall-ffi"))]
pub fn rt_env_cwd() -> String {
    // Use std version
    std::env::current_dir()
        .unwrap()
        .to_string_lossy()
        .into_owned()
}
```

**Cargo.toml:**
```toml
[features]
default = []
syscall-ffi = []  # Enable syscall-based FFI

[profile.bootstrap]
# Enable syscalls for minimal builds
inherits = "release"
features = ["syscall-ffi"]
```

**Impact:**
- ✅ Non-breaking (std version still works)
- ✅ Opt-in for minimal builds
- ✅ Can test both implementations
- ❌ Maintains duplicate code
- ❌ More complex build configuration

### Option 3: Hybrid Approach (Best of Both)

**Action:** Use syscalls for simple operations, std for complex ones

**Categories:**
- **Syscalls:** file_exists, file_read, file_write, env_get, getpid (simple ops)
- **Std:** file_copy, dir_walk, process_spawn (complex ops requiring safety/features)

**Impact:**
- ✅ Gradual migration
- ✅ Best performance for each case
- ✅ Maintains safety where needed
- ❌ Requires careful categorization
- ❌ Mixed implementation styles

### Option 4: Do Nothing (Current State)

**Action:** Keep syscalls as separate library, runtime uses std

**Impact:**
- ✅ No additional work
- ✅ Both implementations available
- ❌ Doesn't achieve dependency reduction goal
- ❌ Syscall work not utilized
- ❌ Missed binary size opportunity

## Recommendation

**Adopt Option 2: Conditional Compilation**

### Rationale

1. **Non-breaking:** Existing code continues to work
2. **Flexible:** Users choose std (safe) or syscall (minimal) builds
3. **Testable:** Can verify both implementations
4. **Gradual:** Can migrate functions one by one

### Implementation Plan

#### Step 1: Add Feature Flag

```toml
# runtime/Cargo.toml
[features]
default = []
syscall-ffi = []
```

#### Step 2: Implement Conditional Wrappers

For each of the 23 functions, create conditional wrapper:

```rust
// runtime/src/value/ffi/env_process.rs

#[cfg(feature = "syscall-ffi")]
pub fn rt_env_cwd() -> String {
    use crate::syscalls_ffi;
    unsafe {
        let ptr = syscalls_ffi::rt_env_cwd();
        if ptr.is_null() {
            return String::new();
        }
        let c_str = std::ffi::CStr::from_ptr(ptr);
        let result = c_str.to_string_lossy().into_owned();
        libc::free(ptr as *mut libc::c_void);
        result
    }
}

#[cfg(not(feature = "syscall-ffi"))]
pub fn rt_env_cwd() -> String {
    std::env::current_dir()
        .map(|p| p.to_string_lossy().into_owned())
        .unwrap_or_default()
}
```

#### Step 3: Update Build Profiles

```toml
# Cargo.toml (workspace)
[profile.bootstrap]
inherits = "release"
opt-level = "z"
lto = true
codegen-units = 1
panic = "abort"
strip = true

# Enable syscall FFI for minimal builds
[profile.bootstrap.package.simple-runtime]
features = ["syscall-ffi"]
```

#### Step 4: Test Both Configurations

```bash
# Test std version (default)
cargo test

# Test syscall version
cargo test --features syscall-ffi

# Build bootstrap with syscalls
cargo build --profile bootstrap
```

### Expected Results

With syscalls enabled:
- **Binary size:** ~10M (vs current 13M, 25% additional reduction)
- **Dependencies:** 3-5 fewer crates
- **Functionality:** Same as std version
- **Risk:** Low (fallback to std available)

## Current Work Required

To complete the integration:

1. **Add conditional compilation** (13 functions) - 2-3 hours
   - rt_file_exists, rt_file_read_text, rt_file_write_text, rt_file_delete, rt_file_size
   - rt_file_copy, rt_file_append_text
   - rt_env_cwd, rt_env_get, rt_env_home
   - rt_getpid, rt_system_cpu_count, rt_hostname

2. **Export syscalls_ffi module** - 30 minutes
   - Add `pub mod syscalls_ffi;` to runtime/src/lib.rs
   - Export wrapper functions

3. **Update build configuration** - 30 minutes
   - Add feature flag
   - Configure bootstrap profile

4. **Test both configurations** - 1 hour
   - Verify std build works
   - Verify syscall build works
   - Compare binary sizes

**Total effort:** ~4-5 hours

## Conclusion

The syscall-based FFI system has been successfully created but **not yet integrated** into the runtime. The 90% completion status is accurate - the hard work is done, but the final integration step remains.

**Current State:**
- ✅ Syscall functions implemented and working
- ✅ Binaries built and optimized
- ❌ Syscalls not actually used by runtime
- ❌ No dependency reduction benefit realized

**Next Steps:**
1. Implement conditional compilation (recommended)
2. Test both std and syscall versions
3. Measure actual dependency and size improvements
4. Update documentation with integration results

---

**Analysis Date:** 2026-02-04
**Status:** Integration pending
**Estimated Completion:** 4-5 hours of work remaining
