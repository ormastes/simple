# FFI Function Stubs - Implementation Specification

**Purpose:** Define FFI functions needed for migrated Simple code
**Status:** SPECIFICATION - Not yet implemented
**Priority:** P2 (not needed for testing, required for production)

---

## Overview

The Rust to Simple migration created several modules that need FFI connections to the runtime. This document specifies the required functions and their implementations.

## File 1: compiler_control.rs (NEW)

**Location:** `src/runtime/src/value/compiler_control.rs`
**Purpose:** Control compiler behavior flags
**Dependencies:** None (global state)

### Function 1.1: rt_set_macro_trace

**Signature:**
```rust
#[no_mangle]
pub extern "C" fn rt_set_macro_trace(enabled: bool)
```

**Purpose:** Enable/disable macro expansion tracing for debugging

**Implementation:**
```rust
use std::sync::atomic::{AtomicBool, Ordering};

static MACRO_TRACE_ENABLED: AtomicBool = AtomicBool::new(false);

#[no_mangle]
pub extern "C" fn rt_set_macro_trace(enabled: bool) {
    MACRO_TRACE_ENABLED.store(enabled, Ordering::SeqCst);
    if enabled {
        eprintln!("[runtime] Macro tracing enabled");
    }
}

// Public getter for use by compiler
pub fn is_macro_trace_enabled() -> bool {
    MACRO_TRACE_ENABLED.load(Ordering::SeqCst)
}
```

**Usage in Simple:**
```simple
# In arg_parsing.spl
fn apply():
    if macro_trace:
        ffi_call("rt_set_macro_trace", [true])
```

**Testing:**
```rust
#[test]
fn test_macro_trace() {
    rt_set_macro_trace(true);
    assert!(is_macro_trace_enabled());
    
    rt_set_macro_trace(false);
    assert!(!is_macro_trace_enabled());
}
```

---

### Function 1.2: rt_set_debug_mode

**Signature:**
```rust
#[no_mangle]
pub extern "C" fn rt_set_debug_mode(enabled: bool)
```

**Purpose:** Enable/disable debug mode for detailed logging

**Implementation:**
```rust
static DEBUG_MODE_ENABLED: AtomicBool = AtomicBool::new(false);

#[no_mangle]
pub extern "C" fn rt_set_debug_mode(enabled: bool) {
    DEBUG_MODE_ENABLED.store(enabled, Ordering::SeqCst);
    if enabled {
        eprintln!("[runtime] Debug mode enabled");
        // Could also set log level here
        // env::set_var("RUST_LOG", "debug");
    }
}

pub fn is_debug_mode_enabled() -> bool {
    DEBUG_MODE_ENABLED.load(Ordering::SeqCst)
}
```

**Usage in Simple:**
```simple
# In arg_parsing.spl
fn apply():
    if debug_mode:
        ffi_call("rt_set_debug_mode", [true])
```

**Testing:**
```rust
#[test]
fn test_debug_mode() {
    rt_set_debug_mode(true);
    assert!(is_debug_mode_enabled());
    
    rt_set_debug_mode(false);
    assert!(!is_debug_mode_enabled());
}
```

---

## File 2: sandbox.rs (UPDATE/VERIFY)

**Location:** `src/runtime/src/value/sandbox.rs` (may exist)
**Purpose:** Apply sandbox restrictions to running processes
**Dependencies:** libc, seccomp/landlock (platform-specific)

### Function 2.1: rt_apply_sandbox

**Signature:**
```rust
#[no_mangle]
pub extern "C" fn rt_apply_sandbox(
    config_ptr: *const SandboxConfigFFI
) -> i32  // 0 = success, -1 = error
```

**Purpose:** Apply resource limits and security restrictions

**Data Structure:**
```rust
#[repr(C)]
pub struct SandboxConfigFFI {
    time_limit_secs: u64,      // 0 = no limit
    memory_limit_bytes: u64,   // 0 = no limit
    fd_limit: u64,             // 0 = no limit
    thread_limit: u64,         // 0 = no limit
    no_network: bool,
    // Pointers to null-terminated strings
    network_allowlist_ptr: *const *const i8,
    network_allowlist_len: usize,
    network_blocklist_ptr: *const *const i8,
    network_blocklist_len: usize,
    read_paths_ptr: *const *const i8,
    read_paths_len: usize,
    write_paths_ptr: *const *const i8,
    write_paths_len: usize,
}
```

**Implementation (Linux):**
```rust
use libc::{setrlimit, rlimit, RLIMIT_CPU, RLIMIT_AS, RLIMIT_NOFILE, RLIMIT_NPROC};

#[no_mangle]
pub extern "C" fn rt_apply_sandbox(config_ptr: *const SandboxConfigFFI) -> i32 {
    if config_ptr.is_null() {
        return -1;
    }
    
    let config = unsafe { &*config_ptr };
    
    // Apply CPU time limit
    if config.time_limit_secs > 0 {
        let rlim = rlimit {
            rlim_cur: config.time_limit_secs,
            rlim_max: config.time_limit_secs,
        };
        if unsafe { setrlimit(RLIMIT_CPU, &rlim) } != 0 {
            eprintln!("[sandbox] Failed to set CPU limit");
            return -1;
        }
    }
    
    // Apply memory limit
    if config.memory_limit_bytes > 0 {
        let rlim = rlimit {
            rlim_cur: config.memory_limit_bytes,
            rlim_max: config.memory_limit_bytes,
        };
        if unsafe { setrlimit(RLIMIT_AS, &rlim) } != 0 {
            eprintln!("[sandbox] Failed to set memory limit");
            return -1;
        }
    }
    
    // Apply file descriptor limit
    if config.fd_limit > 0 {
        let rlim = rlimit {
            rlim_cur: config.fd_limit,
            rlim_max: config.fd_limit,
        };
        if unsafe { setrlimit(RLIMIT_NOFILE, &rlim) } != 0 {
            eprintln!("[sandbox] Failed to set FD limit");
            return -1;
        }
    }
    
    // Apply thread limit
    if config.thread_limit > 0 {
        let rlim = rlimit {
            rlim_cur: config.thread_limit,
            rlim_max: config.thread_limit,
        };
        if unsafe { setrlimit(RLIMIT_NPROC, &rlim) } != 0 {
            eprintln!("[sandbox] Failed to set thread limit");
            return -1;
        }
    }
    
    // TODO: Network restrictions (requires seccomp or landlock)
    if config.no_network {
        // Implement using seccomp to block socket syscalls
        // Or use landlock on newer kernels
        eprintln!("[sandbox] Network restrictions not yet implemented");
    }
    
    0  // Success
}
```

**Usage in Simple:**
```simple
# In sandbox.spl
fn apply_sandbox(config: SandboxConfig) -> Result<(), text>:
    # Convert Simple config to FFI struct
    val ffi_config = create_ffi_config(config)
    val result = ffi_call("rt_apply_sandbox", [ffi_config])
    
    if result == 0:
        Ok(())
    else:
        Err("Failed to apply sandbox")
```

**Testing:**
```rust
#[test]
fn test_cpu_limit() {
    let config = SandboxConfigFFI {
        time_limit_secs: 5,
        memory_limit_bytes: 0,
        fd_limit: 0,
        thread_limit: 0,
        no_network: false,
        // ... null pointers for lists
    };
    
    assert_eq!(rt_apply_sandbox(&config), 0);
    
    // Verify rlimit was set
    let mut rlim = rlimit { rlim_cur: 0, rlim_max: 0 };
    unsafe { libc::getrlimit(RLIMIT_CPU, &mut rlim) };
    assert_eq!(rlim.rlim_cur, 5);
}
```

---

## Implementation Checklist

### Phase 1: Basic FFI (1-2 hours)

- [ ] Create `src/runtime/src/value/compiler_control.rs`
- [ ] Implement `rt_set_macro_trace()`
- [ ] Implement `rt_set_debug_mode()`
- [ ] Add unit tests for compiler_control
- [ ] Export functions in runtime's lib.rs
- [ ] Update Simple FFI bindings table

### Phase 2: Sandbox FFI (4-6 hours)

- [ ] Check if `src/runtime/src/value/sandbox.rs` exists
- [ ] Define `SandboxConfigFFI` C struct
- [ ] Implement `rt_apply_sandbox()` for Linux
  - [ ] CPU time limit (rlimit RLIMIT_CPU)
  - [ ] Memory limit (rlimit RLIMIT_AS)
  - [ ] FD limit (rlimit RLIMIT_NOFILE)
  - [ ] Thread limit (rlimit RLIMIT_NPROC)
  - [ ] Network restrictions (seccomp - deferred)
  - [ ] File path restrictions (landlock - deferred)
- [ ] Add unit tests for sandbox
- [ ] Export function in runtime's lib.rs
- [ ] Update Simple FFI bindings

### Phase 3: Simple Integration (2-3 hours)

- [ ] Update `arg_parsing.spl` to use real FFI
- [ ] Update `sandbox.spl` to use real FFI
- [ ] Create FFI conversion helpers in Simple
- [ ] Integration tests
- [ ] Documentation updates

---

## Platform Support

### Linux
- ✅ rlimit (CPU, memory, FD, threads)
- ⏸️ seccomp (network restrictions)
- ⏸️ landlock (file restrictions - kernel 5.13+)

### macOS
- ✅ rlimit (limited support)
- ❌ No seccomp equivalent
- ⏸️ Sandbox.h (Apple-specific, complex)

### Windows
- ❌ No rlimit
- ⏸️ Job Objects (alternative approach)
- ⏸️ Network Policy (requires admin)

**Recommendation:** Start with Linux rlimit, add platform guards

---

## Security Considerations

### CRITICAL: Sandbox must be unbypassable

1. **Apply before loading user code**
   - Call `rt_apply_sandbox()` before running Simple script
   - Once set, limits cannot be raised (only lowered)

2. **Validate all limits**
   - Check for integer overflow
   - Verify reasonable ranges
   - Log all applications

3. **Fail closed**
   - If sandbox fails to apply, abort execution
   - Never run untrusted code without sandbox

4. **Audit logging**
   - Log all sandbox applications
   - Log any bypass attempts

### Network restrictions (future)

**Option 1: seccomp (Linux)**
```rust
// Block socket(), connect(), bind(), etc.
use seccomp::*;

fn block_network() -> Result<(), Error> {
    let mut ctx = Context::new(Action::Allow)?;
    ctx.add_rule(Rule::new(
        Syscall::socket,
        Compare::eq(0), // Doesn't matter, we're blocking
        Action::Errno(libc::EACCES),
    ))?;
    ctx.load()?;
    Ok(())
}
```

**Option 2: landlock (Linux 5.13+)**
- More flexible, file-based
- Allows specific network rules
- Newer, less tested

### File restrictions (future)

**landlock example:**
```rust
use landlock::*;

fn restrict_files(allowed_paths: &[PathBuf]) -> Result<(), Error> {
    let mut ruleset = Ruleset::new()
        .handle_fs_access(AccessFs::from_all(ABI::V1))?;
    
    for path in allowed_paths {
        ruleset = ruleset.add_rule(PathFd::new(path)?.allow_read_file())?;
    }
    
    ruleset.apply()?;
    Ok(())
}
```

---

## Error Handling

All FFI functions should:
1. Validate pointers (null checks)
2. Return error codes (0 = success, -1 = error)
3. Log errors to stderr
4. Never panic across FFI boundary

**Example:**
```rust
#[no_mangle]
pub extern "C" fn rt_apply_sandbox(config_ptr: *const SandboxConfigFFI) -> i32 {
    if config_ptr.is_null() {
        eprintln!("[sandbox] ERROR: null config pointer");
        return -1;
    }
    
    match apply_sandbox_internal(unsafe { &*config_ptr }) {
        Ok(()) => 0,
        Err(e) => {
            eprintln!("[sandbox] ERROR: {}", e);
            -1
        }
    }
}
```

---

## Testing Strategy

### Unit Tests (Rust)
- Test each function in isolation
- Mock system calls where possible
- Verify error handling

### Integration Tests (Simple + Rust)
- Test from Simple code
- Verify FFI marshalling
- Test actual sandbox behavior

### Security Tests
- Try to bypass sandbox
- Test with malicious inputs
- Verify fail-closed behavior

---

## Documentation Updates

After implementation:
1. Update arg_parsing migration report
2. Update sandbox migration report
3. Create FFI integration guide
4. Update simple runtime documentation
5. Add security policy document

---

## Timeline Estimate

| Phase | Tasks | Time | Dependencies |
|-------|-------|------|--------------|
| Phase 1 | Compiler control FFI | 1-2h | None |
| Phase 2 | Sandbox rlimit | 2-3h | Phase 1 |
| Phase 3 | Simple integration | 2-3h | Phase 2 |
| Phase 4 | Network/file (future) | 8-12h | seccomp/landlock |

**Total (Phases 1-3):** 5-8 hours
**Total (All phases):** 13-20 hours

---

**Status:** READY FOR IMPLEMENTATION
**Next step:** Create compiler_control.rs and implement Phase 1
