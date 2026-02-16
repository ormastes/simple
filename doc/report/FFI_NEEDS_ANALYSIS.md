# FFI Needs Analysis: What Requires New C Runtime vs. SFFI

## Analysis Date
2026-02-12

## Summary

**Total Skipped Tests**: 606
**Pending Features**: 3

This document categorizes all pending features and skipped tests into:
1. **Requires New C Runtime FFI** - Cannot be done with existing SFFI
2. **Can Use Existing SFFI** - Implement in Pure Simple
3. **Already Has SFFI** - Just needs Simple implementation

---

## Category 1: REQUIRES New C Runtime FFI

### 1.1 Async/Await System (150+ tests) - COMPLEX RUNTIME
**Why Needs C Runtime:**
- Requires OS-level async I/O primitives (epoll, kqueue, IOCP)
- Non-blocking sockets
- Event loop management
- Timer wheel implementation
- Context switching for coroutines

**Cannot use SFFI because:**
- Performance-critical (can't use shell commands)
- Requires kernel integration
- Needs low-latency event notification

**Estimated C LOC**: 2000-3000 (full async runtime)

---

### 1.2 GPU/CUDA Runtime (80+ tests) - EXTERNAL LIBRARY FFI
**Why Needs C Runtime:**
- CUDA C API bindings (`cudaMalloc`, `cudaMemcpy`, `cudaLaunchKernel`)
- cuBLAS, cuDNN library bindings
- Device memory management
- Stream/event synchronization

**Cannot use SFFI because:**
- External library (libcuda.so, libcudart.so)
- Complex data structures
- GPU-specific operations

**Estimated C LOC**: 500-1000 (CUDA bindings)

---

### 1.3 Memory-Mapped File I/O (10+ tests) - OS-SPECIFIC
**Why Needs C Runtime:**
- `mmap()` / `CreateFileMapping()` - OS primitives
- Memory protection flags
- `madvise()` / `VirtualAlloc()` - OS hints
- `msync()` / `FlushViewOfFile()` - synchronization

**Cannot use SFFI because:**
- Performance-critical (direct memory access)
- No shell command equivalent
- OS-specific APIs

**Estimated C LOC**: 100-200

**Status**: ⚠️ Partially exists - mmap functions declared but incomplete

---

### 1.4 Process Async Spawn (25+ tests) - OS-SPECIFIC
**Why Needs C Runtime:**
- `fork()` + `execvp()` (Unix) / `CreateProcess()` (Windows)
- Non-blocking `waitpid(WNOHANG)`
- Process kill with timeout
- Signal handling

**Cannot use SFFI because:**
- Shell commands are synchronous/blocking
- Need precise process control
- Timeout management requires polling

**Estimated C LOC**: 150-200

**Status**: ✅ ALREADY IMPLEMENTED (Track D1.1 complete)

---

### 1.5 High-Resolution Time (15+ tests) - OS-SPECIFIC
**Why Needs C Runtime:**
- `clock_gettime(CLOCK_MONOTONIC_RAW)` (Unix)
- `QueryPerformanceCounter()` (Windows)
- Nanosecond precision

**Cannot use SFFI because:**
- Shell `date` command has only second precision
- Benchmarking requires sub-millisecond accuracy

**Estimated C LOC**: 50-100

**Status**: ✅ ALREADY IMPLEMENTED (Track D0.2 complete)

---

### 1.6 Network Sockets (potential future)
**Why Needs C Runtime:**
- `socket()`, `bind()`, `listen()`, `accept()`, `connect()`
- Non-blocking I/O (`fcntl(O_NONBLOCK)`)
- `select()` / `poll()` / `epoll()`

**Cannot use SFFI because:**
- No shell command for socket programming
- Need low-level network control

**Estimated C LOC**: 300-500

**Status**: ❌ NOT IMPLEMENTED, not in pending features

---

## Category 2: CAN Use Existing SFFI (Pure Simple Implementation)

### 2.1 Offset-Based File I/O - CAN USE SHELL COMMANDS
**Current Approach**: New C runtime functions
**SFFI Alternative**: Use `dd` command via existing `shell_output()`

```simple
fn file_read_text_at(path: text, offset: i64, size: i64) -> text:
    # Use dd: bs=1 (byte size), skip=offset, count=size
    val cmd = "dd if='{path}' bs=1 skip={offset} count={size} 2>/dev/null"
    shell_output(cmd)

fn file_write_text_at(path: text, offset: i64, data: text) -> i64:
    # Use dd: seek=offset, conv=notrunc (don't truncate)
    val temp = "/tmp/spl_{_getpid()}"
    file_write(temp, data)
    val cmd = "dd if='{temp}' of='{path}' bs=1 seek={offset} conv=notrunc 2>/dev/null && rm '{temp}'"
    if shell_bool(cmd):
        data.len()
    else:
        -1
```

**Pros**: Uses existing SFFI, no C code needed
**Cons**: Slower than pread/pwrite, shell dependency
**Recommendation**: Use SFFI for now, add C if performance critical

---

### 2.2 File Locking - ALREADY EXISTS
**Status**: ✅ Already has C runtime + SFFI wrappers
- `rt_file_lock()` - C function exists
- `file_lock()` - SFFI wrapper exists in `file_ops.spl`

**Action**: None needed

---

### 2.3 Debugger Infrastructure (100+ tests) - PURE SIMPLE
**Can implement in Simple:**
- Breakpoint management: Dict<text, [i64]> (file → line numbers)
- Watch expressions: Array of expressions to evaluate
- Call stack: Built from interpreter state
- Step commands: Control interpreter loop

**Uses existing:**
- Interpreter runtime
- Expression evaluation
- No new C runtime needed

**Recommendation**: Implement in Pure Simple

---

### 2.4 Windows Platform Support (50+ tests) - SFFI
**Can use SFFI:**
- Path handling: Pure Simple string manipulation
- Command resolution: `where` command via `shell()`
- Environment variables: Existing `rt_env_get()`

**Recommendation**: Pure Simple implementation

---

### 2.5 Generic Type System (30+ tests) - COMPILER
**Pure compiler work:**
- Template tracking: Compiler data structures
- Monomorphization: Compiler pass
- Type validation: Type checker

**No runtime FFI needed**

---

## Category 3: VERY HIGH COMPLEXITY (Defer or Architectural)

### 3.1 Async/Await System
**Complexity**: VERY HIGH
**Effort**: 4-6 weeks
**Dependencies**: Full async runtime
**Recommendation**: **DEFER** - Major architectural change

---

### 3.2 GPU/CUDA Runtime
**Complexity**: VERY HIGH
**Effort**: 3-4 weeks
**Dependencies**: CUDA toolkit, hardware
**Recommendation**: **DEFER** - Niche use case, hardware-dependent

---

### 3.3 Baremetal/Embedded (50+ tests)
**Complexity**: VERY HIGH
**Effort**: 6-8 weeks
**Dependencies**: Architecture-specific assembly, QEMU testing
**Recommendation**: **DEFER** - Specialized domain

---

### 3.4 Compiler Bootstrapping
**Complexity**: VERY HIGH
**Effort**: 8-12 weeks
**Dependencies**: Feature-complete compiler pipeline
**Recommendation**: **DEFER** - Long-term goal

---

## Category 4: Runtime Interpreter Limitations (NOT FFI)

These are interpreter bugs, NOT FFI needs:

1. **Closure capture modification** - Interpreter bug
2. **Module closures** - Interpreter bug
3. **Chained method calls** - Interpreter bug
4. **Multi-line booleans** - Parser/interpreter bug
5. **Generics at runtime** - Interpreter limitation

**Recommendation**: Fix interpreter, no FFI needed

---

## Immediate Action Items

### HIGH PRIORITY: Remove Unnecessary C Runtime

**File**: `seed/runtime.h`, `seed/platform/unix_common.h`, `seed/platform/platform_win.h`

**Remove (use SFFI instead)**:
```c
// Remove these - can use dd command
const char* rt_file_read_text_at(...)
int64_t rt_file_write_text_at(...)
```

**Implement in Pure Simple**:
```simple
// src/app/io/file_ops.spl
fn file_read_text_at(path: text, offset: i64, size: i64) -> text:
    shell_output("dd if='{path}' bs=1 skip={offset} count={size} 2>/dev/null")
```

### KEEP: Essential C Runtime

**Keep these** (no SFFI alternative):
```c
// High-resolution time - no shell equivalent
int64_t rt_time_now_nanos(void);
int64_t rt_time_now_micros(void);

// Async process - shell is blocking
int64_t rt_process_spawn_async(...);
int64_t rt_process_wait(...);
bool rt_process_is_running(...);
bool rt_process_kill(...);

// File locking - exists, already works
int64_t rt_file_lock(...);
bool rt_file_unlock(...);
```

---

## Summary Table

| Feature | Tests | Needs C FFI? | Can Use SFFI? | Priority | Status |
|---------|-------|--------------|---------------|----------|--------|
| **Async/Await** | 150+ | ✅ Yes | ❌ No | P3 Defer | Not started |
| **GPU/CUDA** | 80+ | ✅ Yes | ❌ No | P3 Defer | Not started |
| **Debugger** | 100+ | ❌ No | ✅ Yes (Pure Simple) | P2 Medium | Not started |
| **Baremetal** | 50+ | ✅ Yes | ❌ No | P3 Defer | Not started |
| **Generics** | 30+ | ❌ No | N/A (Compiler) | P2 High | Not started |
| **Windows** | 50+ | ❌ No | ✅ Yes (SFFI) | P2 Medium | Partial |
| **High-res Time** | 15+ | ✅ Yes | ❌ No | P1 High | ✅ **DONE** |
| **Async Process** | 25+ | ✅ Yes | ❌ No | P1 High | ✅ **DONE** |
| **Offset File I/O** | 50+ | ❌ **NO** | ✅ **YES** (dd) | P2 Medium | ⚠️ **REVERT** |
| **File Locking** | 20+ | ✅ Yes | ❌ No | P1 High | ✅ Exists |
| **Mmap** | 10+ | ✅ Yes | ❌ No | P2 Medium | Incomplete |

---

## Recommendations

### Immediate (This Session)
1. **REVERT** offset-based file I/O C runtime functions
2. **IMPLEMENT** offset file I/O using `dd` command via SFFI
3. **TEST** that it works with existing `shell_output()` wrapper

### Short Term (1-2 weeks)
4. **FIX** interpreter bugs (closures, method chaining) - no FFI needed
5. **IMPLEMENT** debugger in Pure Simple
6. **COMPLETE** Windows support using SFFI

### Medium Term (1-2 months)
7. **IMPLEMENT** mmap FFI if profiling shows need
8. **CONSIDER** network sockets if web server needed
9. **DEFER** async/await until clear use case

### Long Term (3+ months)
10. **DEFER** GPU/CUDA until ML features needed
11. **DEFER** baremetal until embedded use case
12. **DEFER** full bootstrapping until compiler mature

---

## Conclusion

**Key Finding**: Many "FFI needs" can actually use existing SFFI wrappers!

**Immediate Action**:
- ✅ Keep: High-res time, async process, file locking (true FFI needs)
- ❌ Remove: Offset file I/O C functions (can use dd command)
- 📝 Document: When to use FFI vs. SFFI

**Test Impact**:
- With existing FFI: ~60 tests (+40 from time/process)
- With SFFI implementations: ~150 tests (+90 from debugger/windows)
- Total potential: ~210 tests without new C runtime

**Philosophy**: Add C runtime FFI only when:
1. No shell command equivalent exists
2. Performance is critical (profiled bottleneck)
3. OS-specific API required
4. External library binding needed
