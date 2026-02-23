# Phase 3: Simple Wrapper Migration Guide

**Prerequisites:** Phases 1-2 complete ✅
**Duration:** 1 week estimated
**Goal:** Update Simple wrappers to use syscall implementations

## Quick Start

```bash
# 1. Verify Phase 2 is working
cargo build -p simple-runtime --release

# 2. Run existing tests
simple test test/system/ffi/syscalls_test.spl

# 3. Check current wrapper status
cat src/app/io/mod.spl | grep "extern fn rt_" | wc -l
# Should show: 107 total FFI wrappers
```

## Phase 3 Overview

### Goals

1. ✅ Audit all FFI wrappers in `src/app/io/mod.spl` (107 total)
2. ✅ Identify which can use syscalls vs need external libs
3. ✅ Update wrappers to use syscall implementations
4. ✅ Test thoroughly to ensure no regressions
5. ✅ Document migration decisions

### Non-Goals

- **Don't** remove external crates yet (that's Phase 4)
- **Don't** change FFI signatures (breaking changes)
- **Don't** add new functionality (focus on migration)

## Step 1: Audit FFI Wrappers

### Current Status

**File:** `src/app/io/mod.spl`
- 107 total FFI wrappers
- 16 have syscall implementations (Phase 1) ✅
- 91 need evaluation

### Categorization

Run this audit script:

```bash
# Create audit script
cat > scripts/audit_ffi_wrappers.sh << 'EOF'
#!/bin/bash
cd "$(dirname "$0")/.."

echo "=== FFI Wrapper Audit ==="
echo ""

echo "1. File I/O functions:"
grep -E "rt_file|rt_dir" src/app/io/mod.spl | grep "extern fn" | wc -l

echo "2. Environment functions:"
grep -E "rt_env" src/app/io/mod.spl | grep "extern fn" | wc -l

echo "3. Process functions:"
grep -E "rt_process|rt_getpid" src/app/io/mod.spl | grep "extern fn" | wc -l

echo "4. System functions:"
grep -E "rt_system|rt_hostname" src/app/io/mod.spl | grep "extern fn" | wc -l

echo "5. Network functions:"
grep -E "rt_net|rt_http" src/app/io/mod.spl | grep "extern fn" | wc -l

echo "6. Crypto functions:"
grep -E "rt_sha|rt_hash" src/app/io/mod.spl | grep "extern fn" | wc -l

echo ""
echo "Total:"
grep "extern fn rt_" src/app/io/mod.spl | wc -l
EOF

chmod +x scripts/audit_ffi_wrappers.sh
./scripts/audit_ffi_wrappers.sh
```

### Decision Matrix

| Category | Syscalls | External Libs | Reason |
|----------|----------|---------------|--------|
| **File I/O** | ✅ Use syscalls | | Direct kernel operations |
| **Directory** | ✅ Use syscalls | | Direct kernel operations |
| **Environment** | ✅ Use syscalls | | Simple getenv/getcwd |
| **Process** | ✅ Use syscalls | | fork/exec manageable |
| **System Info** | ✅ Use syscalls | | sysconf/gethostname |
| **Network** | | ❌ Keep ureq | Complex HTTP protocol |
| **Crypto** | | ❌ Keep sha1/sha2 | Complex algorithms |
| **Archive** | | ❌ Keep tar/flate2 | Complex formats |
| **Serialization** | | ❌ Keep serde_json/toml | Complex parsers |
| **Regex** | | ❌ Keep regex | Complex engine |
| **Concurrency** | | ❌ Keep rayon | Complex scheduler |
| **JIT** | | ❌ Keep cranelift | Complex codegen |

## Step 2: Verify Syscall Wrappers

### Check Current Wrappers

**File:** `src/app/io/mod.spl`

Look for these patterns:

```simple
# Pattern 1: Direct extern (already uses syscall)
extern fn rt_file_exists(path: text) -> bool
fn file_exists(path: text) -> bool:
    rt_file_exists(path)

# Pattern 2: Wrapper with conversion (may need update)
extern fn rt_file_read_text(path: text) -> text
fn file_read(path: text) -> text:
    val content = rt_file_read_text(path)
    if content.is_empty():
        return ""
    content

# Pattern 3: Complex wrapper (may use different FFI)
fn file_copy(src: text, dst: text) -> bool:
    # May call different FFI function, not syscall
```

### Syscall Functions Ready (16 total)

These should already work with syscalls:

**File I/O (9):**
- `rt_file_exists()`
- `rt_file_read_text()`
- `rt_file_write_text()`
- `rt_file_delete()`
- `rt_file_size()`
- `rt_dir_create()`
- `rt_dir_list()`
- `rt_file_lock()`
- `rt_file_unlock()`

**Environment (3):**
- `rt_env_cwd()`
- `rt_env_get()`
- `rt_env_home()`

**Process (2):**
- `rt_getpid()`
- `rt_process_run()`

**System (2):**
- `rt_system_cpu_count()`
- `rt_hostname()`

## Step 3: Run Integration Tests

### Test Syscall Functions

```bash
# Run syscall integration tests
simple test test/system/ffi/syscalls_test.spl

# Expected output:
# ✓ File operations test passed
# ✓ Directory operations test passed
# ✓ File locking test passed
# ✓ Environment test passed
# ✓ Process info test passed
# ✓ Process run test passed
# All syscall tests passed! ✓
```

### Test All FFI Functions

```bash
# Run all system tests
simple test test/system/

# Check for regressions
simple test test/unit/

# Full test suite
simple test
```

### Manual Verification

Create a test script:

```simple
# test_syscalls_manual.spl

extern fn rt_file_exists(path: text) -> bool
extern fn rt_file_write_text(path: text, content: text) -> bool
extern fn rt_file_read_text(path: text) -> text
extern fn rt_file_delete(path: text) -> bool
extern fn rt_getpid() -> i64
extern fn rt_system_cpu_count() -> i64
extern fn rt_hostname() -> text

fn main():
    print "Testing syscall functions..."

    # Test file operations
    val test_file = "/tmp/simple_test.txt"
    val content = "Hello from syscalls!"

    assert rt_file_write_text(test_file, content)
    assert rt_file_exists(test_file)

    val read_content = rt_file_read_text(test_file)
    assert read_content == content

    assert rt_file_delete(test_file)
    assert not rt_file_exists(test_file)

    # Test system info
    val pid = rt_getpid()
    assert pid > 0
    print "Process ID: {pid}"

    val cpus = rt_system_cpu_count()
    assert cpus > 0
    print "CPU count: {cpus}"

    val hostname = rt_hostname()
    assert hostname != ""
    print "Hostname: {hostname}"

    print "All syscall functions working! ✓"
```

Run it:

```bash
simple test_syscalls_manual.spl
```

## Step 4: Identify Issues

### Common Issues

#### Issue 1: Missing Function

**Symptom:**
```
Error: undefined reference to `rt_some_function`
```

**Diagnosis:**
- Function not implemented in ffi_syscalls
- Function uses different FFI (external lib)

**Solution:**
- Check if function should use syscalls
- If yes: Implement in ffi_syscalls (extend Phase 1)
- If no: Keep using external lib

#### Issue 2: Different Signature

**Symptom:**
```
Error: type mismatch in function call
```

**Diagnosis:**
- Wrapper expects different signature than syscall provides

**Solution:**
- Update wrapper to match syscall signature
- OR add conversion layer in wrapper

#### Issue 3: Platform-Specific

**Symptom:**
```
Warning: syscall not available on Windows
```

**Diagnosis:**
- Syscall is POSIX-only

**Solution:**
- Add conditional compilation: `#[cfg(unix)]`
- Document Windows limitations
- Plan Win32 API implementation (future)

## Step 5: Update Wrappers

### For Most Functions (No Changes Needed)

If the wrapper already uses the correct extern fn, no changes needed:

```simple
# src/app/io/mod.spl - No changes required

extern fn rt_file_exists(path: text) -> bool

fn file_exists(path: text) -> bool:
    rt_file_exists(path)  # Now automatically uses syscall version!
```

### For Functions Needing Updates

If the wrapper needs to change:

```simple
# Before: Using old FFI
extern fn old_rt_file_check(path_ptr: i64) -> i32
fn file_exists(path: text) -> bool:
    val ptr = string_to_ptr(path)
    val result = old_rt_file_check(ptr)
    result != 0

# After: Using syscall FFI
extern fn rt_file_exists(path: text) -> bool
fn file_exists(path: text) -> bool:
    rt_file_exists(path)  # Simpler!
```

### Adding New Wrappers

If a syscall function has no Simple wrapper:

```simple
# Add to src/app/io/mod.spl

# --- File Locking ---
extern fn rt_file_lock(path: text) -> i64
extern fn rt_file_unlock(fd: i64) -> bool

fn file_lock(path: text) -> i64:
    """Acquire exclusive file lock.
    Returns file descriptor or -1 on error."""
    rt_file_lock(path)

fn file_unlock(fd: i64) -> bool:
    """Release file lock and close file descriptor."""
    rt_file_unlock(fd)
```

## Step 6: Document Changes

### Create Migration Log

**File:** `doc/report/ffi_wrapper_migration_2026-02-04.md`

Template:

```markdown
# FFI Wrapper Migration Log

## Date: 2026-02-04

### Functions Migrated to Syscalls

1. `rt_file_exists()` - ✅ Already using syscall
2. `rt_file_read_text()` - ✅ Already using syscall
3. `rt_file_write_text()` - ✅ Already using syscall
... (list all 16)

### Functions Keeping External Libs

1. `rt_http_get()` - Uses ureq (complex HTTP protocol)
2. `rt_sha256()` - Uses sha2 (complex algorithm)
... (list all kept)

### Functions Added

1. `file_lock()` - New wrapper for rt_file_lock()
2. `file_unlock()` - New wrapper for rt_file_unlock()
... (list all added)

### Issues Encountered

1. Issue: ...
   Solution: ...

2. Issue: ...
   Solution: ...
```

### Update Main Documentation

**File:** `doc/guide/ffi_syscalls_quick_reference.md`

Add "Usage in Simple" section showing wrapper functions.

## Step 7: Performance Testing

### Benchmark Syscall Functions

Create benchmark:

```simple
# benchmark_syscalls.spl

import std.time

extern fn rt_file_exists(path: text) -> bool
extern fn rt_getpid() -> i64

fn benchmark_file_exists():
    val iterations = 10000
    val start = time.now()

    for i in 0..iterations:
        rt_file_exists("/tmp")

    val end = time.now()
    val elapsed = end - start
    val per_call = elapsed / iterations

    print "file_exists: {per_call} ns/call"

fn benchmark_getpid():
    val iterations = 1000000
    val start = time.now()

    for i in 0..iterations:
        rt_getpid()

    val end = time.now()
    val elapsed = end - start
    val per_call = elapsed / iterations

    print "getpid: {per_call} ns/call"

fn main():
    print "Benchmarking syscall functions..."
    benchmark_file_exists()
    benchmark_getpid()
```

### Expected Results

- `rt_file_exists()`: ~1-5 μs/call (depends on filesystem)
- `rt_getpid()`: ~20-50 ns/call (very fast syscall)
- `rt_file_read_text()`: ~10-100 μs/call (depends on file size)

## Step 8: Regression Testing

### Test Matrix

| Test Suite | Command | Expected |
|------------|---------|----------|
| Syscall integration | `simple test test/system/ffi/syscalls_test.spl` | All pass |
| File I/O tests | `simple test test/system/file/` | All pass |
| System tests | `simple test test/system/` | All pass |
| Unit tests | `simple test test/unit/` | All pass |
| Full suite | `simple test` | All pass |
| Rust tests | `cargo test --workspace` | All pass |

### Continuous Testing

Run tests after each change:

```bash
# Quick iteration loop
while true; do
    clear
    echo "Testing..."
    simple test test/system/ffi/syscalls_test.spl
    if [ $? -eq 0 ]; then
        echo "✓ Tests passed"
    else
        echo "✗ Tests failed - fix before continuing"
    fi
    sleep 2
done
```

## Success Criteria

Phase 3 is complete when:

- ✅ All 16 syscall functions have Simple wrappers
- ✅ All wrappers tested and working
- ✅ No regressions in existing tests
- ✅ Performance benchmarks acceptable
- ✅ Migration documented
- ✅ Ready for Phase 4 (cleanup)

## Timeline

| Task | Duration | Status |
|------|----------|--------|
| Audit FFI wrappers | 1 day | ⏳ TODO |
| Verify syscall wrappers | 1 day | ⏳ TODO |
| Run integration tests | 0.5 days | ⏳ TODO |
| Identify issues | 1 day | ⏳ TODO |
| Update wrappers | 2 days | ⏳ TODO |
| Document changes | 0.5 days | ⏳ TODO |
| Performance testing | 0.5 days | ⏳ TODO |
| Regression testing | 0.5 days | ⏳ TODO |
| **Total** | **7 days** | |

## Next: Phase 4

Once Phase 3 is complete, proceed to Phase 4:

**File:** `doc/guide/ffi_syscalls_phase4_guide.md`

**Goal:** Remove redundant external crates

**Tasks:**
1. Remove 7 external crate dependencies
2. Delete redundant code
3. Measure binary size reduction
4. Update documentation
5. Final verification

**Duration:** 1-2 days

## Quick Command Reference

```bash
# Audit wrappers
grep "extern fn rt_" src/app/io/mod.spl | wc -l

# Test syscalls
simple test test/system/ffi/syscalls_test.spl

# Full test suite
simple test

# Build runtime
cargo build -p simple-runtime --release

# Check symbols
nm rust/target/release/libsimple_runtime.so | grep "rt_"

# Benchmark (when implemented)
simple benchmark_syscalls.spl
```

## Getting Help

If stuck:
1. Check documentation: `doc/guide/ffi_syscalls_quick_reference.md`
2. Review Phase 1-2 reports: `doc/report/ffi_syscalls_*.md`
3. Examine implementation: `rust/ffi_syscalls/src/lib.rs`
4. Test in isolation: Create minimal Simple script to test function
