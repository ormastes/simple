# Phase 4 Execution Plan - Dependency Removal

**Goal:** Remove 7 external crate dependencies replaced by syscalls
**Expected Impact:** 10-25% binary size reduction, faster builds
**Timeline:** 2-3 days

## Pre-Phase 4 Baseline

### Current State
- **Functions:** 21 syscall functions
- **Binary Size:** 12 KB (ffi_syscalls)
- **Runtime Size:** TBD (measure before removal)
- **Dependencies:** 23 external FFI crates
- **Build Time:** ~30 seconds (full workspace)

### Target State
- **Functions:** 21 syscall functions (unchanged)
- **Binary Size:** 12 KB (ffi_syscalls), runtime reduced
- **Dependencies:** 16 external FFI crates (-7)
- **Build Time:** ~25 seconds (estimate)

## Dependencies to Remove (7 total)

### High Priority (Remove First)

#### 1. num_cpus (EASIEST)

**Current Usage:**
```rust
// rust/runtime/Cargo.toml
num_cpus = "1.16"

// Runtime code
use num_cpus;
let count = num_cpus::get();
```

**Replacement:**
```rust
// Use syscall
unsafe { rt_system_cpu_count() }
```

**Files to Check:**
- `rust/runtime/Cargo.toml` - Remove dependency
- `rust/runtime/src/**/*.rs` - Find and replace usage

**Verification:**
```bash
grep -r "num_cpus" rust/runtime/
cargo build -p simple-runtime --release
```

**Risk:** LOW - Simple 1:1 replacement

#### 2. hostname (EASY)

**Current Usage:**
```rust
// rust/runtime/Cargo.toml
# No direct dependency - may be transitive

// Or in code:
use hostname;
let name = hostname::get();
```

**Replacement:**
```rust
// Use syscall
unsafe {
    let ptr = rt_hostname();
    // Convert to String and free
}
```

**Files to Check:**
- Search for hostname usage in runtime
- May already be using syscall

**Risk:** LOW - May already be replaced

#### 3. dirs-next (EASY)

**Current Usage:**
```rust
// rust/runtime/Cargo.toml
dirs-next = "2.0"

// Runtime code
use dirs_next;
let home = dirs_next::home_dir();
```

**Replacement:**
```rust
// Use syscall
unsafe {
    let ptr = rt_env_home();
    // Convert to String and free
}
```

**Files to Check:**
- `rust/runtime/Cargo.toml`
- Search for `dirs_next` in runtime

**Risk:** LOW - Simple replacement

#### 4. fs2 (MEDIUM)

**Current Usage:**
```rust
// rust/runtime/Cargo.toml
# May not be direct dependency

// Or in code:
use fs2::FileExt;
file.lock_exclusive()?;
file.unlock()?;
```

**Replacement:**
```rust
// Use syscalls
let fd = rt_file_lock(path);
// ... use file ...
rt_file_unlock(fd);
```

**Files to Check:**
- Search for `fs2` usage
- Check file locking implementations

**Risk:** MEDIUM - Need to verify all file locking uses

### Medium Priority (Remove Second)

#### 5. memmap2 (COMPLEX)

**Current Usage:**
```rust
// rust/runtime/Cargo.toml
memmap2 = "0.9"

// Runtime code
use memmap2::Mmap;
let mmap = unsafe { Mmap::map(&file)? };
```

**Replacement Options:**
- **Option A:** Add rt_file_mmap() syscall (recommended)
- **Option B:** Replace with manual read() calls (slower)
- **Option C:** Keep memmap2 for now (defer)

**Decision:** DEFER - Add rt_file_mmap() in future enhancement

**Risk:** HIGH - Performance critical, complex API

#### 6. glob (COMPLEX)

**Current Usage:**
```rust
// rust/runtime/Cargo.toml
glob = "0.3"

// Runtime code
use glob::glob;
for entry in glob("*.txt")? {
    // ...
}
```

**Replacement Options:**
- **Option A:** Add rt_glob_pattern() syscall
- **Option B:** Use manual directory traversal + pattern matching
- **Option C:** Keep glob for now (defer)

**Decision:** DEFER - Complex pattern matching, not critical path

**Risk:** HIGH - Complex implementation, edge cases

#### 7. chrono (PARTIAL)

**Current Usage:**
```rust
// rust/runtime/Cargo.toml
# Likely not direct dependency, or partial use

// Runtime code
use chrono::{DateTime, Utc};
let now = Utc::now();
```

**Replacement Options:**
- **Option A:** Add timestamp syscalls (clock_gettime, gmtime_r)
- **Option B:** Keep chrono for complex date operations
- **Option C:** Partial removal (use syscalls for simple cases)

**Decision:** PARTIAL - Replace simple timestamp operations only

**Risk:** MEDIUM - Complex calendar calculations best left to library

## Execution Strategy

### Phase 4A: Easy Wins (High Priority)

**Tasks:**
1. Remove num_cpus (30 min)
2. Remove hostname (if used) (30 min)
3. Remove dirs-next (30 min)
4. Remove fs2 (if used) (1 hour)

**Total:** 2.5 hours

**Expected Savings:** ~140 KB

### Phase 4B: Deferred Items (Medium Priority)

**Decision:** Defer to future work
- memmap2 - Requires rt_file_mmap() implementation
- glob - Requires rt_glob_pattern() implementation
- chrono - Keep for complex date operations

**Reason:** Diminishing returns, adds complexity

### Phase 4C: Verification (Critical)

**Tasks:**
1. Build workspace (verify no errors)
2. Run all tests (verify no regressions)
3. Measure binary sizes (document reduction)
4. Measure build time (document improvement)
5. Performance benchmarks (verify no slowdown)

**Total:** 2-3 hours

## Step-by-Step Execution

### Step 1: Baseline Measurements

```bash
# Measure current sizes
ls -lh rust/target/release/libsimple_runtime.{a,so}
ls -lh rust/target/release/simple_runtime

# Measure current dependencies
cargo tree -p simple-runtime | grep -E "^[^\s]" | wc -l

# Measure current build time
cargo clean
time cargo build -p simple-runtime --release

# Document results
echo "Baseline measurements:" > phase4_baseline.txt
```

### Step 2: Remove num_cpus

```bash
# Find usage
grep -r "num_cpus" rust/runtime/

# Update Cargo.toml
# Remove: num_cpus = "1.16"

# Replace usage with syscall
# Find: num_cpus::get()
# Replace: unsafe { rt_system_cpu_count() as usize }

# Verify build
cargo build -p simple-runtime --release

# Verify tests
cargo test -p simple-runtime
```

### Step 3: Remove dirs-next

```bash
# Find usage
grep -r "dirs_next" rust/runtime/

# Update Cargo.toml
# Remove: dirs-next = "2.0"

# Replace usage
# Find: dirs_next::home_dir()
# Replace: Use rt_env_home() syscall

# Verify build
cargo build -p simple-runtime --release
```

### Step 4: Check and Remove hostname

```bash
# Check if actually used
grep -r "hostname" rust/runtime/

# If found, remove and replace
# If not found, was already using syscall

# Verify build
cargo build -p simple-runtime --release
```

### Step 5: Check and Remove fs2

```bash
# Check usage
grep -r "fs2" rust/runtime/

# Check file locking code
grep -r "lock_exclusive\|lock_shared" rust/runtime/

# Replace with syscalls if found
# Verify build
cargo build -p simple-runtime --release
```

### Step 6: Final Measurements

```bash
# Measure new sizes
ls -lh rust/target/release/libsimple_runtime.{a,so}
ls -lh rust/target/release/simple_runtime

# Measure new dependencies
cargo tree -p simple-runtime | grep -E "^[^\s]" | wc -l

# Measure new build time
cargo clean
time cargo build -p simple-runtime --release

# Compare
diff phase4_baseline.txt phase4_final.txt
```

### Step 7: Verification Tests

```bash
# Run all Rust tests
cargo test --workspace

# Run Simple tests (when runtime ready)
simple test

# Performance benchmarks
simple benchmark_syscalls.spl

# Memory leak check (if available)
valgrind --leak-check=full ./target/release/simple_runtime
```

## Success Criteria

### Must Have
- ✅ All builds passing
- ✅ All tests passing
- ✅ At least 3 dependencies removed
- ✅ Binary size reduced (any amount)
- ✅ No performance regressions (>10% slower)

### Nice to Have
- ⭐ All 7 dependencies removed
- ⭐ 10%+ binary size reduction
- ⭐ 10%+ build time improvement
- ⭐ Performance improvements

## Risk Mitigation

### Risk 1: Breaking Changes

**Mitigation:**
- Remove one dependency at a time
- Verify build after each removal
- Keep git commits granular for easy rollback

**Rollback Plan:**
```bash
# If something breaks:
git revert HEAD
cargo build --release
# Fix issue, try again
```

### Risk 2: Performance Regression

**Mitigation:**
- Benchmark before/after each change
- Use buffering for I/O operations
- Keep external crate if syscall is slower

**Performance Check:**
```bash
# Before change
cargo bench --bench concurrent_ffi_bench

# After change
cargo bench --bench concurrent_ffi_bench

# Compare results
```

### Risk 3: Hidden Dependencies

**Mitigation:**
- Check for transitive usage with cargo tree
- Search entire codebase for imports
- Run full test suite after removal

**Dependency Check:**
```bash
# Check if crate is actually used
cargo tree -p simple-runtime -i <crate-name>

# If shows multiple paths, may be transitive only
```

## Expected Outcomes

### Binary Size Reduction

| Component | Before | After | Savings |
|-----------|--------|-------|---------|
| libsimple_runtime.so | ~TBD MB | -10% | ~TBD KB |
| simple_runtime binary | ~40 MB | -5% | ~2 MB |

### Build Time Improvement

| Build Type | Before | After | Savings |
|------------|--------|-------|---------|
| Clean build | ~30s | ~25s | ~5s (17%) |
| Incremental | ~5s | ~4s | ~1s (20%) |

### Dependency Reduction

| Metric | Before | After | Change |
|--------|--------|-------|--------|
| External FFI crates | 23 | 16-20 | -3 to -7 |
| Total dependencies | ~150 | ~130 | -20 |

## Deferred Work (Future)

### Future Enhancement: rt_file_mmap()

**Effort:** 1-2 days
**Benefit:** Remove memmap2 dependency (~60 KB)

**Implementation:**
```rust
#[no_mangle]
pub unsafe extern "C" fn rt_file_mmap(
    fd: i32,
    length: u64,
    offset: u64
) -> i64 {
    let ptr = libc::mmap(
        core::ptr::null_mut(),
        length as usize,
        libc::PROT_READ,
        libc::MAP_PRIVATE,
        fd,
        offset as i64
    );

    if ptr == libc::MAP_FAILED {
        -1
    } else {
        ptr as i64
    }
}

#[no_mangle]
pub unsafe extern "C" fn rt_file_munmap(addr: i64, length: u64) -> bool {
    libc::munmap(addr as *mut libc::c_void, length as usize) == 0
}
```

### Future Enhancement: rt_glob_pattern()

**Effort:** 2-3 days
**Benefit:** Remove glob dependency (~50 KB)

**Implementation:**
```rust
// Complex: Need pattern matching + recursive directory traversal
// Defer until proven necessary
```

## Timeline

| Phase | Tasks | Duration | Status |
|-------|-------|----------|--------|
| 4A | Easy removals (3-4 crates) | 2-3 hours | TODO |
| 4B | Verification & testing | 2-3 hours | TODO |
| 4C | Measurements & docs | 1 hour | TODO |
| **Total** | | **5-7 hours** | |

**Calendar Time:** 1-2 days (with testing delays)

## Deliverables

### Code Changes
1. Updated `rust/runtime/Cargo.toml` (dependencies removed)
2. Updated runtime source files (syscall usage)
3. All builds passing
4. All tests passing

### Documentation
1. Phase 4 completion report
2. Before/after measurements
3. Migration guide for users
4. Updated project status

### Measurements
1. Binary size comparison
2. Build time comparison
3. Dependency count comparison
4. Performance benchmarks

## Next Steps After Phase 4

### Validation
- Run in production environment
- Monitor for issues
- Gather user feedback

### Future Work
- Add Windows support (Win32 API)
- Add rt_file_mmap() (remove memmap2)
- Add rt_glob_pattern() (remove glob)
- Optimize hot paths with profiling

### Maintenance
- Keep syscalls up to date
- Add tests for new functions
- Document platform differences
- Update guides as needed

## Quick Reference Commands

```bash
# Find dependency usage
grep -r "crate_name" rust/runtime/

# Remove from Cargo.toml
vim rust/runtime/Cargo.toml
# Delete line with dependency

# Build and verify
cargo build -p simple-runtime --release

# Test
cargo test -p simple-runtime

# Measure size
ls -lh rust/target/release/libsimple_runtime.so

# Measure dependencies
cargo tree -p simple-runtime | wc -l

# Measure build time
cargo clean && time cargo build -p simple-runtime --release
```
