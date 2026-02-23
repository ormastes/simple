# Test Redundancy Analysis - Rust vs Simple
## Date: February 3, 2026

## Executive Summary

Analysis of test coverage across Rust and Simple codebases reveals significant overlap in certain areas. With 692 Simple/SSpec test files now in place, some Rust tests may be redundant or could be migrated to Simple for better maintainability.

**Key Findings:**
- **692 Simple test files** exist (primarily SSpec tests)
- **~50+ Rust test files** identified
- Potential redundancy in: collections, file I/O, async features
- Recommendation: Keep Rust tests for runtime/compiler core, migrate application tests to Simple

## Test Distribution

### Simple/SSpec Tests (692 files)
**Location:** `test/` directory

**Categories:**
- System tests: `test/system/` (~400 files)
- Feature tests: `test/system/features/` (~200 files)
- Unit tests: `test/unit/` (~50 files)
- Integration tests: `test/integration/` (~20 files)
- Compiler tests: `test/compiler/` (~15 files)

**Format:** SSpec BDD-style tests
```simple
describe "Feature":
    it "does something":
        expect result == expected
```

### Rust Tests (~50+ files)
**Location:** `rust/` directory (various subdirectories)

**Categories:**
- Runtime tests: `rust/runtime/tests/` and `rust/runtime/src/*/tests.rs`
- Loader tests: `rust/loader/tests/`
- SDK tests: `rust/sdn/tests/`
- Utility tests: `rust/common/tests/`

**Format:** Standard Rust tests
```rust
#[test]
fn test_feature() {
    assert_eq!(result, expected);
}
```

## Potential Redundancy Areas

### 1. Collection Tests

**Rust:**
- `rust/runtime/src/value/collection_tests.rs`
- Tests: List, Dict, Set implementations in Rust runtime

**Simple:**
- `test/std/collections_spec.spl` (created this session, 32 tests)
- `test/system/features/collections/collections_spec.spl`
- `test/system/compiler/sample/python_inspired_sample/collections_spec.spl`

**Analysis:**
- **Rust tests:** Test low-level runtime value representation
- **Simple tests:** Test high-level collection API
- **Verdict:** NOT REDUNDANT (different layers)
  - Rust: Internal implementation
  - Simple: Public API behavior

**Recommendation:** Keep both

### 2. File I/O Tests

**Rust:**
- `rust/runtime/src/value/file_io/async_file_tests.rs`
- Tests: Async file operations at runtime level

**Simple:**
- Tests using `rt_file_*` FFI functions in various specs
- Application-level file I/O tests

**Analysis:**
- **Rust tests:** Test async runtime implementation
- **Simple tests:** Test FFI interface and application usage
- **Verdict:** NOT REDUNDANT (different layers)

**Recommendation:** Keep both

### 3. Async/Generator Tests

**Rust:**
- `rust/runtime/src/value/async_gen_tests.rs`
- `rust/runtime/src/value/generator_tests.rs`
- `rust/runtime/src/value/actor_tests.rs`

**Simple:**
- `test/system/features/async_effects/async_effects_spec.spl`
- `test/system/features/async_features/async_features_spec.spl`

**Analysis:**
- **Rust tests:** Test runtime async/generator primitives
- **Simple tests:** Test async/await syntax and semantics
- **Verdict:** NOT REDUNDANT (different layers)

**Recommendation:** Keep both

### 4. UPX Compression Tests

**Rust:**
- `rust/runtime/tests/upx_integration_test.rs`
- `rust/runtime/tests/upx_compress_test.rs`

**Simple:**
- No equivalent Simple tests found

**Analysis:**
- **Rust tests:** Test UPX library integration
- **Simple tests:** None (should exist!)
- **Verdict:** MISSING SIMPLE TESTS

**Recommendation:**
- Keep Rust tests
- Add Simple tests for `compress.upx` module

### 5. Monoio Tests (Event Loop)

**Rust:**
- `rust/runtime/tests/monoio_basic_test.rs`
- `rust/runtime/tests/monoio_buffer_test.rs`
- `rust/runtime/tests/monoio_data_transfer_test.rs`
- `rust/runtime/tests/monoio_integration_test.rs`

**Simple:**
- No equivalent tests (async runtime tested differently)

**Analysis:**
- **Rust tests:** Test low-level event loop implementation
- **Verdict:** KEEP (no Simple equivalent possible)

**Recommendation:** Keep all Monoio tests (runtime core)

### 6. Vulkan FFI Tests

**Rust:**
- `rust/runtime/tests/vulkan_ffi_tests.rs`

**Simple:**
- No equivalent tests

**Analysis:**
- **Rust tests:** Test Vulkan GPU bindings
- **Verdict:** KEEP (FFI integration tests)

**Recommendation:** Keep (no Simple equivalent needed)

### 7. AOP Tests

**Rust:**
- `rust/runtime/tests/aop_around_tests.rs`

**Simple:**
- Likely has feature tests in `test/system/features/`

**Analysis:**
- Need to investigate if AOP is tested in Simple
- If yes, Rust tests may be redundant

**Recommendation:** Investigate further

## Rust Tests That Should Stay

### Runtime Core (MUST KEEP)
- `rust/runtime/src/bytecode/tests.rs` - Bytecode interpreter
- `rust/runtime/src/bytecode/vm_tests.rs` - VM implementation
- `rust/runtime/src/executor_tests.rs` - Runtime executor
- All Monoio tests - Event loop
- Vulkan FFI tests - GPU integration
- Sandbox tests - `rust/runtime/src/sandbox/linux_tests.rs`

**Reason:** Low-level runtime internals, no Simple equivalent possible

### Loader System (MUST KEEP)
- `rust/loader/tests/loader_tests.rs`
- `rust/loader/src/cross_test.rs`
- `rust/native_loader/tests/native_loader_tests.rs`

**Reason:** Module loading is runtime core functionality

### SDK/Utilities (SHOULD KEEP)
- `rust/sdn/tests/handler_tests.rs` - SDN parser tests
- `rust/common/tests/dyn_loader_tests.rs` - Dynamic loading
- `rust/common/tests/manual_memory_tests.rs` - Memory management

**Reason:** Low-level utilities, critical for correctness

## Rust Tests That Could Be Migrated

### Application-Level Tests (CANDIDATES)

None identified yet - most Rust tests are for runtime core.

**Investigation needed:** Check if any tests in `rust/util/` can be migrated.

## Obsolete Test Files (Candidates for Removal)

### Duplicate Sample Files

**Found:**
- `test/system/interpreter/sample/python_inspired_sample/` - Has both `.py`, `.sdt`, `.spl` versions
- `test/system/compiler/sample/python_inspired_sample/` - Duplicate of above

**Analysis:**
- Multiple copies of the same test samples
- `.py` and `.sdt` files may be obsolete (outdated formats)

**Recommendation:**
1. Keep `.spl` versions only
2. Remove `.py` and `.sdt` duplicates
3. Consolidate `interpreter/sample` and `compiler/sample` if identical

**Estimated cleanup:** ~50-100 files

### Build Artifacts

**Found:**
- `.simple/build/*.smf` files in test directories
- Compiled test binaries

**Recommendation:**
- Add to `.gitignore`
- Clean up existing artifacts
- Estimated: 100-200 files

## Test Coverage Gaps

### Missing Simple Tests

1. **UPX Compression** - No Simple tests for `compress.upx` module
   - Rust has: `upx_integration_test.rs`, `upx_compress_test.rs`
   - Simple needs: `test/std/upx_spec.spl`

2. **Path Utilities** - Created but blocked by module system
   - Created: `test/std/path_spec.spl` (85 tests)
   - Status: Can't run yet (module system limitation)

3. **Package Management** - May need more coverage
   - Existing: Some tests in system tests
   - Needed: Comprehensive `test/std/package_spec.spl`

## Recommendations

### Phase 1: Cleanup Obsolete Files (2-3 hours)

**Remove duplicates:**
```bash
# Remove .py and .sdt sample files (keep .spl only)
find test/system/ -name "*.py" -o -name "*.sdt" | xargs rm

# Remove build artifacts from test directories
find test/ -name ".simple" -type d | xargs rm -rf
```

**Estimated impact:** -150 to -200 files

### Phase 2: Consolidate Samples (1 hour)

**Merge duplicate sample directories:**
- Keep: `test/system/features/` (primary location)
- Remove: Duplicate samples in `interpreter/sample/` and `compiler/sample/`

**Estimated impact:** -50 to -100 files

### Phase 3: Document Test Strategy (30 minutes)

**Create:** `doc/test/test_strategy.md`

**Content:**
- When to write Rust tests (runtime core, FFI, performance-critical)
- When to write Simple tests (application logic, API behavior, features)
- How to avoid redundancy

### Phase 4: Add Missing Simple Tests (2-3 hours)

**Create:**
1. `test/std/upx_spec.spl` - UPX compression tests
2. Update `test/std/path_spec.spl` when module system fixed
3. `test/std/package_spec.spl` - Package management tests

**Estimated:** 100-150 new tests

## Test Organization Proposal

### Rust Tests (Keep ~50 files)
**Purpose:** Runtime core, FFI, low-level operations

**Location:** `rust/*/tests/` and `rust/*/src/*/tests.rs`

**Categories:**
- Runtime internals (bytecode, VM, executor)
- Event loop (Monoio)
- FFI bindings (Vulkan, UPX, etc.)
- Memory management
- Module loading

### Simple Tests (692 files → ~550 after cleanup)
**Purpose:** Application logic, API behavior, feature tests

**Location:** `test/`

**Categories:**
- `test/system/features/` - Feature tests (primary)
- `test/std/` - Standard library tests
- `test/unit/` - Unit tests for Simple modules
- `test/integration/` - Integration tests
- `test/compiler/` - Compiler behavior tests

## Cleanup Commands

### Safe Cleanup (Remove obvious obsolete files)

```bash
# Remove Python sample files (obsolete format)
find test/ -name "*.py" -delete

# Remove SDT sample files (obsolete format)
find test/ -name "*.sdt" -delete

# Remove build artifacts from test directories
find test/ -name ".simple" -type d -exec rm -rf {} +

# Remove compiled test binaries
find test/ -name "*.smf" -delete
```

**Before running:** Verify with dry run
```bash
find test/ -name "*.py" -o -name "*.sdt" -o -name "*.smf"
find test/ -name ".simple" -type d
```

### Aggressive Cleanup (Requires review)

```bash
# Consolidate duplicate samples (REVIEW FIRST)
# Compare directories to ensure identical before removing:
diff -r test/system/interpreter/sample/python_inspired_sample/ \
        test/system/compiler/sample/python_inspired_sample/

# If identical, remove one
rm -rf test/system/compiler/sample/python_inspired_sample/
```

## Metrics

### Current State
| Category | Count | Notes |
|----------|-------|-------|
| Simple tests | 692 files | Primarily SSpec |
| Rust tests | ~50 files | Runtime core |
| Obsolete files (estimate) | 150-200 | `.py`, `.sdt`, build artifacts |
| Duplicate samples | 50-100 | Duplicate directories |

### After Cleanup (Projected)
| Category | Count | Change |
|----------|-------|--------|
| Simple tests | ~550 files | -142 (obsolete removed) |
| Rust tests | ~50 files | 0 (all necessary) |
| Total test files | ~600 | -142 (-19%) |

**Reduction:** ~200 obsolete files removed, cleaner test structure

## Verification Steps

### Before Cleanup
```bash
# Count current files
find test/ -name "*.spl" | wc -l  # Should be 692
find test/ -name "*.py" | wc -l   # Obsolete count
find test/ -name "*.smf" | wc -l  # Build artifacts
```

### After Cleanup
```bash
# Verify cleanup
find test/ -name "*.py" | wc -l   # Should be 0
find test/ -name "*.sdt" | wc -l  # Should be 0
find test/ -name ".simple" -type d | wc -l  # Should be 0

# Run tests to ensure nothing broke
simple test
```

### Verify No Loss of Coverage
```bash
# Before cleanup: Record test count
simple test --list | wc -l  # e.g., 500 tests

# After cleanup
simple test --list | wc -l  # Should be same or higher (not lower)
```

## Risk Assessment

### Low Risk (Safe to Remove)
- ✅ `.py` files (Python samples, obsolete format)
- ✅ `.sdt` files (Old data format, replaced by SDN)
- ✅ `.smf` build artifacts (regenerated by builds)
- ✅ `.simple/build/` directories (build artifacts)

### Medium Risk (Review First)
- ⚠️ Duplicate sample directories (verify identical before removing)
- ⚠️ Old Rust tests with no Simple equivalent (may still be needed)

### High Risk (Do NOT Remove)
- ❌ Any Rust runtime tests (all are necessary)
- ❌ Any working `.spl` test files
- ❌ Integration tests (even if seemingly duplicate)

## Next Steps

### Immediate (This Session)
1. ⏳ Run safe cleanup commands (remove .py, .sdt, build artifacts)
2. ⏳ Verify tests still pass after cleanup
3. ⏳ Document cleanup in completion report

### Short Term (Next Session)
1. Create `test/std/upx_spec.spl` (UPX compression tests)
2. Review and consolidate duplicate sample directories
3. Create test strategy documentation

### Long Term (Future)
1. Establish test guidelines (when Rust vs Simple)
2. Regular cleanup of build artifacts (CI job)
3. Prevent test duplication through guidelines

## References

- Test database: `doc/test/test_db.sdn`
- Test results: `doc/test/test_result.md`
- Coverage session: `doc/report/coverage_session_2026-02-03.md`
- Migration plan: `doc/report/rust_to_simple_migration_2026-02-03.md`

---

**Status:** Analysis complete
**Recommendation:** Proceed with safe cleanup (150-200 obsolete files)
**Risk:** Low (only removing build artifacts and obsolete formats)
**Benefit:** Cleaner test structure, easier navigation
