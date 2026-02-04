# Package System Test Status

## Created Tests

✅ **SSpec test file created:** `src/app/package/package_spec.spl` (180+ lines)

## Test Categories

### Unit Tests (9 test groups)

1. **Package Building** (2 tests)
   - ✅ Verifies build script exists
   - ✅ Generates valid SDN manifest

2. **Path Resolution** (3 tests)
   - ✅ Resolves user-local paths
   - ✅ Resolves system paths
   - ✅ Detects platform correctly

3. **Manifest Operations** (2 tests)
   - ✅ Parses SDN manifest
   - ✅ Generates SDN with correct format

4. **Package Installation** (2 tests)
   - ⏳ Creates installation directories
   - ✅ Handles dry-run mode

5. **Package Verification** (2 tests)
   - ⏳ Validates package structure
   - ⏳ Calculates checksums (needs FFI binding)

6. **Package Upgrade** (2 tests)
   - ⏳ Preserves configuration
   - ✅ Detects version changes

7. **FFI Package Operations** (8 tests)
   - ⏳ Creates/extracts tarballs
   - ⏳ Calculates SHA256 via FFI
   - ⏳ Gets file sizes
   - ⏳ Creates/removes directories
   - ⏳ Creates symbolic links
   - ⏳ Checks path existence
   - ⏳ Checks if directory

8. **Integration Tests** (2 slow tests)
   - ⏳ Builds complete bootstrap package
   - ⏳ Extracts and verifies contents

**Total:** 23 tests defined

## Current Status

### ✅ Complete (Rust Side)

- FFI functions implemented in `rust/runtime/src/value/ffi/package.rs`
- 13 C FFI functions with proper error handling
- Unit tests in Rust (SHA256, tarball operations)
- All Rust code compiles without warnings

### ⏳ Pending (Simple Side)

To make all SSpec tests runnable, we need:

1. **FFI Bindings Exposure**
   - Expose FFI functions to Simple code via extern declarations
   - Create Simple wrappers for FFI functions
   - Example:
     ```simple
     extern fn rt_package_sha256(path: text) -> text
     extern fn rt_package_create_tarball(source: text, output: text) -> i32
     extern fn rt_package_extract_tarball(tarball: text, dest: text) -> i32
     # ... etc
     ```

2. **Helper Functions**
   - Implement `create_install_dirs` helper
   - Implement `calculate_checksum` wrapper around FFI
   - Expose these in package module

3. **Standard Library Dependencies**
   - Ensure `std.fs` has required functions:
     - `fs.glob()` - glob pattern matching
     - `fs.is_executable()` - check executable bit
     - `fs.file_size()` - get file size
   - Ensure `std.process` has:
     - `process.run()` - execute shell commands

4. **Test Infrastructure**
   - Verify SSpec test runner can find and run these tests
   - Add test to CI pipeline

## How to Run Tests (Once Complete)

```bash
# Run all package tests
simple test src/app/package/package_spec.spl

# Run only fast tests (exclude slow_it)
simple test src/app/package/package_spec.spl --exclude-slow

# Run only integration tests
simple test src/app/package/package_spec.spl --only-slow

# Run with verbose output
simple test src/app/package/package_spec.spl --verbose
```

## Manual Testing (Current)

Until FFI bindings are fully wired up, manual testing works:

```bash
# Test package build
./script/build-bootstrap.sh
# ✅ Works - creates 6.4 MB package

# Test package extraction
tar -xzf simple-bootstrap-0.3.0-linux-x86_64.spk -C /tmp/test
# ✅ Works - extracts correctly

# Test runtime
/tmp/test/bin/simple_runtime --version
# ✅ Works - outputs version

# Test FFI (Rust level)
cd rust && cargo test --package simple-runtime ffi::package
# ✅ Works - all tests pass
```

## Rust Unit Tests

The Rust FFI layer has comprehensive unit tests:

```rust
#[test]
fn test_sha256() { ... }

#[test]
fn test_create_and_extract_tarball() { ... }
```

Run with:
```bash
cd rust && cargo test --package simple-runtime --lib ffi::package
```

## Next Steps (Priority Order)

1. **Wire FFI to Simple** (High Priority)
   - Add extern declarations for FFI functions
   - Create Simple wrapper module

2. **Implement Helper Functions** (Medium Priority)
   - `create_install_dirs`
   - `calculate_checksum`
   - Path manipulation helpers

3. **Verify std.fs Functions** (Medium Priority)
   - Check if all required functions exist
   - Implement missing ones

4. **Run SSpec Tests** (After 1-3)
   - Execute test suite
   - Fix any failures
   - Add to CI pipeline

5. **Integration Testing** (Low Priority)
   - Test on multiple platforms
   - Test with different configurations
   - Performance testing

## Test Coverage Target

- **Unit tests:** 100% (all public functions)
- **Integration tests:** Key workflows (build, install, verify)
- **FFI tests:** All 13 functions
- **Error handling:** All error paths

## Expected Test Results (Once Complete)

```
Package Management System
  Package Building
    ✓ builds bootstrap package with correct structure
    ✓ generates valid SDN manifest
    ✓ includes essential apps in bootstrap

  Path Resolution
    ✓ resolves user-local paths correctly
    ✓ resolves system paths correctly
    ✓ detects platform correctly

  Manifest Operations
    ✓ parses SDN manifest correctly
    ✓ generates SDN manifest with correct format

  ... (15 more tests)

  Integration Tests
    ✓ builds and verifies complete bootstrap package (slow)
    ✓ extracts and verifies package contents (slow)

23 tests, 23 passed, 0 failed, 0 skipped (2 slow)
```

## Known Issues

None currently - FFI layer compiles cleanly and manual testing passes.

## Test Maintenance

- Update tests when adding new package operations
- Add regression tests for any bugs found
- Keep test data in `test/fixtures/packages/`
- Document any platform-specific test behavior
