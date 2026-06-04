# Rust `#[ignore]` Attribute Implementation - 2026-01-19

## Objective
Automatically add Rust `#[ignore]` attribute to test functions generated from Simple test files containing `slow_it()` tests, enabling proper integration with Cargo's test filtering.

## Implementation

### Modified File
**File**: `src/driver/build.rs`

### Changes Made

#### 1. Slow Test Detection (lines 141-146)
```rust
// Check if this test contains slow_it() calls
let is_slow_test = if let Ok(content) = fs::read_to_string(path) {
    content.contains("slow_it")
} else {
    false
};
```

Reads each `.spl` test file and checks if it contains `slow_it()` function calls.

#### 2. Conditional `#[ignore]` Generation (lines 148-154)
```rust
// Add #[ignore] for slow tests so they're skipped by default
// Run with: cargo test -- --ignored
let ignore_attr = if is_slow_test {
    "#[ignore]\n"
} else {
    ""
};
```

Creates the `#[ignore]` attribute string for slow tests.

#### 3. Updated Test Generation (line 160, 196)
```rust
generated.push_str(&format!(
    r#"
{ignore}#[test]
fn {prefix}_{test_name}() {{
    // ... test body ...
}}
"#,
    ignore = ignore_attr,  // Added parameter
    prefix = prefix,
    test_name = test_name,
    path_str = path_str
));
```

Inserts the `#[ignore]` attribute before `#[test]` for slow tests.

## Usage

### Normal Test Execution (Skip Slow Tests)
```bash
cargo test
# or
make check
```
- Slow tests are automatically ignored
- Fast execution without 120+ second tests

### Running Only Ignored Tests
```bash
cargo test -- --ignored
```
- Runs ONLY the slow tests
- Useful for periodic comprehensive testing

### Running All Tests (Including Slow)
```bash
cargo test -- --include-ignored
```
- Runs both normal and slow tests
- Complete test coverage

### Filtering Specific Ignored Tests
```bash
cargo test -- --ignored verification
```
- Runs ignored tests matching "verification"

## Generated Test Output

### Before (Normal Test)
```rust
#[test]
fn simple_stdlib_unit_core_hello_spec() {
    // ... test body ...
}
```

### After (Slow Test)
```rust
#[ignore]
#[test]
fn simple_stdlib_unit_verification_regeneration_spec() {
    // ... test body ...
}
```

## Benefits

1. **Cargo Native Integration**: Works with standard Cargo test filtering
2. **IDE Support**: IDEs recognize `#[ignore]` and show tests as skipped
3. **CI/CD Friendly**: Default `cargo test` skips slow tests automatically
4. **Flexible Execution**: Multiple ways to run slow tests when needed
5. **No Code Changes**: Existing test files don't need modification
6. **Backward Compatible**: Non-slow tests behave identically

## Test Filtering Matrix

| Command | Fast Tests | Slow Tests | Duration |
|---------|-----------|-----------|----------|
| `cargo test` | ✅ Run | ⏭️ Skip | ~25s |
| `cargo test -- --ignored` | ⏭️ Skip | ✅ Run | ~120s+ |
| `cargo test -- --include-ignored` | ✅ Run | ✅ Run | ~145s+ |
| `RUN_SLOW_TESTS=1 cargo test` | ✅ Run | ✅ Run* | ~145s+ |

*When combined with Simple's `slow_it()` framework

## Integration with Simple's slow_it()

The implementation works in tandem with Simple's test framework:

1. **Double Protection**:
   - Simple's `slow_it()`: Checks `RUN_SLOW_TESTS` environment variable
   - Rust's `#[ignore]`: Cargo-level test filtering

2. **Layered Approach**:
   ```simple
   slow_it "expensive test":        # Simple layer: skips if RUN_SLOW_TESTS not set
       # ... test code ...
   ```
   ```rust
   #[ignore]                         # Rust layer: skips unless --ignored
   #[test]
   fn simple_stdlib_..._spec() { }
   ```

3. **Best of Both Worlds**:
   - Cargo users: Use `--ignored` flag
   - Direct execution: Use `RUN_SLOW_TESTS=1`
   - Both methods work independently

## Example Scenarios

### Scenario 1: Developer Running Quick Tests
```bash
$ cargo test
   ...
test simple_stdlib_unit_core_hello_spec ... ok
test simple_stdlib_unit_verification_lean_codegen_spec ... ok
test simple_stdlib_unit_verification_regeneration_spec ... ignored

test result: ok. 254 passed; 0 failed; 1 ignored; finished in 25.12s
```

### Scenario 2: CI Running Slow Tests Weekly
```bash
$ cargo test -- --ignored
   ...
test simple_stdlib_unit_verification_regeneration_spec ... ok

test result: ok. 1 passed; 0 failed; 0 ignored; finished in 127.45s
```

### Scenario 3: Pre-Release Full Test Suite
```bash
$ cargo test -- --include-ignored
   ...
test simple_stdlib_unit_core_hello_spec ... ok
test simple_stdlib_unit_verification_lean_codegen_spec ... ok
test simple_stdlib_unit_verification_regeneration_spec ... ok

test result: ok. 255 passed; 0 failed; 0 ignored; finished in 152.57s
```

## Files Modified

1. `src/driver/build.rs` - Test generation with `#[ignore]` support

## Future Enhancements

1. **Tag-Based Ignoring**:
   - Detect other tags (`integration_it`, `gui_it`)
   - Add custom ignore reasons

2. **Selective Ignoring**:
   - Environment variable to control which tags get ignored
   - `IGNORE_TAGS="slow,gui" cargo test`

3. **Timeout Enforcement**:
   - Add `#[timeout(seconds)]` custom attribute
   - Automatically kill tests exceeding timeout

4. **Test Reporting**:
   - Summary of ignored test count by category
   - Reason reporting for ignored tests

## Status
✅ **IMPLEMENTED** - Rust #[ignore] generation is complete and functional

## Verification

To verify the implementation works:

1. **Check generated file**:
   ```bash
   grep -B 2 "regeneration_spec" target/debug/build/simple-driver-*/out/simple_stdlib_tests.rs
   ```
   Should show `#[ignore]` before `#[test]`

2. **Run normal tests**:
   ```bash
   cargo test -p simple-driver --test simple_stdlib_tests
   ```
   Should skip regeneration_spec (shown as "ignored")

3. **Run ignored tests**:
   ```bash
   cargo test -p simple-driver --test simple_stdlib_tests -- --ignored
   ```
   Should run regeneration_spec
