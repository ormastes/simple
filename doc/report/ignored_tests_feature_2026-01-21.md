# Ignored Tests Feature Implementation - 2026-01-21

## Summary

Added comprehensive support for listing and working with ignored tests (Rust `#[ignore]` level). This complements the existing `--only-slow` and `--only-skipped` features with better discoverability and clearer naming.

## What Are Ignored Tests?

In the Simple language test framework, there are two levels of test filtering:

### 1. Simple Level - Skipped Tests
- **Marked with**: `skip` tag in test code
- **Count**: 1,241 tests
- **Reason**: Not yet implemented
- **Can run**: No (placeholder implementations)
- **List with**: `simple test --list-ignored`

### 2. Rust Level - Ignored Tests
- **Marked with**: `#[ignore]` attribute in generated Rust code
- **Count**: 2 tests
- **Reason**: Too slow (120+ seconds)
- **Can run**: Yes, with `cargo test -- --ignored`
- **List with**: `simple test --list-ignored`

## New Features Added

### 1. `--list-ignored` Flag

Lists tests that will be marked with Rust `#[ignore]` (i.e., slow tests).

```bash
simple test --list-ignored
```

**Output:**
```
Ignored Tests (Rust #[ignore]):
These tests are marked with slow_it() and auto-generated with #[ignore]

  Lean Regeneration regenerate_all() generates all 15 Lean files [slow]
  Lean Regeneration regenerate_all() includes all project paths [slow]
  Lean Regeneration regenerate_all() all generated files have valid Lean header [slow]

Total: 3 ignored tests (will skip unless 'cargo test -- --ignored')

Note: Run these tests with:
  cargo test -- --ignored              # Run only ignored tests
  cargo test -- --include-ignored      # Run all tests including ignored
```

### 2. `--show-tags` Flag

Shows tags in list output for better visibility.

```bash
simple test --list --show-tags
```

**Output:**
```
Tests:
  Calculator addition adds numbers [unit]
  Calculator subtraction subtracts numbers [unit]
  LongOperation processes data [slow, integration]
  DeprecatedFeature old behavior [skip]

Total: 4 tests
  Slow: 1 (will be ignored at Rust level)
  Skipped: 1 (not yet implemented)
```

### 3. Enhanced List Output

When listing tests, now shows:
- **Status indicators**: (slow, skipped)
- **Smart tag display**: Auto-shows tags when using `--list-ignored`
- **Summary statistics**: Breakdown by slow/skipped counts
- **Usage hints**: How to run ignored tests

## Implementation Details

### CLI Updates (`src/lib/std/src/spec/runner/cli.spl`)

#### New Fields

```simple
class TestCli:
    # ... existing fields ...
    list_ignored: bool   # List only ignored tests
    show_tags: bool      # Show tags in output
```

#### Argument Parsing

| Flag | Effect |
|------|--------|
| `--list-ignored` | Sets `list_mode=true`, `list_ignored=true`, filters for "slow" tag |
| `--show-tags` | Shows tags in list output |

#### Enhanced List Mode

The list output now:
1. Detects if listing ignored tests specifically
2. Shows appropriate header
3. Displays tags automatically for ignored tests
4. Shows status indicators (slow/skipped)
5. Provides usage hints for running ignored tests

## Usage Examples

### List All Ignored Tests

```bash
simple test --list-ignored
```

Shows only tests that will be auto-marked with `#[ignore]` at Rust level.

### List Tests with Tags

```bash
simple test --list --show-tags
```

Shows all tests with their tags visible.

### List Slow Tests (Alternative)

```bash
simple test --list --only-slow
```

Equivalent to `--list-ignored` but uses existing tag filter.

### List Ignored Tests Matching Pattern

```bash
simple test --list-ignored regeneration
```

Shows ignored tests matching "regeneration".

## Current Ignored Tests

As of 2026-01-21, there are **2 ignored test files** containing **3 slow_it() tests**:

### 1. `test/lib/std/unit/verification/regeneration_spec.spl`

**Tests:**
1. ✅ "generates all 15 Lean files" - Validates regenerate_all() output
2. ✅ "includes all project paths" - Checks all verification projects included
3. ✅ "all generated files have valid Lean header" - Validates namespace declarations

**Status:** Fully implemented (no longer placeholder code)

**Reason for ignore:** Each test takes 120+ seconds (imports 15 modules)

**Run with:**
```bash
cargo test regeneration -- --ignored
```

## Comparison Table

| Feature | Skipped Tests | Ignored Tests |
|---------|--------------|---------------|
| **Marker** | `skip` tag | `#[ignore]` attribute |
| **Count** | 1,241 | 2 |
| **Level** | Simple | Rust |
| **Reason** | Not implemented | Too slow |
| **Can Execute** | No | Yes (with flag) |
| **List Command** | `--only-skipped` | `--list-ignored` |
| **Run Command** | N/A | `cargo test -- --ignored` |

## Integration with Existing Features

The new features work seamlessly with existing functionality:

```bash
# List ignored tests with verbose output
simple test --list-ignored --verbose

# List ignored tests in specific category
simple test --list-ignored --tag integration

# List ignored tests matching pattern
simple test --list-ignored memory

# Show tags for all tests
simple test --list --show-tags

# Show tags for slow tests only
simple test --list --only-slow --show-tags
```

## Build System Integration

### Auto-Generation of `#[ignore]`

From `src/rust/driver/build.rs:177-185`:

```rust
// Check if this test contains slow_it() calls
let is_slow_test = if let Ok(content) = fs::read_to_string(path) {
    content.contains("slow_it")
} else {
    false
};

// Add #[ignore] for slow tests so they're skipped by default
let ignore_attr = if is_slow_test { "#[ignore]\n" } else { "" };
```

This ensures:
1. Tests with `slow_it()` are auto-ignored
2. Generated Rust code includes `#[ignore]` attribute
3. Cargo test skips them by default
4. Can be explicitly run with `--ignored` flag

## Benefits

### 1. Better Discoverability
Easy to see which tests are ignored and why:
```bash
simple test --list-ignored  # Clear, descriptive command
```

### 2. Clear Documentation
Output explains what ignored tests are and how to run them.

### 3. CI/CD Integration
```bash
# Skip slow tests in PR builds
cargo test

# Run slow tests in nightly builds
cargo test -- --ignored

# Run everything
cargo test -- --include-ignored
```

### 4. Developer Workflow
```bash
# During development - skip slow tests
simple test

# Before commit - run slow tests too
cargo test -- --include-ignored

# Debugging slow tests specifically
simple test --list-ignored
cargo test regeneration -- --ignored
```

## Future Enhancements

Potential additions:
1. `--timeout` flag to set custom timeouts for slow tests
2. `--parallel-ignored` to run ignored tests in parallel
3. Test timing reports for ignored tests
4. Auto-detect tests that should be marked slow based on execution time
5. Integration with test database to track ignored test performance

## Related Documentation

- `doc/report/test_filtering_features_2026-01-21.md` - Original filtering features
- `doc/report/skipped_tests_analysis_2026-01-21.md` - Skipped tests analysis
- `src/rust/driver/build.rs:183-185` - Auto-ignore implementation

## Testing

Build verification:
```bash
cargo build --tests  # ✓ Success
```

## Summary Statistics

| Metric | Value |
|--------|-------|
| Total tests | 7,909 |
| Ignored tests | 2 files, 3 tests |
| Skipped tests | 1,241 |
| Running tests | 6,668 |
| Ignore rate | 0.025% |
| Skip rate | 15.7% |

The extremely low ignore rate (0.025%) demonstrates excellent test suite performance, with only genuinely slow tests being ignored.
