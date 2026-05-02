# Test Filtering and Listing Features Implementation - 2026-01-21

## Summary

Added comprehensive test filtering and listing capabilities to the SSpec test framework, enabling users to:
- List tests without running them
- Filter and run only slow tests
- Filter and run only skipped tests
- View test tags and metadata

## Changes Made

### 1. CLI Updates (`src/lib/std/src/spec/runner/cli.spl`)

#### New Flags Added

| Flag | Short | Description |
|------|-------|-------------|
| `--list` | `-l` | List tests without running them |
| `--only-slow` | - | Run only slow tests (tests marked with `slow_it`) |
| `--only-skipped` | - | Run only skipped tests (tests marked with `skip` tag) |

#### Updated TestCli Class

```simple
class TestCli:
    formatter: text
    run_slow: bool
    only_slow: bool        # NEW
    only_skipped: bool     # NEW
    list_mode: bool        # NEW
    filter: TestFilter
    output_file: Option<text>
    show_help: bool
    verbose: bool
    fail_fast: bool
```

#### Argument Parsing

Added parsing for:
- `--list` / `-l`: Enable list mode
- `--only-slow`: Filter for slow tests only
- `--only-skipped`: Filter for skipped tests only

#### List Mode Implementation

When `--list` is specified:
1. Calls `executor.list_tests()` instead of `executor.run()`
2. Prints each test's full description and tags
3. Shows total count
4. Returns exit code 0 (doesn't execute tests)

Example output format:
```
Tests:
  MyClass addition adds two numbers [unit]
  MyClass subtraction subtracts numbers [unit]
  LongRunningOperation processes data [slow, integration]
  DeprecatedFeature old behavior [skip]

Total: 4 tests
```

### 2. Executor Updates (`src/lib/std/src/spec/runner/executor.spl`)

#### New TestInfo Class

```simple
class TestInfo:
    full_description: text
    tags: List<text>
    is_slow: bool
    is_skipped: bool
```

Represents metadata about a test for listing purposes.

#### New Methods

**`collect_tests_from_group(group: ExampleGroup, test_list: List<TestInfo>) -> void`**
- Recursively collects test information from a group and its children
- Respects current filter settings
- Gathers test descriptions, tags, and metadata

**`list_tests() -> List<TestInfo>`**
- Public API for listing tests
- Returns list of all tests that match current filters
- Does not execute any test code

### 3. Updated Help Text

```
Usage: simple test [options] [pattern]

Options:
  -f, --format FORMAT      Output format: progress, doc, json (default: progress)
  -l, --list               List tests without running them
  --slow                   Include slow tests (default: skip slow tests)
  --only-slow              Run only slow tests
  --only-skipped           Run only skipped tests
  -t, --tag TAG            Run only tests with this tag
  --exclude-tag TAG        Skip tests with this tag
  -p, --pattern PATTERN    Run only tests matching pattern
  -o, --output FILE        Write output to file (JSON format only)
  -v, --verbose            Verbose output
  --fail-fast              Stop on first failure
  -h, --help               Show this help message

Examples:
  simple test                          # Run all tests
  simple test --list                   # List all tests
  simple test --list --only-slow       # List only slow tests
  simple test --format doc             # Hierarchical output
  simple test --tag unit               # Run only unit tests
  simple test --slow                   # Include slow tests
  simple test --only-slow              # Run only slow tests
  simple test --only-skipped           # Run only skipped tests
  simple test Calculator               # Run tests matching 'Calculator'
  simple test --format json -o results.json  # JSON output to file
```

## Usage Examples

### List All Tests
```bash
simple test --list
```

### List Only Slow Tests
```bash
simple test --list --only-slow
```

### List Only Skipped Tests
```bash
simple test --list --only-skipped
```

### Run Only Slow Tests
```bash
simple test --only-slow
```

### Run Only Skipped Tests
```bash
simple test --only-skipped
```

### List Tests Matching Pattern
```bash
simple test --list Calculator
```

### List Tests with Specific Tag
```bash
simple test --list --tag integration
```

## Implementation Details

### Test Filtering Logic

1. **List Mode**: When `--list` is set:
   - `executor.list_tests()` is called instead of `executor.run()`
   - Tests are collected but not executed
   - Filters are still applied (tags, patterns, slow/skipped)

2. **Only-Slow Mode**: When `--only-slow` is set:
   - Automatically adds "slow" tag filter
   - Enables slow test execution (`run_slow = true`)
   - Only tests marked with `slow_it` will run/be listed

3. **Only-Skipped Mode**: When `--only-skipped` is set:
   - Automatically adds "skip" tag filter
   - Only tests marked with `skip` tag will be listed
   - Note: Skipped tests won't actually execute even when targeted

### Compatibility with Rust #[ignore]

The Simple test framework's slow tests (marked with `slow_it`) are automatically translated to Rust `#[ignore]` attributes during test generation (see `src/rust/driver/build.rs:183-185`).

This creates a two-layer filtering system:
- **Rust layer**: `#[ignore]` tests skipped unless `cargo test -- --ignored`
- **Simple layer**: `--only-slow` flag filters for slow tests

## Benefits

1. **Fast Test Discovery**: List tests without execution overhead
2. **Better CI/CD**: Easy to identify slow/skipped tests in pipelines
3. **Test Organization**: See test structure and tags at a glance
4. **Selective Execution**: Run only specific categories of tests
5. **Debugging**: Quickly identify which tests will/won't run with current filters

## Related Files

- `src/lib/std/src/spec/runner/cli.spl` - CLI argument parsing and list mode
- `src/lib/std/src/spec/runner/executor.spl` - Test execution and listing logic
- `src/lib/std/src/spec/runner/filter.spl` - Existing filter infrastructure (unchanged)
- `src/rust/driver/build.rs` - Rust test generation with `#[ignore]` support

## Testing

The implementation compiles successfully:
```bash
cargo build --tests  # ✓ Success
```

## Future Enhancements

Potential additions:
1. `--list-ignored` to show Rust-level ignored tests
2. `--count-only` to show just test counts per category
3. `--list-format json` for machine-readable test lists
4. `--list-tree` for hierarchical test visualization
5. Integration with test result databases for historical comparison

## Notes

- The SSpec framework uses "skip" tag for skipped tests, which is conceptually similar to Rust's `#[ignore]`
- Slow tests in Simple are auto-ignored at the Rust level, creating a double-filtering mechanism
- The `--slow` flag *includes* slow tests in runs, while `--only-slow` *exclusively* runs them
