# Simple Std Lib Test Integration with Rust

## Overview

This document describes the design for integrating Simple language standard library tests with Rust's test framework. The goal is to:

1. **Discovery**: Automatically discover `.spl` test files in `simple/std_lib/test/`
2. **Visibility**: Show Simple tests in `cargo test` output alongside Rust tests
3. **Execution**: Run Simple tests through the existing Simple compiler/interpreter
4. **Reporting**: Report pass/fail with meaningful error messages in Rust test format

## Architecture

```
┌─────────────────────────────────────────────────────────────────────┐
│                         cargo test                                   │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│  ┌─────────────────────┐     ┌─────────────────────────────────┐   │
│  │ Rust Unit Tests     │     │ Simple Std Lib Tests            │   │
│  │ (native #[test])    │     │ (generated via build.rs)        │   │
│  └─────────────────────┘     └─────────────────────────────────┘   │
│                                        │                             │
│                                        ▼                             │
│                              ┌─────────────────────┐                │
│                              │ Test Discovery      │                │
│                              │ (glob .spl files)   │                │
│                              └─────────────────────┘                │
│                                        │                             │
│                                        ▼                             │
│                              ┌─────────────────────┐                │
│                              │ Test Execution      │                │
│                              │ (SimpleTestRunner)  │                │
│                              └─────────────────────┘                │
│                                        │                             │
│                                        ▼                             │
│                              ┌─────────────────────┐                │
│                              │ Result Collection   │                │
│                              │ (TestResult enum)   │                │
│                              └─────────────────────┘                │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
```

## Components

### 1. Test Discovery Module (`simple_test_discovery`)

Location: `src/driver/src/simple_test.rs`

```rust
/// Discovered Simple test file
pub struct SimpleTestFile {
    /// Absolute path to the .spl file
    pub path: PathBuf,
    /// Relative path from test root (for display)
    pub relative_path: String,
    /// Test category (unit, integration, system)
    pub category: TestCategory,
    /// Discovered test names (from BDD blocks)
    pub test_names: Vec<String>,
}

pub enum TestCategory {
    Unit,
    Integration,
    System,
    Fixture,
}

/// Discover all Simple test files
pub fn discover_tests(test_root: &Path) -> Vec<SimpleTestFile> {
    // 1. Walk test_root recursively
    // 2. Find all *_spec.spl and *_test.spl files
    // 3. Parse to extract describe/it block names
    // 4. Return list of test files with metadata
}
```

### 2. Test Runner Module (`SimpleTestRunner`)

Location: `src/driver/src/simple_test.rs`

```rust
/// Result of running a Simple test
pub enum SimpleTestResult {
    /// All tests in the file passed
    Pass {
        file: String,
        passed_count: usize,
        duration_ms: u64,
    },
    /// Some tests failed
    Fail {
        file: String,
        passed_count: usize,
        failed_count: usize,
        failures: Vec<TestFailure>,
        duration_ms: u64,
    },
    /// Test file failed to compile
    CompileError {
        file: String,
        error: String,
    },
    /// Test file failed to run (runtime error)
    RuntimeError {
        file: String,
        error: String,
    },
}

pub struct TestFailure {
    pub test_name: String,
    pub message: String,
    pub location: Option<String>,
}

/// Run a single Simple test file
pub fn run_test_file(path: &Path) -> SimpleTestResult {
    // 1. Read file content
    // 2. Compile using existing compiler pipeline
    // 3. Execute with test runtime enabled
    // 4. Collect and return results
}
```

### 3. Build-time Test Generation (`build.rs`)

Location: `src/driver/build.rs` or `tests/build.rs`

```rust
//! Build script that generates Rust test wrappers for Simple tests

fn main() {
    let test_root = Path::new("../../simple/std_lib/test");
    let out_dir = env::var("OUT_DIR").unwrap();
    let dest_path = Path::new(&out_dir).join("simple_tests.rs");

    let mut generated = String::new();

    // Discover test files
    for entry in walkdir::WalkDir::new(test_root) {
        let path = entry.path();
        if path.extension() == Some("spl".as_ref()) {
            let test_name = sanitize_test_name(path);
            generated.push_str(&format!(r#"
#[test]
fn simple_test_{test_name}() {{
    let result = simple_driver::simple_test::run_test_file(
        Path::new("{path}")
    );
    match result {{
        SimpleTestResult::Pass {{ .. }} => (),
        SimpleTestResult::Fail {{ failures, .. }} => {{
            panic!("Simple test failed:\n{{}}",
                failures.iter()
                    .map(|f| format!("  - {{}}: {{}}", f.test_name, f.message))
                    .collect::<Vec<_>>()
                    .join("\n")
            );
        }}
        SimpleTestResult::CompileError {{ error, .. }} => {{
            panic!("Failed to compile Simple test: {{}}", error);
        }}
        SimpleTestResult::RuntimeError {{ error, .. }} => {{
            panic!("Runtime error in Simple test: {{}}", error);
        }}
    }}
}}
"#, test_name = test_name, path = path.display()));
        }
    }

    fs::write(&dest_path, generated).unwrap();
    println!("cargo:rerun-if-changed={}", test_root.display());
}
```

### 4. Test Integration Module

Location: `tests/simple_stdlib_tests.rs`

```rust
//! Auto-generated tests for Simple standard library

// Include generated test functions
include!(concat!(env!("OUT_DIR"), "/simple_tests.rs"));
```

## Test File Naming Convention

| Pattern | Category | Description |
|---------|----------|-------------|
| `*_spec.spl` | Unit/Integration | BDD-style specification tests |
| `*_test.spl` | Unit/Integration | Traditional test files |
| `fixtures/*.spl` | Fixture | Test data, not executed as tests |

## Simple Test Syntax Support

The test runner must understand Simple's BDD syntax:

```simple
describe "ModuleName":
    context "when condition":
        before_each:
            # setup code

        after_each:
            # teardown code

        it "does something":
            expect result to eq expected

        it "handles errors":
            expect { risky_operation() } to raise ValueError
```

### Test Result Extraction

The runner parses stdout/stderr to extract test results:

```
# Success format:
✓ ModuleName > when condition > does something (2ms)

# Failure format:
✗ ModuleName > when condition > handles errors (5ms)
  Expected: ValueError
  Got: no error raised
  at test/unit/module_spec.spl:45

# Summary format:
Tests: 10 passed, 2 failed, 12 total
Time: 1.234s
```

## Implementation Phases

### Phase 1: Basic Discovery and Execution
- [ ] Implement `discover_tests()` function
- [ ] Implement `run_test_file()` function
- [ ] Add `build.rs` for test generation
- [ ] Create `tests/simple_stdlib_tests.rs`

### Phase 2: Result Parsing
- [ ] Parse BDD test output format
- [ ] Extract individual test pass/fail
- [ ] Capture failure messages and locations
- [ ] Report timing information

### Phase 3: Filtering and Categories
- [ ] Support `cargo test simple_` prefix filtering
- [ ] Add `--unit`, `--integration` category filters
- [ ] Support `--test-filter` pattern matching

### Phase 4: Parallel Execution
- [ ] Run test files in parallel
- [ ] Thread-safe result collection
- [ ] Proper output ordering

## File Structure

```
src/driver/
├── src/
│   ├── lib.rs              # Add simple_test module export
│   ├── simple_test.rs      # NEW: Test discovery and runner
│   └── ...
├── build.rs                # NEW: Test generation script
└── tests/
    └── simple_stdlib_tests.rs  # NEW: Generated test entry point

simple/std_lib/
├── test/
│   ├── unit/
│   │   └── doctest/
│   │       ├── parser_spec.spl
│   │       ├── matcher_spec.spl
│   │       └── runner_spec.spl
│   ├── integration/
│   │   └── doctest/
│   │       └── discovery_spec.spl
│   └── fixtures/
│       └── doctest/
│           └── sample.spl
```

## Configuration

### Cargo.toml additions

```toml
[package]
build = "build.rs"

[build-dependencies]
walkdir = "2.4"

[dev-dependencies]
# Already has what we need from simple_driver
```

### Environment Variables

| Variable | Description | Default |
|----------|-------------|---------|
| `SIMPLE_TEST_ROOT` | Override test directory | `simple/std_lib/test` |
| `SIMPLE_TEST_FILTER` | Pattern to filter tests | `*` |
| `SIMPLE_TEST_VERBOSE` | Show detailed output | `false` |
| `SIMPLE_TEST_PARALLEL` | Run tests in parallel | `true` |

## Usage Examples

### Run all Simple stdlib tests
```bash
cargo test simple_stdlib
```

### Run specific category
```bash
cargo test simple_stdlib_unit
cargo test simple_stdlib_integration
```

### Run specific module tests
```bash
cargo test simple_stdlib::doctest::parser
```

### Verbose output
```bash
SIMPLE_TEST_VERBOSE=1 cargo test simple_stdlib
```

## Expected Output

```
running 6 tests
test simple_stdlib_unit_doctest_parser_spec ... ok
test simple_stdlib_unit_doctest_matcher_spec ... ok
test simple_stdlib_unit_doctest_runner_spec ... ok
test simple_stdlib_integration_doctest_discovery_spec ... ok
test simple_stdlib_fixtures_doctest_sample ... ignored (fixture)
test result: ok. 4 passed; 0 failed; 1 ignored; 0 measured; 0 filtered out

   Simple stdlib tests: 45 passed, 0 failed (from 4 files)
```

## Error Reporting

### Compile Error
```
---- simple_stdlib_unit_doctest_parser_spec stdout ----
thread 'simple_stdlib_unit_doctest_parser_spec' panicked at 'Failed to compile Simple test:

  error: undefined variable `parse_docstring` at line 9
    |
  9 |     examples = parse_docstring(content)
    |                ^^^^^^^^^^^^^^^^

  Did you forget to import `std.doctest.parser`?
'
```

### Test Failure
```
---- simple_stdlib_unit_doctest_parser_spec stdout ----
thread 'simple_stdlib_unit_doctest_parser_spec' panicked at 'Simple test failed:

  ✗ DoctestParser > parse_docstring > parses simple example with output
    Expected: examples.len == 1
    Got: examples.len == 0
    at test/unit/doctest/parser_spec.spl:12
'
```

## Future Enhancements

1. **Coverage Integration**: Connect to `cargo-llvm-cov` for coverage reporting
2. **Watch Mode**: Auto-rerun on file changes
3. **IDE Integration**: Generate test metadata for VS Code test explorer
4. **Snapshot Testing**: Support for output snapshot comparison
5. **Benchmark Integration**: Run Simple benchmarks through `cargo bench`

## Related Documents

- `doc/test.md` - Test policy and levels
- `doc/spec/stdlib.md` - Standard library specification
- `simple/std_lib/README.md` - Stdlib structure
