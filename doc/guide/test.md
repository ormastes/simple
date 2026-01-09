# Test Policy

## Overview

This document defines the test strategy for the Simple language compiler, using `simple_mock_helper` for mock policy enforcement and coverage tracking.

**Current Test Count: 807+ tests**

## Test Categories and Directory Structure

Tests are organized into four categories with separate coverage tracking:

```
# Rust unit tests in each crate (631+ tests total):
src/parser/       # 115 tests (50 inline + 65 in tests/)
src/compiler/     # 79 tests (57 inline + 22 in tests/)
src/common/       # 29 tests (18 inline + 11 in tests/)
src/type/         # 68 tests (in tests/inference.rs)
src/driver/       # 216 tests (in tests/)
src/loader/       # 21 tests (in tests/)
src/runtime/      # 19 tests (in tests/)
src/native_loader/# 11 tests
src/lib/          # 2 tests
simple_mock_helper/ # 37 tests

# Simple language tests (BDD framework):
test/                           # Root test folder (Simple .spl tests)
├── __init__.spl                # Root test environment (std.spec.* imports)
├── environment/                # Test runtime orchestration
│   ├── __init__.spl            # Environment configuration
│   ├── bootstrap.spl           # Process-level bootstrap
│   ├── fixtures/               # Test fixtures and data
│   └── helpers/                # Shared test helpers
├── unit/                       # Unit tests (Simple .spl)
│   ├── __init__.spl            # Unit test configuration
│   └── **/*_spec.spl           # Fast isolated tests
├── integration/                # Integration tests (Simple .spl)
│   ├── __init__.spl            # Integration test configuration
│   └── **/*_spec.spl           # Public function tests
└── system/                     # System tests (Simple .spl)
    ├── __init__.spl            # System test configuration
    └── **/*_spec.spl           # Public class/struct tests

# Specialized test levels in tests/ crate (Rust):
tests/
├── unit/           # Additional unit tests with mock policy
│   └── main.rs     # Entry point with #[ctor] init
├── integration/    # Integration tests - mocks only in HAL layers
│   └── main.rs
├── system/         # System tests - no mocks allowed
│   └── main.rs
└── environment/    # Environment tests - HAL/library verification
    └── main.rs
```

## Test Levels

| Level | Mock Policy | Coverage Metric | Coverage Data | Threshold |
|-------|-------------|-----------------|---------------|-----------|
| **Unit** | All mocks allowed | Branch, Condition | Merged (UT+IT+ST+ENV) | 100% |
| **Integration** | HAL-only mocks | Public function touch | Own raw data | 100% |
| **System** | No mocks | Public class/struct touch | Own raw data | 100% |
| **Environment** | HAL/External/Lib mocks | Branch, Condition | Merged into UT | 100% |

### Coverage Data Strategy

```
Coverage Data Flow:
┌─────────────────────────────────────────────────────────────┐
│                    Overall (UT) Coverage                     │
│         (Branch/Condition - merged from all levels)          │
│  ┌─────────┐  ┌─────────┐  ┌─────────┐  ┌─────────┐        │
│  │   UT    │ +│   IT    │ +│   ST    │ +│   ENV   │ = TOTAL │
│  └─────────┘  └─────────┘  └─────────┘  └─────────┘        │
└─────────────────────────────────────────────────────────────┘

Separate Raw Data (for specific coverage metrics):
┌─────────────────────────┐  ┌─────────────────────────┐
│   IT Coverage (Own)     │  │   ST Coverage (Own)     │
│  Public func on class/  │  │  Class/struct method    │
│  struct coverage        │  │  coverage               │
└─────────────────────────┘  └─────────────────────────┘
```

- **Overall/UT Coverage**: Merges all test levels (UT+IT+ST+ENV) for branch/condition metrics
- **IT Coverage**: Keeps its own raw data for public function coverage on class/struct
- **ST Coverage**: Keeps its own raw data for class/struct method coverage
- **ENV Coverage**: Merged into overall UT coverage for branch/condition

### Coverage Policy by Test Level

#### Unit Tests (UT) - 631+ tests
- **Coverage Metrics**: Branch and Condition coverage (100% required)
- **Data Handling**: Overall coverage merges UT+IT+ST+ENV for branch/condition
- **Purpose**: Ensure thorough testing of all code paths, branches, and conditions
- **Threshold**: 100% branch, 100% condition
- **Mock Policy**: All mocks allowed
- **Command**: `make test-unit` or `cargo test --workspace`
- **Coverage**: `make coverage-unit` (overall merged coverage)

#### Integration Tests (IT) - 9 tests
- **Coverage Metrics**: Public function touch (100% required)
- **Data Handling**: **Own raw data** (separate from overall, for public function touch analysis)
- **Purpose**: Verify all public API functions are touched (called at least once)
- **Threshold**: 100% public functions touched
- **Mock Policy**: HAL-only mocks allowed
- **Command**: `make test-integration`
- **Coverage**: `make coverage-integration` (own raw data for public function touch)
- **Location**: `test/integration/` (Simple .spl tests) and `tests/integration/` (Rust tests)

#### System Tests (ST) - 8 tests
- **Coverage Metrics**: Public class/struct touch (100% required)
- **Data Handling**: **Own raw data** (separate from overall, for public class/struct touch analysis)
- **Purpose**: Verify all public classes/structs are touched (instantiated/used at least once)
- **Threshold**: 100% public classes/structs touched
- **Mock Policy**: No mocks allowed (real implementations only)
- **Command**: `make test-system`
- **Coverage**: `make coverage-system` (own raw data for public class/struct touch)
- **Location**: `test/system/` (Simple .spl tests) and `tests/system/` (Rust tests)

#### Environment Tests (env_test) - 7 tests
- **Coverage Metrics**: Branch and Condition coverage (100% required)
- **Data Handling**: Merged into overall UT coverage for branch/condition
- **Purpose**: Test HAL, external libraries, and other lib dependencies
- **Threshold**: 100% branch, 100% condition (merged with UT)
- **Mock Policy**: Can mock HAL, external, and library dependencies
- **Command**: `make test-env`
- **Coverage**: `make coverage-env` (merged into overall)
- **Use Cases**:
  - Verify HAL implementations work correctly
  - Test external library integrations
  - Simulate different environment scenarios (filesystem, network, etc.)
  - Test error handling for external dependencies

## Full Test Mode with Automatic Coverage

Full test mode runs all tests with LLVM coverage instrumentation and automatically generates extended coverage reports.

### Quick Start

```bash
# Run all tests + generate coverage reports (System, Integration, Merged)
make test-full

# Run tests with coverage but skip extended reports
make test-full-quick

# Run full tests + verify coverage thresholds
make test-full-check
```

### Environment Variables

| Variable | Default | Description |
|----------|---------|-------------|
| `SIMPLE_COVERAGE` | `1` | Set to `0` to disable coverage (just run tests) |
| `SIMPLE_COV_THRESHOLD` | `80` | Coverage threshold percentage for pass/fail |

### Generated Reports

Full test mode generates three types of extended coverage reports:

| Report | File | Coverage Metric |
|--------|------|-----------------|
| **System** | `coverage_system.json` | Public class/struct method coverage |
| **Integration** | `coverage_integration.json` | Public function coverage |
| **Merged** | `coverage_merged.json` | All metrics combined |

Reports are written to `target/coverage/extended/`.

### Coverage Tool CLI

The `coverage_gen` tool provides commands for working with coverage data:

```bash
# Generate extended reports from LLVM coverage data
cargo run -p simple_mock_helper --bin coverage_gen -- generate \
    --llvm-cov target/coverage/coverage.json \
    --api public_api.yml \
    --output-dir target/coverage/extended \
    --report-type all  # system, integration, merged, or all

# Check coverage against threshold
cargo run -p simple_mock_helper --bin coverage_gen -- check \
    --coverage target/coverage/extended/coverage_system.json \
    --threshold 80

# Print coverage summary
cargo run -p simple_mock_helper --bin coverage_gen -- summary \
    --coverage target/coverage/extended/coverage_merged.json
```

### Public API Specification

The `public_api.yml` file defines which types and functions are tracked for coverage:

```yaml
# Public functions for Integration test coverage
public_functions:
  simple_driver:
    - Runner::new
    - Runner::run_file
    - Interpreter::run

# Types for System test coverage (class/struct methods)
types:
  simple_driver::Runner:
    methods: [new, run_file, run_source, compile_to_smf]
  simple_parser::Parser:
    methods: [new, parse]
```

## Using simple_mock_helper

### Initialization per Test Binary

Each test binary must initialize its test level once via `#[ctor::ctor]`:

```rust
// tests/unit/main.rs
use ctor::ctor;
use simple_mock_helper::{init_unit_tests, validate_test_config};

#[ctor]
fn init() {
    init_unit_tests!("my_crate_unit");
}

mod my_tests;

#[test]
fn validate_config() {
    validate_test_config().expect_pass();
}
```

```rust
// tests/integration/main.rs
use ctor::ctor;
use simple_mock_helper::{init_integration_tests, validate_test_config};

#[ctor]
fn init() {
    init_integration_tests!("my_crate_integration");
}
```

```rust
// tests/system/main.rs
use ctor::ctor;
use simple_mock_helper::{init_system_tests, validate_test_config};

#[ctor]
fn init() {
    init_system_tests!("my_crate_system");
}
```

### Mock Policy Enforcement

Mocks must call `check_mock_use_from(module_path!())` to enforce the policy:

```rust
pub fn mock_filesystem_read(path: &str) -> Vec<u8> {
    simple_mock_helper::check_mock_use_from(module_path!());
    // Mock implementation...
    vec![]
}
```

### HAL Layer Patterns

Integration tests allow mocks only in HAL layers. Default patterns:
- `*::hal::*` - Hardware abstraction layer
- `*::sub_hal::*` - Sub-HAL components

Custom patterns can be specified:
```rust
init_integration_tests!(patterns: &["*::hal::*", "*::drivers::*"]);
```

## Coverage Integration

### Coverage Data Strategy

Coverage data follows a specific strategy:
- **Overall (UT)**: Merges ALL test levels (UT+IT+ST+ENV) for branch/condition coverage
- **IT**: Keeps **own raw data** for public function coverage analysis
- **ST**: Keeps **own raw data** for class/struct method coverage analysis

```
target/coverage/
├── overall/                   # ALL tests merged (UT+IT+ST+ENV) - branch/condition
│   ├── coverage.json
│   ├── coverage.lcov
│   └── html/
├── integration/               # IT only - own raw data (public function touch)
│   ├── coverage.json
│   └── public_func_touch_report.txt
└── system/                    # ST only - own raw data (public class/struct touch)
    ├── coverage.json
    └── class_touch_report.txt
```

### Generating Coverage Data

**Backend Strategy**: Coverage builds automatically use the **LLVM backend** for:
- Native coverage instrumentation (more accurate than post-build analysis)
- Integration with `cargo llvm-cov` tooling
- Support for all target architectures including 32-bit

```bash
# 1. Overall coverage: ALL tests merged (UT+IT+ST+ENV) for branch/condition
# (Automatically switches to LLVM backend for native instrumentation)
cargo llvm-cov --workspace --branch \
    --json --output-path=target/coverage/overall/coverage.json
cargo llvm-cov --workspace --branch \
    --html --output-dir=target/coverage/overall/html

# 2. Integration tests: Own raw data for public function touch
cargo llvm-cov -p simple-tests --test integration \
    --json --output-path=target/coverage/integration/coverage.json

# 3. System tests: Own raw data for public class/struct touch
cargo llvm-cov -p simple-tests --test system \
    --json --output-path=target/coverage/system/coverage.json

# Or use Makefile targets (backend selection is automatic)
make coverage-unit          # Overall merged (UT+IT+ST+ENV) - branch/condition
make coverage-integration   # IT only - own raw data for public func touch
make coverage-system        # ST only - own raw data for public class/struct touch
make coverage-all           # All reports
```

**Note**: The build system automatically selects the LLVM backend when running coverage commands to ensure accurate instrumentation and analysis.

### Public API Specification

Define public functions for IT coverage in `public_api.yml`:

```yaml
# For Integration Tests: Public functions
public_functions:
  simple_compiler:
    - CompilerPipeline::new
    - CompilerPipeline::compile
  simple_parser:
    - Parser::new
    - Parser::parse
  simple_loader:
    - ModuleLoader::new
    - ModuleLoader::load

# For System Tests: Class/struct methods
types:
  simple_compiler::CompilerPipeline:
    methods: [new, compile, emit, with_options]
  simple_parser::Parser:
    methods: [new, parse, parse_expression, parse_statement]
  simple_loader::ModuleLoader:
    methods: [new, load, entry_point, symbols]
  simple_driver::Runner:
    methods: [new, run_source, run_file, with_gc]
```

### Computing Coverage by Test Level

#### Unit/Environment Coverage (Line, Branch, Condition)

```bash
# Generate merged coverage report
cargo llvm-cov --test unit --test environment --html

# Check thresholds
cargo llvm-cov --test unit --test environment --fail-under-lines 80
cargo llvm-cov --test unit --test environment --fail-under-branches 70
```

#### Integration Coverage (Public Function Touch)

```rust
use simple_mock_helper::{
    load_llvm_cov_export, load_public_api_spec,
    compute_public_func_touch, CoverageSummary,
};

fn check_integration_coverage() -> anyhow::Result<()> {
    let cov = load_llvm_cov_export("target/coverage/integration/coverage.json")?;
    let api = load_public_api_spec("public_api.yml")?;

    let results = compute_public_func_touch(&cov, &api);
    let summary = CoverageSummary::from_results(&results);

    assert!(summary.meets_threshold(100.0),
        "Public function touch {:.1}% < 100%", summary.coverage_percent());
    Ok(())
}
```

#### System Coverage (Public Class/Struct Touch)

```rust
use simple_mock_helper::{
    load_llvm_cov_export, load_public_api_spec,
    compute_class_touch, print_class_touch_table,
    CoverageSummary,
};

fn check_system_coverage() -> anyhow::Result<()> {
    let cov = load_llvm_cov_export("target/coverage/system/coverage.json")?;
    let api = load_public_api_spec("public_api.yml")?;

    let results = compute_class_touch(&cov, &api);
    print_class_touch_table(&results, None);

    let summary = CoverageSummary::from_results(&results);
    assert!(summary.meets_threshold(100.0),
        "Public class/struct touch {:.1}% < 100%", summary.coverage_percent());
    Ok(())
}
```

### Coverage CLI Tool

```bash
# Check merged coverage (UT + environment)
cargo run -p simple_mock_helper --bin smh_coverage -- \
    --coverage target/coverage/merged/coverage.json \
    --type line-branch-condition \
    --line-threshold 80 \
    --branch-threshold 70 \
    --condition-threshold 60

# Check integration coverage (public function touch)
cargo run -p simple_mock_helper --bin smh_coverage -- \
    --coverage target/coverage/integration/coverage.json \
    --api public_api.yml \
    --type public-func-touch \
    --threshold 100

# Check system coverage (public class/struct touch)
cargo run -p simple_mock_helper --bin smh_coverage -- \
    --coverage target/coverage/system/coverage.json \
    --api public_api.yml \
    --type class-struct-touch \
    --threshold 100
```

## Cargo.toml Configuration

```toml
[package]
name = "my_crate"

[dev-dependencies]
simple_mock_helper = { path = "../util/simple_mock_helper" }
ctor = "0.2"
tempfile = "3"

# Define test executables
[[test]]
name = "unit"
path = "tests/unit/main.rs"

[[test]]
name = "integration"
path = "tests/integration/main.rs"

[[test]]
name = "system"
path = "tests/system/main.rs"

[[test]]
name = "environment"
path = "tests/environment/main.rs"
```

## Running Tests

```bash
# Run all tests
cargo test --workspace

# Run specific test level
cargo test --test unit
cargo test --test integration
cargo test --test system
cargo test --test environment

# Run with coverage
cargo llvm-cov --workspace --test unit --test integration
```

## System Tests

### Tooling
- Use `shadow-terminal` for headless CLI testing
- Use `tempfile` for isolated test directories
- Use the `Runner` from `src/driver` for end-to-end coverage

### CLI Test Example

```rust
#[test]
fn cli_compile_and_run() -> shadow_terminal::Result<()> {
    let tmp = tempfile::tempdir()?;
    let src = tmp.path().join("main.spl");
    std::fs::write(&src, "main = 42")?;

    let mut term = shadow_terminal::Command::new([
        "cargo", "run", "-p", "simple-driver", "--", "run",
        src.to_str().unwrap(),
    ])
    .rows(24)
    .cols(80)
    .spawn()?;

    term.wait_for_exit_success()?;
    assert!(src.with_extension("smf").exists());
    Ok(())
}
```

### GC Logging Tests

```rust
#[test]
fn gc_logging_enabled() {
    let runner = Runner::new_with_gc_logging();
    let result = runner.run_source("main = 0").unwrap();
    // GC markers should be emitted
}
```

### System Test Scenarios

- **CLI watch mode**: Start `watch <src>` under `shadow-terminal`, mutate the source, assert rebuild and `.smf` mtime bump
- **Diagnostics**: Feed invalid source, expect non-zero exit and error message
- **Dependency invalidation**: `main.spl` imports `util.spl`; touching `util.spl` triggers rebuild
- **Macro tracking**: Change macro body, dependents rebuild

## Environment Tests

Environment tests verify HAL, external libraries, and other dependencies work correctly. They can mock these dependencies to simulate various scenarios.

```rust
// tests/environment/main.rs
use ctor::ctor;
use simple_mock_helper::{init_env_tests, validate_test_config};

#[ctor]
fn init() {
    // environment can mock HAL, external libs, and other library dependencies
    init_env_tests!("environment");
}

mod hal_tests;          // Test HAL implementations
mod external_lib_tests; // Test external library integrations
mod filesystem_tests;   // Test filesystem operations (real or mocked)
mod network_tests;      // Test network operations (real or mocked)

#[test]
fn validate_config() {
    validate_test_config().expect_pass();
}
```

> Note: Skipping the `init_*_tests!()` macro in any test binary (including system tests) will cause `validate_test_config()` to fail, ensuring the mock policy and test level are always initialized.

### Mock Patterns for Environment Tests

Environment tests allow mocking of:
- `*::hal::*` - Hardware abstraction layer
- `*::external::*` - External library wrappers
- `*::lib::*` - Internal library dependencies
- `*::io::*` - I/O operations

```rust
// Custom patterns for env_test
init_env_tests!(patterns: &[
    "*::hal::*",
    "*::external::*",
    "*::lib::*",
    "*::io::*",
]);
```

### HAL/External Mock Examples

```rust
// Mock HAL for testing error scenarios
#[test]
fn test_hal_error_handling() {
    // Mock filesystem to simulate disk full error
    mock_hal::filesystem::set_error(IoError::DiskFull);

    let result = my_module::save_data("test.txt", &data);
    assert!(matches!(result, Err(SaveError::StorageFull)));
}

// Mock external library behavior
#[test]
fn test_external_lib_timeout() {
    // Mock network library to simulate timeout
    mock_external::http::set_timeout(Duration::from_millis(1));

    let result = api_client::fetch_data();
    assert!(matches!(result, Err(ApiError::Timeout)));
}

// Test with real HAL (no mocking)
#[test]
fn verify_real_filesystem() {
    let tmp = tempfile::tempdir().unwrap();
    let path = tmp.path().join("test.txt");

    std::fs::write(&path, b"hello").unwrap();
    let data = std::fs::read(&path).unwrap();
    assert_eq!(data, b"hello");
}
```

## Best Practices

1. **Initialize once**: Call `init_*_tests!()` exactly once per test binary
2. **Validate config**: Include a `validate_test_config()` test in each binary
3. **Use module paths**: Always pass `module_path!()` to mock checkers
4. **Keep tests fast**: Use tempdirs, avoid network, minimize I/O
5. **Assert specifically**: Check exact values, not just "no error"
6. **Separate coverage concerns**:
   - UT/env_test → line/branch/condition (merged)
   - IT → public function coverage (separate)
   - System → class/struct coverage (separate)

## Coverage Thresholds

| Test Level | Metric | Threshold |
|------------|--------|-----------|
| Unit + environment | Line | 80% |
| Unit + environment | Branch | 70% |
| Unit + environment | Condition | 60% |
| Integration | Public function touch | 100% |
| System | Public class/struct touch | 100% |

## Makefile Targets

```makefile
# Test execution
test:                   # Run all tests
test-unit:              # Run unit tests only
test-integration:       # Run integration tests only
test-system:            # Run system tests only
test-environment:       # Run environment tests only

# Coverage generation (separated by policy)
coverage-merged:        # UT + environment → line/branch/condition
coverage-integration:   # Integration only → public function touch
coverage-system:        # System only → public class/struct touch
coverage-all:           # Generate all three coverage reports

# Coverage verification
coverage-check:              # Verify all coverage thresholds
coverage-check-merged:       # Check UT + environment thresholds
coverage-check-integration:  # Check integration public func touch threshold
coverage-check-system:       # Check system class touch threshold

# Reports
coverage-html:          # Generate HTML report (merged only)
coverage-report:        # Print summary of all coverage types
```

## CI/CD Integration

### Coverage Check Pipeline

```yaml
# .github/workflows/coverage.yml
coverage:
  steps:
    # 1. Run tests and generate coverage
    - name: Generate merged coverage (UT + environment)
      run: |
        cargo llvm-cov --test unit --test environment \
          --json --output-path=target/coverage/merged/coverage.json

    - name: Generate integration coverage
      run: |
        cargo llvm-cov --test integration \
          --json --output-path=target/coverage/integration/coverage.json

    - name: Generate system coverage
      run: |
        cargo llvm-cov --test system \
          --json --output-path=target/coverage/system/coverage.json

    # 2. Check thresholds
    - name: Check merged coverage thresholds
      run: |
        cargo run -p simple_mock_helper --bin smh_coverage -- \
          --coverage target/coverage/merged/coverage.json \
          --type line-branch-condition \
          --line-threshold 80 --branch-threshold 70 --condition-threshold 60

    - name: Check integration public function touch
      run: |
        cargo run -p simple_mock_helper --bin smh_coverage -- \
          --coverage target/coverage/integration/coverage.json \
          --api public_api.yml --type public-func-touch --threshold 100

    - name: Check system class/struct touch
      run: |
        cargo run -p simple_mock_helper --bin smh_coverage -- \
          --coverage target/coverage/system/coverage.json \
          --api public_api.yml --type class-struct-touch --threshold 100
```

### Coverage Report Summary

The CI should output a summary like:

```
=== Coverage Report ===

Merged (UT + environment):
  Line:      82.5% (target: 80%) ✓
  Branch:    71.2% (target: 70%) ✓
  Condition: 63.8% (target: 60%) ✓

Integration (public function touch):
  Touch:     100.0% (target: 100%) ✓

System (public class/struct touch):
  Touch:     100.0% (target: 100%) ✓

All coverage thresholds met!
```

## GC/Abfall Hooks

- Runtime GC (`simple_runtime::gc::GcRuntime`) wraps Abfall, emitting structured `GcLogEvent` markers
- In system tests, use `Runner::with_gc(GcRuntime::with_logger(...))` for in-memory assertions
- Use `Runner::new_with_gc_logging()` or CLI `--gc-log` to surface logs to stdout

---

## See Also

- `doc/system_test.md` - System test framework guide (SDN config, BDD patterns)
- `doc/spec/testing/testing_bdd_framework.md` - BDD spec framework specification (describe/context/it)
- `doc/spec/sdn.md` - SDN (Simple Data Notation) format specification
