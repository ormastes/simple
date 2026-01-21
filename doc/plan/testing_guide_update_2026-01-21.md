# Testing Guide Update Plan

**Date**: 2026-01-21
**Status**: Planning
**Goal**: Update `doc/guide/test.md` to reflect new directory structure and testing infrastructure

---

## Overview

This plan updates the testing documentation to align with:
1. **Directory restructure** (`directory_restructure_migration_2026-01-21.md`)
2. **Testing roadmap** (`testing_roadmap_2026.md`)
3. New testing features being implemented

**Target Document**: `doc/guide/test.md` (currently 750 lines)

---

## Changes Required

### 1. Directory Path Updates

#### Current References → New References

| Current Path | New Path | Occurrences |
|--------------|----------|-------------|
| `tests/unit/` | `test/rust/unit/` | ~10 |
| `tests/integration/` | `test/rust/integration/` | ~8 |
| `tests/system/` | `test/rust/system/` | ~8 |
| `tests/environment/` | `test/rust/environment/` | ~7 |
| `simple/test/` | `test/` | ~5 |
| `simple/std_lib/test/` | `test/lib/std/` | ~6 |
| `src/parser/tests/` | `src/rust/parser/tests/` | ~3 |
| `src/compiler/tests/` | `src/rust/compiler/tests/` | ~3 |

**Total Estimated Changes**: ~50 path references

---

### 2. Directory Structure Diagram Update

**Current** (lines 10-54):
```
# Rust unit tests in each crate (631+ tests total):
src/parser/       # 115 tests
src/compiler/     # 79 tests
...

# Simple language tests (BDD framework):
test/                           # Root test folder
├── __init__.spl
├── environment/
├── unit/
├── integration/
└── system/

# Specialized test levels in tests/ crate (Rust):
tests/
├── unit/
├── integration/
├── system/
└── environment/
```

**New Structure** (from migration plan):
```
# Rust compiler source (with inline tests):
src/rust/
├── parser/           # 115 tests (50 inline + 65 in tests/)
├── compiler/         # 79 tests (57 inline + 22 in tests/)
├── type/             # 68 tests
├── driver/           # 216 tests
├── runtime/          # 19 tests
└── util/
    └── simple_mock_helper/  # 37 tests

# Test directory (all test types):
test/
├── rust/                      # Rust test harness
│   ├── unit/main.rs          # 631+ tests
│   ├── integration/main.rs   # 9 tests
│   ├── system/main.rs        # 8 tests
│   ├── environment/main.rs   # 7 tests
│   ├── contract/             # Contract tests (new)
│   └── deployment/           # Deployment tests (new)
├── unit/                      # Simple language unit tests
│   ├── __init__.spl
│   └── **/*_spec.spl
├── integration/               # Simple language integration
│   ├── __init__.spl
│   └── **/*_spec.spl
├── system/                    # Simple language system
│   ├── __init__.spl
│   └── **/*_spec.spl
├── lib/                       # Library tests
│   └── std/                   # Standard library tests
│       ├── unit/
│       ├── integration/
│       ├── system/
│       └── fixtures/
├── app/                       # Application tests
│   ├── formatter/
│   ├── linter/
│   └── vscode_extension/
├── fixtures/                  # Shared test data
│   ├── rust/
│   ├── simple/
│   ├── smf/
│   └── data/
├── mock/                      # Mock infrastructure
│   └── simple/                # Simple language mock library
│       ├── lib.spl
│       ├── stub.spl
│       ├── mock.spl
│       └── verify.spl
└── environment/               # Test orchestration
    ├── __init__.spl
    ├── bootstrap.spl
    └── helpers/

# Benchmarks (new):
bench/
├── Cargo.toml
├── parser_bench.rs
├── compiler_bench.rs
└── runtime_bench.rs

# Fuzzing (new):
fuzz/
├── Cargo.toml
└── fuzz_targets/
    ├── parser.rs
    ├── hir_lowering.rs
    └── mir_generation.rs
```

---

### 3. New Sections to Add

#### 3.1 Mock Library for Simple Language

**Location**: After "Mock Policy Enforcement" section (line 259)

```markdown
## Mock Library for Simple Language

Simple language tests can use the native mock library located in `test/mock/simple/`.

### Basic Usage

\`\`\`simple
# test/unit/user_service_spec.spl
import spec.mock.*

describe "UserService":
    context "when creating user":
        it "saves to database":
            # Create mock
            val db_mock = Mock.of<Database>("Database")

            # Configure stub
            db_mock.when("save")
                .with_args([User.new("Alice")])
                .returns(123)

            # Execute code under test
            val service = UserService.new(db_mock)
            val user_id = service.create_user("Alice")

            # Assertions
            expect(user_id).to(eq(123))

            # Verify calls
            db_mock.verify("save")
                .called_once()
                .with_args([User.new("Alice")])
\`\`\`

### Stub API

\`\`\`simple
mock.when("method_name")
    .with_args([arg1, arg2])     # Match specific arguments
    .returns(value)              # Return value
    .throws(error)               # Throw error
    .calls(\args: compute(args)) # Custom callback
\`\`\`

### Verification API

\`\`\`simple
mock.verify("method_name")
    .called()                    # Called at least once
    .called_once()               # Called exactly once
    .called_times(n)             # Called exactly n times
    .never_called()              # Never called
    .with_args([arg1, arg2])     # With specific arguments
\`\`\`

### Mock Policy Enforcement

The mock library integrates with the test level system:

| Test Level | Mock Policy | Library Available |
|------------|-------------|-------------------|
| Unit       | All mocks allowed | ✅ Yes |
| Integration| HAL-only mocks | ⚠️  Limited (HAL mocks only) |
| System     | No mocks | ❌ No (import fails) |
| Environment| HAL/External/Lib | ✅ Yes |

Attempting to import the mock library in system tests will fail:

\`\`\`simple
# test/system/end_to_end_spec.spl
import spec.mock.*  # ERROR: Mock not allowed in system tests

# This will trigger a compilation error at test discovery time
\`\`\`

See `testing_roadmap_2026.md` Phase 1.1 for implementation details.
```

---

#### 3.2 Contract Testing

**Location**: New section after "Environment Tests" (line 622)

```markdown
## Contract Testing

Contract tests verify that API contracts between modules/services are maintained.

### Directory Structure

\`\`\`
test/rust/contract/
├── main.rs                    # Contract test harness
├── parser_contract_tests.rs   # Parser public API contracts
├── compiler_contract_tests.rs # Compiler contracts
└── runtime_contract_tests.rs  # Runtime contracts
\`\`\`

### Contract Test Example

\`\`\`rust
// test/rust/contract/parser_contract_tests.rs
use simple_parser::Parser;

#[test]
fn parser_api_contract() {
    // Consumer expectation: Parser::new() returns a Parser
    let parser = Parser::new();

    // Consumer expectation: Parser::parse() accepts &str
    let result = parser.parse("val x = 42");

    // Contract: parse() returns Result<Ast, ParseError>
    assert!(result.is_ok());

    // Contract: AST has expected structure
    let ast = result.unwrap();
    assert_eq!(ast.statements.len(), 1);
}
\`\`\`

### Simple Language Contract Tests

\`\`\`simple
# test/contract/api_contract_spec.spl
import spec.contract.*

describe "UserService API Contract":
    it "provides user by ID":
        val contract = PactBuilder.new()
            .given("user 123 exists")
            .upon_receiving("request for user 123")
            .with_request("GET", "/users/123", nil)
            .will_respond_with(200, {id: 123, name: "Alice"})
            .build()

        expect(contract.verify()).to(be_successful)
\`\`\`

### Running Contract Tests

\`\`\`bash
# Rust contract tests
cargo test -p simple-tests --test contract

# Simple contract tests
make test-contract

# Makefile target
make test-contract
\`\`\`

See `testing_roadmap_2026.md` Phase 1.3 for implementation details.
```

---

#### 3.3 Deployment Testing

**Location**: After "Contract Testing" section

```markdown
## Deployment Testing

Deployment tests verify that the compiled compiler/runtime work correctly when deployed.

### Directory Structure

\`\`\`
test/rust/deployment/
├── main.rs              # Deployment test harness
├── smoke_tests.rs       # Basic smoke tests
└── linkage_tests.rs     # Binary linkage tests
\`\`\`

### Smoke Test Example

\`\`\`rust
// test/rust/deployment/smoke_tests.rs
use std::process::Command;

#[test]
fn binary_executes_successfully() {
    let output = Command::new("bin/rust/simple")
        .arg("--version")
        .output()
        .expect("Failed to execute binary");

    assert!(output.status.success());
    assert!(String::from_utf8_lossy(&output.stdout).contains("simple"));
}

#[test]
fn compile_and_run_hello_world() {
    let tmp = tempfile::tempdir().unwrap();
    let src = tmp.path().join("hello.spl");
    std::fs::write(&src, r#"
        fn main():
            print "Hello, World!"
    "#).unwrap();

    // Compile
    let compile = Command::new("bin/rust/simple")
        .arg("compile")
        .arg(&src)
        .output()
        .expect("Failed to compile");
    assert!(compile.status.success());

    // Run
    let run = Command::new("bin/rust/simple")
        .arg("run")
        .arg(&src)
        .output()
        .expect("Failed to run");
    assert!(run.status.success());
    assert!(String::from_utf8_lossy(&run.stdout).contains("Hello, World!"));
}
\`\`\`

### Simple Language Deployment Tests

\`\`\`simple
# test/deployment/smoke_spec.spl
import spec.deployment.*

describe "Production Deployment":
    context "Critical Services":
        it "compiler binary responds to --version":
            val check = ServiceHealthCheck.new("simple --version")
            expect(check.execute()).to(be_successful)

        it "can compile and run simple programs":
            val suite = DeploymentSuite.new(
                Environment.Production,
                [
                    CompileCheck.new("fixtures/hello.spl"),
                    RuntimeCheck.new("fixtures/hello.spl", "Hello, World!")
                ]
            )
            val report = suite.run()
            expect(report.all_passed()).to(be_true)
\`\`\`

### Running Deployment Tests

\`\`\`bash
# Run deployment smoke tests
cargo test -p simple-tests --test deployment

# Makefile target
make test-deployment
\`\`\`

See `testing_roadmap_2026.md` Phase 1.2 for implementation details.
```

---

#### 3.4 Benchmarking

**Location**: New section after "Deployment Testing"

```markdown
## Benchmarking

Benchmarks measure performance of critical compiler components.

### Directory Structure

\`\`\`
bench/
├── Cargo.toml
├── parser_bench.rs      # Parser benchmarks
├── compiler_bench.rs    # Compiler pipeline benchmarks
├── runtime_bench.rs     # Runtime benchmarks
└── fixtures/            # Benchmark input files
    ├── small.spl
    ├── medium.spl
    └── large.spl
\`\`\`

### Benchmark Example

\`\`\`rust
// bench/parser_bench.rs
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use simple_parser::Parser;

fn bench_parse_small(c: &mut Criterion) {
    let source = std::fs::read_to_string("bench/fixtures/small.spl").unwrap();
    c.bench_function("parse_small_file", |b| {
        b.iter(|| {
            let parser = Parser::new();
            parser.parse(black_box(&source))
        })
    });
}

fn bench_parse_large(c: &mut Criterion) {
    let source = std::fs::read_to_string("bench/fixtures/large.spl").unwrap();
    c.bench_function("parse_large_file", |b| {
        b.iter(|| {
            let parser = Parser::new();
            parser.parse(black_box(&source))
        })
    });
}

criterion_group!(benches, bench_parse_small, bench_parse_large);
criterion_main!(benches);
\`\`\`

### Running Benchmarks

\`\`\`bash
# Run all benchmarks
cargo bench --workspace

# Run specific benchmark
cargo bench --bench parser_bench

# Makefile target
make bench

# With baseline comparison
cargo bench --bench parser_bench -- --save-baseline main
# After changes:
cargo bench --bench parser_bench -- --baseline main
\`\`\`

### CI Integration

Benchmarks run nightly in CI to detect performance regressions:

\`\`\`yaml
# .github/workflows/benchmarks.yml
name: Benchmarks
on:
  schedule:
    - cron: '0 2 * * *'  # Nightly at 2 AM
jobs:
  benchmark:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - name: Run benchmarks
        run: cargo bench --workspace
      - name: Upload results
        uses: actions/upload-artifact@v3
        with:
          name: benchmark-results
          path: target/criterion/
\`\`\`

See `testing_roadmap_2026.md` Phase 2.3 for implementation details.
```

---

#### 3.5 Fuzzing

**Location**: After "Benchmarking" section

```markdown
## Fuzzing

Fuzzing tests compiler robustness by feeding randomized inputs.

### Directory Structure

\`\`\`
fuzz/
├── Cargo.toml
├── fuzz_targets/
│   ├── parser.rs           # Fuzz parser with arbitrary source
│   ├── hir_lowering.rs     # Fuzz HIR lowering
│   ├── mir_generation.rs   # Fuzz MIR generation
│   └── codegen.rs          # Fuzz code generation
└── corpus/                 # Seed inputs
    ├── parser/
    │   ├── valid_programs/
    │   └── edge_cases/
    └── hir_lowering/
\`\`\`

### Fuzz Target Example

\`\`\`rust
// fuzz/fuzz_targets/parser.rs
#![no_main]
use libfuzzer_sys::fuzz_target;
use simple_parser::Parser;

fuzz_target!(|data: &[u8]| {
    // Convert bytes to string
    if let Ok(source) = std::str::from_utf8(data) {
        let parser = Parser::new();

        // Parser should never panic, even on invalid input
        let _ = parser.parse(source);
    }
});
\`\`\`

### Running Fuzzing

\`\`\`bash
# Install cargo-fuzz
cargo install cargo-fuzz

# Run specific fuzzer (1 hour)
cargo fuzz run parser -- -max_total_time=3600

# Run all fuzzers
for target in fuzz/fuzz_targets/*.rs; do
    name=$(basename "$target" .rs)
    cargo fuzz run "$name" -- -max_total_time=3600
done

# Minimize corpus
cargo fuzz cmin parser

# View crashes
ls fuzz/artifacts/parser/
\`\`\`

### CI Integration

Fuzzing runs nightly to catch crashes:

\`\`\`yaml
# .github/workflows/fuzz.yml
name: Fuzzing
on:
  schedule:
    - cron: '0 2 * * *'  # Nightly
jobs:
  fuzz:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - name: Install cargo-fuzz
        run: cargo install cargo-fuzz
      - name: Run fuzzers
        run: |
          cargo fuzz run parser -- -max_total_time=3600
          cargo fuzz run hir_lowering -- -max_total_time=3600
      - name: Upload crashes
        if: failure()
        uses: actions/upload-artifact@v3
        with:
          name: fuzz-crashes
          path: fuzz/artifacts/
\`\`\`

See `testing_roadmap_2026.md` Phase 3.2 for implementation details.
```

---

#### 3.6 Coverage for Simple Source

**Location**: Update "Coverage Integration" section (lines 282-336)

**Add subsection**:

```markdown
### Simple Language Coverage

Coverage for Simple language source files (`.spl`) is tracked separately from Rust coverage.

#### How It Works

1. **MIR Instrumentation**: Coverage probes inserted at MIR level during compilation
2. **Runtime Collection**: Probes emit coverage events during test execution
3. **LCOV Export**: Coverage data exported in LCOV format
4. **HTML Reports**: Merged with Rust coverage for unified view

#### Generating Simple Coverage

\`\`\`bash
# Enable Simple coverage collection
export SIMPLE_SOURCE_COVERAGE=1

# Run tests with coverage
make test

# Generate report
make coverage-simple

# View HTML report
open target/coverage/simple/html/index.html
\`\`\`

#### Coverage Output

\`\`\`
target/coverage/
├── rust/                  # Rust coverage (cargo llvm-cov)
│   ├── coverage.json
│   └── html/
├── simple/                # Simple source coverage (NEW)
│   ├── coverage.lcov
│   └── html/
└── merged/                # Combined Rust + Simple coverage
    ├── coverage.json
    └── html/
\`\`\`

#### Example Coverage Report

\`\`\`
=== Simple Language Coverage ===

src/lib/std/string.spl:
  Lines:    142/150 (94.7%)
  Branches: 28/32 (87.5%)

src/lib/std/array.spl:
  Lines:    98/98 (100.0%)
  Branches: 24/24 (100.0%)

Total Simple Coverage:
  Lines:    240/248 (96.8%)
  Branches: 52/56 (92.9%)
\`\`\`

See `testing_roadmap_2026.md` Phase 2.2 for implementation details.
```

---

### 4. Updated Makefile Targets Section

**Location**: Replace "Makefile Targets" section (lines 645-670)

```markdown
## Makefile Targets

### Test Execution

\`\`\`makefile
# Run all tests
make test

# Run specific test levels
make test-unit              # Rust unit tests
make test-integration       # Rust integration tests
make test-system            # Rust system tests
make test-environment       # Rust environment tests
make test-contract          # Contract tests (new)
make test-deployment        # Deployment smoke tests (new)

# Run Simple language tests
make test-simple-unit       # Simple unit tests
make test-simple-integration # Simple integration tests
make test-simple-system     # Simple system tests

# Run application tests
make test-app-formatter     # Formatter tests
make test-app-linter        # Linter tests
make test-app-vscode        # VSCode extension tests
\`\`\`

### Coverage Generation

\`\`\`makefile
# Overall coverage (all test levels merged)
make coverage               # Generate all coverage reports
make coverage-html          # HTML report only
make coverage-merged        # UT + IT + ST + ENV merged

# Per-level coverage (own raw data)
make coverage-unit          # Unit test branch/condition
make coverage-integration   # Integration public function touch
make coverage-system        # System class/struct touch
make coverage-environment   # Environment branch/condition

# Simple language coverage (new)
make coverage-simple        # Simple source file coverage
make coverage-simple-html   # Simple coverage HTML report

# Extended reports
make coverage-extended-all  # All extended reports
make coverage-check         # Verify all thresholds
\`\`\`

### Benchmarking (new)

\`\`\`makefile
# Run benchmarks
make bench                  # All benchmarks
make bench-parser           # Parser benchmarks only
make bench-compiler         # Compiler benchmarks only
make bench-runtime          # Runtime benchmarks only

# Benchmark with baseline
make bench-baseline         # Save current as baseline
make bench-compare          # Compare to baseline
\`\`\`

### Fuzzing (new)

\`\`\`makefile
# Run fuzzers
make fuzz                   # All fuzzers (1 hour each)
make fuzz-parser            # Parser fuzzer only
make fuzz-hir               # HIR lowering fuzzer
make fuzz-mir               # MIR generation fuzzer

# Corpus management
make fuzz-cmin              # Minimize corpus
make fuzz-clean             # Clean artifacts
\`\`\`

### Quality Checks

\`\`\`makefile
# Pre-commit checks
make check                  # fmt + lint + test
make check-full             # + coverage + duplication

# Individual checks
make fmt                    # Format code
make fmt-check              # Check formatting
make lint                   # Run clippy
make test                   # Run all tests
make arch-test              # Architecture compliance tests
\`\`\`
```

---

### 5. CI/CD Integration Updates

**Location**: Update "CI/CD Integration" section (lines 672-736)

**Add new jobs**:

```markdown
### GitHub Actions Workflows

#### Main Test Workflow

\`\`\`yaml
# .github/workflows/rust-tests.yml
name: Rust Tests
on: [push, pull_request]
jobs:
  test:
    strategy:
      matrix:
        os: [ubuntu-latest, macos-latest, windows-latest]
        rust: [stable, nightly]
    runs-on: ${{ matrix.os }}
    steps:
      - uses: actions/checkout@v4
      - name: Setup Rust
        uses: dtolnay/rust-toolchain@master
        with:
          toolchain: ${{ matrix.rust }}
      - name: Run tests
        run: cargo test --workspace
      - name: Run coverage
        if: matrix.os == 'ubuntu-latest' && matrix.rust == 'stable'
        run: make coverage
      - name: Upload to Codecov
        if: matrix.os == 'ubuntu-latest' && matrix.rust == 'stable'
        uses: codecov/codecov-action@v3
        with:
          files: target/coverage/merged/coverage.lcov
\`\`\`

#### Contract Tests Workflow (new)

\`\`\`yaml
# .github/workflows/contract-tests.yml
name: Contract Tests
on: [push, pull_request]
jobs:
  contract:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - name: Run contract tests
        run: cargo test -p simple-tests --test contract
\`\`\`

#### Deployment Tests Workflow (new)

\`\`\`yaml
# .github/workflows/deployment-tests.yml
name: Deployment Tests
on:
  push:
    branches: [main]
  pull_request:
jobs:
  deployment:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - name: Build binaries
        run: cargo build --release
      - name: Link binaries
        run: make link-bins
      - name: Run smoke tests
        run: cargo test -p simple-tests --test deployment
\`\`\`

#### Benchmarks Workflow (new)

\`\`\`yaml
# .github/workflows/benchmarks.yml
name: Benchmarks
on:
  schedule:
    - cron: '0 2 * * *'  # Nightly
  workflow_dispatch:
jobs:
  benchmark:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - name: Run benchmarks
        run: cargo bench --workspace
      - name: Upload results
        uses: actions/upload-artifact@v3
        with:
          name: benchmark-results
          path: target/criterion/
\`\`\`

#### Fuzzing Workflow (new)

\`\`\`yaml
# .github/workflows/fuzz.yml
name: Fuzzing
on:
  schedule:
    - cron: '0 2 * * *'  # Nightly
jobs:
  fuzz:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - name: Install cargo-fuzz
        run: cargo install cargo-fuzz
      - name: Run fuzzers
        run: |
          cargo fuzz run parser -- -max_total_time=3600
          cargo fuzz run hir_lowering -- -max_total_time=3600
      - name: Upload crashes
        if: failure()
        uses: actions/upload-artifact@v3
        with:
          name: fuzz-crashes
          path: fuzz/artifacts/
\`\`\`
```

---

### 6. Coverage Thresholds Table Update

**Location**: Replace table at line 637

```markdown
## Coverage Thresholds

| Test Level | Metric | Data Source | Threshold | Notes |
|------------|--------|-------------|-----------|-------|
| **Rust Coverage** |
| Unit + Environment | Line | Merged (all levels) | 80% | Overall coverage |
| Unit + Environment | Branch | Merged (all levels) | 70% | Overall coverage |
| Unit + Environment | Condition | Merged (all levels) | 60% | Overall coverage |
| Integration | Public function touch | Own raw data | 100% | All public APIs called |
| System | Class/struct touch | Own raw data | 100% | All public types used |
| **Simple Coverage** (new) |
| Simple Source | Line | MIR instrumentation | 80% | `.spl` file coverage |
| Simple Source | Branch | MIR instrumentation | 70% | `.spl` branch coverage |
| **Quality Metrics** (new) |
| Mutation Testing | Mutation score | cargo-mutants | 80% | Test suite quality |
| Fuzzing | Crash count | cargo-fuzz | 0 | No crashes in 24h |
```

---

### 7. Best Practices Updates

**Location**: Update "Best Practices" section (line 623)

**Add**:

```markdown
## Best Practices

### General

1. **Initialize once**: Call `init_*_tests!()` exactly once per test binary
2. **Validate config**: Include a `validate_test_config()` test in each binary
3. **Use module paths**: Always pass `module_path!()` to mock checkers
4. **Keep tests fast**: Use tempdirs, avoid network, minimize I/O
5. **Assert specifically**: Check exact values, not just "no error"

### Mock Usage

6. **Mock at boundaries**: Only mock external dependencies (DB, network, HAL)
7. **Verify behavior**: Always verify mocks were called as expected
8. **Stub return values**: Provide realistic return values, not just `nil`
9. **Respect test level**: Don't bypass mock policy enforcement

### Coverage

10. **Separate coverage concerns**:
    - UT/Environment → line/branch/condition (merged)
    - Integration → public function touch (own data)
    - System → class/struct touch (own data)
    - Simple source → line/branch (MIR instrumentation)
11. **Track coverage trends**: Monitor coverage over time in CI
12. **Don't game coverage**: Write meaningful tests, not just coverage boosters

### Performance

13. **Benchmark critical paths**: Parser, compiler, runtime hot loops
14. **Detect regressions**: Compare benchmarks to baseline
15. **Profile before optimizing**: Use benchmarks to guide optimization

### Quality

16. **Fuzz robustness-critical code**: Parser, compiler, runtime
17. **Minimize corpus**: Keep fuzz corpus small and diverse
18. **Mutation test your tests**: Validate test suite quality
19. **Contract test APIs**: Prevent breaking changes to public APIs
```

---

## Implementation Steps

### Step 1: Pre-Migration Snapshot
**Duration**: 5 minutes

```bash
# Create backup
cp doc/guide/test.md doc/guide/test.md.backup

# Verify current document
wc -l doc/guide/test.md
# Should be ~750 lines
```

---

### Step 2: Path Updates (Automated)
**Duration**: 15 minutes

Create script `scripts/update-test-guide-paths.sh`:

```bash
#!/bin/bash
set -e

FILE="doc/guide/test.md"

# Create backup
cp "$FILE" "$FILE.tmp"

# Update paths
sed -i 's|tests/unit/|test/rust/unit/|g' "$FILE"
sed -i 's|tests/integration/|test/rust/integration/|g' "$FILE"
sed -i 's|tests/system/|test/rust/system/|g' "$FILE"
sed -i 's|tests/environment/|test/rust/environment/|g' "$FILE"
sed -i 's|simple/test/|test/|g' "$FILE"
sed -i 's|simple/std_lib/test/|test/lib/std/|g' "$FILE"
sed -i 's|src/parser/|src/rust/parser/|g' "$FILE"
sed -i 's|src/compiler/|src/rust/compiler/|g' "$FILE"
sed -i 's|src/type/|src/rust/type/|g' "$FILE"
sed -i 's|src/driver/|src/rust/driver/|g' "$FILE"
sed -i 's|src/runtime/|src/rust/runtime/|g' "$FILE"
sed -i 's|src/common/|src/rust/common/|g' "$FILE"
sed -i 's|src/loader/|src/rust/loader/|g' "$FILE"
sed -i 's|src/util/|src/rust/util/|g' "$FILE"

echo "Path updates complete!"
```

**Run**:
```bash
chmod +x scripts/update-test-guide-paths.sh
./scripts/update-test-guide-paths.sh
```

**Verify**:
```bash
# Check changes
git diff doc/guide/test.md | grep "^-" | grep "tests/"
git diff doc/guide/test.md | grep "^+" | grep "test/"
```

---

### Step 3: Directory Structure Update
**Duration**: 20 minutes

**Manual edit** of lines 10-54:
1. Open `doc/guide/test.md`
2. Replace directory structure diagram with new structure (from section 2 above)
3. Update test count comments if changed
4. Verify formatting

---

### Step 4: Add New Sections
**Duration**: 1 hour

Add sections in order:
1. Mock Library for Simple Language (after line 259)
2. Contract Testing (after line 622)
3. Deployment Testing (after Contract Testing)
4. Benchmarking (after Deployment Testing)
5. Fuzzing (after Benchmarking)
6. Simple Language Coverage (update lines 282-336)

**Process**:
- Copy content from section 3 above
- Adjust line numbers as document grows
- Maintain consistent formatting
- Update cross-references

---

### Step 5: Update Tables and Lists
**Duration**: 30 minutes

1. Replace Makefile Targets section (lines 645-670)
2. Update CI/CD Integration section (lines 672-736)
3. Replace Coverage Thresholds table (line 637)
4. Update Best Practices list (line 623)

---

### Step 6: Add Cross-References
**Duration**: 15 minutes

Add references to new planning documents:

At end of document (before "See Also"):

```markdown
## Related Documentation

- `directory_restructure_migration_2026-01-21.md` - Directory migration plan
- `testing_roadmap_2026.md` - Testing infrastructure roadmap
- `testing_guide_update_2026-01-21.md` - This update plan
- `doc/guide/directory_structure.md` - Directory structure reference
```

---

### Step 7: Validation
**Duration**: 30 minutes

```bash
# 1. Check document length
wc -l doc/guide/test.md
# Expected: ~1200-1400 lines (was 750, added ~500)

# 2. Verify markdown formatting
npx markdownlint doc/guide/test.md

# 3. Check internal links
grep -n "](#" doc/guide/test.md
# Verify all anchors exist

# 4. Verify code blocks
grep -c '```' doc/guide/test.md
# Should be even number

# 5. Check path references
grep -E "(tests/|simple/test/|simple/std_lib/test/)" doc/guide/test.md
# Should return NO matches (all updated to new paths)

grep -E "(test/rust/|test/lib/std/)" doc/guide/test.md
# Should return MANY matches
```

---

### Step 8: Review and Commit
**Duration**: 15 minutes

```bash
# Review changes
git diff doc/guide/test.md | less

# Stage changes
git add doc/guide/test.md

# Commit
git commit -m "docs: update test guide for new directory structure

- Update all path references (tests/ → test/rust/, etc.)
- Add Mock Library for Simple Language section
- Add Contract Testing section
- Add Deployment Testing section
- Add Benchmarking section
- Add Fuzzing section
- Add Simple Language Coverage section
- Update Makefile targets
- Update CI/CD workflows
- Update coverage thresholds
- Update best practices

Related: directory_restructure_migration_2026-01-21.md, testing_roadmap_2026.md"
```

---

## Timeline

| Step | Duration | Cumulative |
|------|----------|------------|
| 1. Pre-migration snapshot | 5 min | 5 min |
| 2. Path updates (automated) | 15 min | 20 min |
| 3. Directory structure update | 20 min | 40 min |
| 4. Add new sections | 60 min | 1h 40m |
| 5. Update tables/lists | 30 min | 2h 10m |
| 6. Add cross-references | 15 min | 2h 25m |
| 7. Validation | 30 min | 2h 55m |
| 8. Review and commit | 15 min | 3h 10m |
| **Total** | **~3 hours** | |

---

## Dependencies

### Must Complete Before Starting
1. ✅ Directory restructure migration plan finalized
2. ✅ Testing roadmap finalized
3. ⚠️  Decide if updating before or after actual migration

### Coordination with Other Tasks
- If **before migration**: Document shows future state, add note at top
- If **after migration**: Update as part of Phase 5 (Final Cleanup)

**Recommendation**: Update **after Phase 2** (test directory migration) but **before Phase 5** (final cleanup).

---

## Rollback Plan

If issues found after update:

```bash
# Restore backup
cp doc/guide/test.md.backup doc/guide/test.md

# Or revert commit
git revert <commit-hash>
```

---

## Success Criteria

- [ ] All path references updated to new structure
- [ ] Directory structure diagram matches migration plan
- [ ] All new sections added (Mock lib, Contract, Deployment, Bench, Fuzz)
- [ ] Makefile targets updated
- [ ] CI/CD workflows documented
- [ ] Coverage thresholds updated
- [ ] No broken internal links
- [ ] Markdown linting passes
- [ ] Document length ~1200-1400 lines
- [ ] Cross-references to related docs added

---

## Notes

### Timing with Migration

**Option A: Update Before Migration**
- Pros: Documentation ready when migration starts
- Cons: Docs describe non-existent structure, confusing
- Add banner: "⚠️ Note: This document describes the directory structure after the migration planned for [date]. See `directory_restructure_migration_2026-01-21.md` for current status."

**Option B: Update After Migration**
- Pros: Docs match reality
- Cons: Outdated docs during migration
- Add to migration Phase 5 (step 5.1)

**Option C: Update During Migration (Recommended)**
- After Phase 2 (test directory migration complete)
- Before Phase 5 (final cleanup)
- Test directories already moved, can document accurately
- Source directories still to be moved (document future state with note)

### Future Maintenance

After this update, maintain by:
1. Adding new test types to appropriate sections
2. Updating coverage thresholds as needed
3. Documenting new Makefile targets
4. Keeping CI/CD workflows in sync
5. Adding examples for new testing patterns

---

**Status**: Ready for execution
**Execution Window**: After Phase 2 of directory restructure migration
**Estimated Completion**: 3 hours of focused work
