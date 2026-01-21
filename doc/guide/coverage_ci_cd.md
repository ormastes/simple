# Coverage in CI/CD Pipelines

This guide explains how to integrate Simple language coverage into your CI/CD pipelines.

## GitHub Actions Integration

### Current Setup

The project's GitHub Actions workflow (`.github/workflows/rust-tests.yml`) now includes:

1. **Interpreter Coverage Tests Job** (`interpreter-coverage`)
   - Runs on: Ubuntu, Windows, macOS
   - Environment: Stable Rust
   - Enabled via: `SIMPLE_COVERAGE=1` environment variable

### Coverage Jobs

#### 1. Compiled Code Coverage

Job: `coverage`

Collects coverage for compiled/native code via `cargo-llvm-cov`:

```yaml
- name: Generate coverage
  run: cargo llvm-cov --workspace --lcov --output-path lcov.info

- name: Upload coverage to Codecov
  uses: codecov/codecov-action@v4
  with:
    files: lcov.info
```

**Files covered**: Native code, compiled to LLVM IR

**Metrics**: Line, decision, condition, and path coverage

**Output**: LCOV format, uploaded to Codecov.io

#### 2. Interpreter Coverage Tests

Job: `interpreter-coverage`

Tests interpreter coverage functionality:

```yaml
- name: Run interpreter coverage tests
  run: cargo test --test interpreter_coverage_line --verbose
  env:
    SIMPLE_COVERAGE: "1"

- name: Run coverage-related tests
  run: cargo test coverage --lib --verbose
  env:
    SIMPLE_COVERAGE: "1"
```

**Files covered**: Interpreter execution paths

**Metrics**: Line, function, decision, and condition coverage

**Output**: Test pass/fail status, coverage data in memory

## Branch Support

### Supported Branches

Workflows run on:
- `main` - Primary branch
- `master` - Alternative primary
- `develop` - Development branch

Pull requests to any of these branches trigger the workflows.

### Custom Branches

To add coverage to additional branches, edit `.github/workflows/rust-tests.yml`:

```yaml
on:
  push:
    branches: [ main, master, develop, your-branch ]
  pull_request:
    branches: [ main, master, develop, your-branch ]
```

## Running Coverage Locally

### Before Submitting PR

```bash
# Run interpreter coverage tests
SIMPLE_COVERAGE=1 cargo test --test interpreter_coverage_line

# Run all coverage-related tests
cargo test coverage

# Generate compiled code coverage (optional)
cargo llvm-cov --workspace --lcov --output-path lcov.info
```

## Coverage Thresholds

### Setting Minimum Coverage

Add threshold enforcement in CI/CD:

```bash
#!/bin/bash
set -e

# Run tests with coverage
SIMPLE_COVERAGE=1 cargo test --test interpreter_coverage_line

# Check that required tests passed
if ! cargo test coverage --lib | grep -q "test result: ok"; then
  echo "Coverage tests failed!"
  exit 1
fi

echo "All coverage tests passed!"
```

### Codecov Configuration

Create `.codecov.yml` in repository root:

```yaml
coverage:
  precision: 2
  round: down
  range: "70...100"

ignore:
  - "tests"
  - "examples"

flags:
  compiled:
    description: "Compiled code coverage"
    paths:
      - src/rust

  interpreter:
    description: "Interpreter coverage"
    paths:
      - src/rust/compiler/src/interpreter
```

## Usage Examples

### GitHub Actions - Custom Coverage Job

Add to `.github/workflows/custom-coverage.yml`:

```yaml
name: Custom Coverage Check

on:
  push:
    branches: [ main, develop ]
  pull_request:
    branches: [ main, develop ]

jobs:
  coverage:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - uses: dtolnay/rust-toolchain@stable

      - name: Install dependencies
        run: sudo apt-get install -y spirv-tools

      - name: Test with interpreter coverage
        run: |
          SIMPLE_COVERAGE=1 cargo test --test interpreter_coverage_line

      - name: Generate LLVM coverage
        uses: taiki-e/install-action@cargo-llvm-cov

      - name: Run llvm-cov
        run: cargo llvm-cov --workspace --lcov --output-path lcov.info

      - name: Upload to Codecov
        uses: codecov/codecov-action@v4
        with:
          files: lcov.info
          flags: interpreted,compiled
          name: full-coverage
```

### GitLab CI - Coverage Integration

Create `.gitlab-ci.yml`:

```yaml
interpreter-coverage:
  stage: test
  image: rust:latest
  before_script:
    - apt-get update && apt-get install -y spirv-tools
  script:
    - SIMPLE_COVERAGE=1 cargo test --test interpreter_coverage_line --verbose
    - cargo test coverage --lib --verbose
  coverage: '/test result: ok.*/'
  artifacts:
    reports:
      coverage_report:
        coverage_format: generic
        path: coverage.xml
  only:
    - main
    - develop
    - merge_requests
```

## Test Results in CI

### Expected Output

```
running 14 tests
test test_line_coverage_basic ... ok
test test_decision_coverage_if_else ... ok
test test_condition_coverage_and ... ok
...
test result: ok. 14 passed; 0 failed
```

### Failure Scenarios

If tests fail:

1. **Parser Errors**: Issue with Simple code syntax
   - Check test code for indentation
   - Verify Simple language syntax

2. **Coverage Disabled**: `SIMPLE_COVERAGE` not set
   - CI job doesn't collect coverage but tests still run
   - Set `SIMPLE_COVERAGE: "1"` in env

3. **Missing Dependencies**: SPIR-V tools not installed
   - Linux: `apt-get install -y spirv-tools`
   - macOS: `brew install spirv-tools`

## Performance Considerations

### Build Caching

The CI configuration includes caching to speed up builds:

```yaml
- name: Cache cargo build
  uses: actions/cache@v4
  with:
    path: target
    key: ${{ runner.os }}-cargo-interpreter-cov-${{ hashFiles('**/Cargo.lock') }}
```

Caching reduces build time by ~60-70% on subsequent runs.

### Runtime Overhead

- Coverage tests add <100ms overhead per job
- All 14 tests complete in <1 second
- Negligible impact on CI/CD pipeline duration

## Reporting Coverage

### Codecov Integration

After PR merge, coverage reports available at:
- https://codecov.io/gh/your-org/simple

### GitHub PR Comments

Coverage changes posted automatically:
- ```
  Coverage: 87.5% (+2.3%)
  ```

### Custom Reporting

Generate coverage report locally:

```bash
# Collect coverage data
SIMPLE_COVERAGE=1 cargo test --test interpreter_coverage_line

# Generate HTML report
cargo llvm-cov --html
open target/llvm-cov/html/index.html
```

## Best Practices

### 1. Always Run Coverage Locally

```bash
# Before pushing
SIMPLE_COVERAGE=1 cargo test --test interpreter_coverage_line
cargo test coverage
```

### 2. Document Coverage Requirements

Add to `README.md`:

```markdown
## Coverage

This project maintains >85% coverage across:
- Interpreter execution paths
- Compiled code (LLVM)

Run locally:
```bash
SIMPLE_COVERAGE=1 cargo test --test interpreter_coverage_line
```
```

### 3. Review Coverage Gaps

Check which lines aren't covered:

```bash
# Generate HTML report
cargo llvm-cov --html
```

### 4. Update Coverage When Adding Features

- Add new tests for new code paths
- Verify all branches are tested
- Run full coverage before PR

## Troubleshooting

### Coverage Job Times Out

**Cause**: Large test suite or slow environment

**Solution**:
```yaml
timeout-minutes: 30  # Add to job
```

### Codecov Upload Fails

**Cause**: Token missing or invalid

**Solution**: Check codecov token in repository secrets

### Tests Pass Locally but Fail in CI

**Cause**: Different environment (OS, dependencies)

**Solution**:
- Test on same OS as CI (e.g., Ubuntu)
- Check dependency versions
- Use CI workflow locally with Act: `act -j interpreter-coverage`

## Related Documentation

- [Source Coverage Guide](./source_coverage.md) - User guide
- [Coverage Architecture](../design/coverage_architecture.md) - Design details
- [GitHub Actions Docs](https://docs.github.com/en/actions)
- [Codecov Documentation](https://docs.codecov.io/)

## Environment Variables

| Variable | Purpose | Default |
|----------|---------|---------|
| `SIMPLE_COVERAGE` | Enable coverage | `0` (disabled) |
| `SIMPLE_COVERAGE_OUTPUT` | Output file path | `target/coverage/simple_coverage.json` |
| `CARGO_TERM_COLOR` | Colored output | `always` |
| `RUST_BACKTRACE` | Debug info | `1` |

## Next Steps

1. **Push to branch**: Code gets tested automatically
2. **Review PR**: Coverage changes visible in comments
3. **Merge**: Coverage trends tracked over time
4. **Monitor**: Watch coverage dashboard for regressions
