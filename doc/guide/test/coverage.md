# Simple Source Coverage Guide

This guide explains how to use the Simple source coverage feature to measure test coverage of your Simple code.

## Overview

Simple provides built-in coverage tracking that measures:

- **Decision Coverage**: Whether boolean expressions have been evaluated to both `true` and `false`
- **Condition Coverage**: Individual conditions within compound boolean expressions (`&&`, `||`)
- **Path Coverage**: Execution paths through functions (function entry tracking)

Coverage data is collected at runtime and can be exported in SDN (Simple Data Notation) format.

## Interpreter Coverage

Simple now provides coverage tracking for code running in the interpreter mode, enabling coverage measurement for interpreter-executed tests.

### Enabling Interpreter Coverage

To enable coverage for interpreter execution, set the `SIMPLE_COVERAGE=1` environment variable:

```bash
# Run interpreter with coverage enabled
SIMPLE_COVERAGE=1 simple my_script.spl

# Run tests with coverage
SIMPLE_COVERAGE=1 cargo test simple_stdlib

# Run specific test with coverage
SIMPLE_COVERAGE=1 cargo test --test interpreter_coverage_line
```

### Supported Coverage Types

| Type | Interpreter | Compiled |
|------|-------------|----------|
| **Line Coverage** | ✅ | ✅ |
| **Function Coverage** | ✅ | ✅ |
| **Decision Coverage** | ✅ | ✅ |
| **Condition Coverage** | ✅ | ✅ |

### Coverage Data Collection

When `SIMPLE_COVERAGE=1` is set:
- Coverage data is **collected in memory** during interpreter execution
- Data persists throughout the program lifetime
- Data is accessible via the Simple API (`coverage.get_coverage_sdn()`, etc.)
- Data is **not automatically saved** to a file (use `coverage.save_coverage_data()` to save)

For test frameworks, coverage data is typically accessed programmatically before test completion.

### Line Coverage

Line coverage tracks which statements have been executed during interpreter execution. Every statement (assignments, declarations, control flow) is recorded when executed.

```simple
# Example: Both lines will be tracked
val x = 10
val y = 20
print x + y
```

### Decision Coverage

Decision coverage tracks whether boolean decisions (if/while/match statements) have evaluated to both true and false outcomes.

```simple
# Decision: if statement condition
fn check_positive(n: i32) -> bool:
    if n > 0:
        return true
    else:
        return false

# For full decision coverage, call with both positive and negative values
check_positive(5)    # true branch
check_positive(-5)   # false branch
```

### Condition Coverage

Condition coverage tracks individual operands in compound boolean expressions (`&&` and `||`).

```simple
# Condition coverage: Tracks both operands independently
fn validate(age: i32, score: i32) -> bool:
    if (age >= 18) && (score > 50):  # Two conditions tracked separately
        return true
    else:
        return false

# For full condition coverage, test cases should evaluate all combinations:
validate(20, 60)    # age >= 18: true,  score > 50: true
validate(20, 40)    # age >= 18: true,  score > 50: false
validate(15, 60)    # age >= 18: false, score > 50: true
validate(15, 40)    # age >= 18: false, score > 50: false
```

For compound expressions with `||` (OR):

```simple
fn can_proceed(has_token: bool, is_admin: bool) -> bool:
    if has_token || is_admin:       # Two conditions tracked separately
        return true
    else:
        return false

# Full coverage requires testing both branches of both conditions
can_proceed(true, false)   # has_token: true,  is_admin: false
can_proceed(false, true)   # has_token: false, is_admin: true
can_proceed(false, false)  # has_token: false, is_admin: false
```

**Note**: Even with short-circuit evaluation, both operands are recorded for coverage:
- `(false) && (anything)` → left = false, right = not evaluated but recorded
- `(true) || (anything)` → left = true, right = not evaluated but recorded

### Function Coverage

Function coverage tracks which user-defined functions and methods have been called during execution.

```simple
fn helper() -> i32:
    return 42

fn main() -> i32:
    return helper()

# Running main() will record a call to helper()
```

### Environment Variable: SIMPLE_COVERAGE

When `SIMPLE_COVERAGE=1` is set:

1. Coverage collection is enabled in the runtime
2. Coverage data is accumulated during execution
3. Coverage data can be saved to a JSON file
4. Default output location: `target/coverage/simple_coverage.json`

Override the output location with `SIMPLE_COVERAGE_OUTPUT`:

```bash
SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT=/tmp/my_coverage.json cargo test
```

## Compilation with Coverage

To enable coverage instrumentation, use the `--coverage` flag when compiling:

```bash
# Compile with coverage enabled
simple compile src/main.spl --coverage

# Compile with custom coverage output path
simple compile src/main.spl --coverage-output=my_coverage.sdn
```

The `--coverage` flag inserts coverage probes at decision points during compilation.

## Quick Start

### For Interpreter Execution

```bash
# Enable coverage via environment variable
export SIMPLE_COVERAGE=1

# Run your code
simple my_script.spl

# Or run tests
cargo test my_test_suite
```

### Programmatic Coverage Access

```simple
import std.tooling.coverage as coverage

# Check if coverage is available
if coverage.is_coverage_enabled():
    # Clear any previous data
    coverage.clear_coverage()

    # ... run your code or tests ...

    # Get coverage data as SDN format
    val sdn_report = coverage.get_coverage_sdn()
    print sdn_report

    # Or save to file with summary
    coverage.save_coverage_data(quiet: false)
```

## API Reference

### `is_coverage_enabled() -> bool`

Check if coverage tracking is available in the runtime.

```simple
if coverage.is_coverage_enabled():
    print "Coverage tracking is available"
```

Returns `true` when the Simple runtime is linked with coverage support (which is the default).

### `clear_coverage()`

Reset all accumulated coverage data.

```simple
coverage.clear_coverage()
```

Call this before running tests to ensure clean coverage data.

### `get_coverage_sdn() -> text`

Get the current coverage data as an SDN-formatted string.

```simple
val sdn = coverage.get_coverage_sdn()
print sdn
```

Returns the complete coverage report including decisions, conditions, paths, and summary statistics.

### `save_coverage_data(quiet: bool)`

Save coverage data to a file and optionally print a summary.

```simple
# Save with summary output
coverage.save_coverage_data(quiet: false)

# Save silently
coverage.save_coverage_data(quiet: true)
```

The default output path is `.coverage/coverage.sdn`. The function:
1. Creates the output directory if needed
2. Writes the SDN coverage report
3. Prints a summary (unless `quiet: true`)

## SDN Format

Coverage data is exported in SDN (Simple Data Notation) format:

```sdn
# Coverage Report
version: 1.0

decisions |id, file, line, column, true_count, false_count|
    1, src/math.spl, 10, 5, 42, 17
    2, src/math.spl, 15, 8, 30, 30

conditions |decision_id, condition_id, file, line, column, true_count, false_count|
    1, 1, src/math.spl, 10, 5, 42, 17
    1, 2, src/math.spl, 10, 15, 35, 24

paths |path_id, blocks, hit_count|
    1, [0 1 2], 100
    1, [0 1 3], 50

summary:
    total_decisions: 2
    covered_decisions: 2
    total_conditions: 2
    covered_conditions: 2
    total_paths: 2
    covered_paths: 2
    decision_percent: 100.0
    condition_percent: 100.0
    path_percent: 100.0
```

### Format Details

| Section | Description |
|---------|-------------|
| `decisions` | Each decision point (if, while, etc.) with true/false counts |
| `conditions` | Individual conditions in compound expressions (a && b) |
| `paths` | Execution paths through code blocks |
| `summary` | Aggregate statistics and percentages |

### Coverage Metrics

- **Covered Decision**: Both true and false branches have been executed
- **Covered Condition**: Both true and false evaluations have occurred
- **Covered Path**: The path has been executed at least once

## Usage Patterns

### Test Suite Coverage

```simple
import std.spec
import std.tooling.coverage as coverage

# At the start of test suite
coverage.clear_coverage()

# Run tests...
describe "My Module":
    it "does something":
        val result = my_function()
        expect(result).to(eq(expected))

# At the end of test suite
coverage.save_coverage_data(quiet: false)
```

### Programmatic Coverage Analysis

```simple
import std.tooling.coverage as coverage

fn run_coverage_analysis():
    coverage.clear_coverage()

    # Run code under test
    val results = run_all_tests()

    # Get coverage data
    val sdn = coverage.get_coverage_sdn()

    # Parse and analyze
    if sdn.contains("decision_percent: 100"):
        print "Full decision coverage achieved!"
    else:
        print "Coverage gaps exist"
        # Analyze sdn for details

    sdn
```

### CI/CD Integration

```simple
import std.tooling.coverage as coverage

fn main():
    coverage.clear_coverage()

    val test_passed = run_test_suite()

    # Always save coverage, even if tests fail
    coverage.save_coverage_data(quiet: true)

    if not test_passed:
        exit(1)

    # Check coverage threshold
    val sdn = coverage.get_coverage_sdn()
    if not meets_threshold(sdn, 80.0):
        print "Coverage below 80% threshold"
        exit(1)

    exit(0)
```

## How Coverage Works

### Compile-Time Instrumentation

When Simple code is compiled with coverage enabled (`--coverage` flag), the compiler inserts probes at:

1. **Decision Points**:
   - `if` statement conditions
   - `while` loop conditions
   - `assert` statement conditions
   - `assume` statement conditions
   - Compound boolean expressions (`&&`, `||`) result

2. **Condition Points**:
   - Individual operands in `&&` expressions (left and right)
   - Individual operands in `||` expressions (left and right)

3. **Path Points**:
   - Function entry (tracks which functions are executed)

**Note**: For loops and match expressions are not yet instrumented (requires iterator protocol and match in native codegen respectively).

### Runtime Collection

During execution:
1. Each probe records its outcome (true/false for decisions/conditions)
2. Path probes record block sequences
3. Data is stored in thread-safe global storage

### Export

When you call `get_coverage_sdn()` or `save_coverage_data()`:
1. Coverage data is serialized to SDN format
2. Statistics are calculated
3. The report is returned/saved

## Best Practices

### 1. Clear Before Each Test Run

```simple
before_each:
    coverage.clear_coverage()
```

This ensures each test starts with clean coverage data.

### 2. Test Both Branches

For full coverage, ensure each decision evaluates to both true and false:

```simple
# Good: Tests both branches
it "handles positive numbers":
    expect(classify(5)).to(eq("positive"))

it "handles negative numbers":
    expect(classify(-5)).to(eq("negative"))
```

### 3. Check Coverage in CI

Include coverage checks in your CI pipeline:

```bash
simple test --coverage
simple coverage check --threshold 80
```

### 4. Use Coverage Gaps to Find Missing Tests

If coverage shows a branch is never taken, add a test for that case:

```simple
# If "x < 0" branch is uncovered:
it "handles edge case with negative input":
    val result = process(-1)
    expect(result).to(eq(expected_for_negative))
```

## Verification

### Verifying Coverage is Working

1. **Run with coverage enabled**:
   ```bash
   SIMPLE_COVERAGE=1 cargo test --test interpreter_coverage_line
   ```

2. **Expected output**: All tests should pass
   ```
   test result: ok. 9 passed; 0 failed
   ```

3. **Verify coverage collection**: The test `test_line_coverage_basic` verifies that:
   - Coverage is enabled
   - Coverage data is being collected
   - Line count is greater than 0

### Manual Verification

Create a test script to check coverage is working:

```bash
# Create test script
cat > test_cov.spl << 'EOF'
fn add(a: i32, b: i32) -> i32:
    return a + b

fn check(n: i32) -> bool:
    if n > 0:
        return true
    else:
        return false

main = add(5, 3)
EOF

# Run with coverage enabled
SIMPLE_COVERAGE=1 simple test_cov.spl

# The functions add() and check() would be in coverage data
# (check() not called, so only add() would be recorded)
```

## Troubleshooting

### Coverage Always Shows 0

**Cause**: Coverage environment variable not set or coverage not enabled.

**Solution**: Ensure `SIMPLE_COVERAGE=1` is set before running:
```bash
export SIMPLE_COVERAGE=1
cargo test
```

### Coverage Data Missing After Clear

**Cause**: `clear_coverage()` was called after running tests but before getting coverage.

**Solution**: Get coverage data before clearing:

```simple
# Wrong order
coverage.clear_coverage()
val sdn = coverage.get_coverage_sdn()  # Empty!

# Correct order
val sdn = coverage.get_coverage_sdn()  # Has data
coverage.clear_coverage()              # Now clear
```

### File Save Fails

**Cause**: Directory doesn't exist or no write permission.

**Solution**: The module automatically creates the `.coverage` directory, but ensure you have write permissions to the current directory.

### Coverage Works But No JSON File Created

**Cause**: Auto-save is not enabled for interpreter coverage.

**Solution**: Coverage data must be saved explicitly via `coverage.save_coverage_data()` or accessed via `coverage.get_coverage_sdn()`. This is the expected behavior - coverage is collected in memory during execution.

## Related Documentation

- [SSpec Testing Framework](./sspec.md) - Writing tests with SSpec
- [Test Runner Guide](./test_runner.md) - Running tests with coverage
- [SDN Format Reference](./sdn_format.md) - SDN data format specification

## Implementation Notes

The coverage system is implemented in:

### Compiled Code Coverage
- **Rust Runtime**: `src/rust/runtime/src/coverage.rs` - Core coverage data structures and FFI
- **MIR Lowering**: `src/rust/compiler/src/mir/lower/lowering_coverage.rs` - Coverage probe insertion
- **MIR Instructions**: `DecisionProbe`, `ConditionProbe`, `PathProbe` in `src/rust/compiler/src/mir/inst_enum.rs`
- **CLI**: `--coverage` and `--coverage-output=` flags in compile command

### Interpreter Coverage
- **Coverage Helpers**: `src/rust/compiler/src/interpreter/coverage_helpers.rs` - Location extraction and decision recording
- **Node Execution**: `src/rust/compiler/src/interpreter/node_exec.rs:24` - Line coverage hook in `exec_node()`
- **Control Flow**: `src/rust/compiler/src/interpreter_control.rs` - Decision coverage hooks in `exec_if()`, `exec_while()`, `exec_match_core()`
- **Function Calls**: `src/rust/compiler/src/interpreter_call/core/function_exec.rs:221` - Function coverage already implemented
- **Coverage Collector**: `src/rust/compiler/src/coverage/collector.rs` - Runtime coverage collection for interpreter mode
- **Simple Module**: `src/lib/std/src/tooling/coverage.spl` - Simple API for coverage control

### Coverage Probes

| Probe Type | Purpose | Inserted At |
|------------|---------|-------------|
| `DecisionProbe` | Track decision true/false | if, while, assert, assume, && / \|\| result |
| `ConditionProbe` | Track condition true/false | && / \|\| operands |
| `PathProbe` | Track execution paths | Function entry |

### Tests

- **Runtime Tests**: `cargo test --package simple-compiler coverage` (12 tests)
- **MIR Lowering Tests**: `cargo test --package simple-compiler coverage_tests` (8 tests)
- **SSpec Tests**: `src/lib/std/test/unit/tooling/coverage_ffi_spec.spl`
