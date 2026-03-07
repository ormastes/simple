# Coverage Guide

Source code coverage and documentation coverage tools for the Simple language.

---

## Table of Contents

1. [Source Coverage](#source-coverage)
2. [Coverage Types](#coverage-types)
3. [Interpreter Coverage](#interpreter-coverage)
4. [Compiled Coverage](#compiled-coverage)
5. [Coverage API](#coverage-api)
6. [SDN Report Format](#sdn-report-format)
7. [Documentation Coverage](#documentation-coverage)
8. [SDoctest Enforcement](#sdoctest-enforcement)
9. [CI/CD Integration](#cicd-integration)
10. [Troubleshooting](#troubleshooting)

---

## Source Coverage

Simple provides built-in coverage tracking that measures how thoroughly tests exercise source code. Coverage is available for both interpreter and compiled execution modes.

### Coverage Types

| Type | Description | Interpreter | Compiled |
|------|-------------|-------------|----------|
| **Line** | Which statements were executed | Yes | Yes |
| **Function** | Which functions were called | Yes | Yes |
| **Decision** | Whether boolean expressions evaluated to both true and false | Yes | Yes |
| **Condition** | Individual conditions in compound booleans (`&&`, `||`) | Yes | Yes |

### Quick Start

```bash
# Interpreter coverage
SIMPLE_COVERAGE=1 simple my_script.spl

# Compiled coverage
simple compile src/main.spl --coverage

# Run tests with coverage
SIMPLE_COVERAGE=1 cargo test simple_stdlib
```

---

## Interpreter Coverage

Enable coverage by setting the `SIMPLE_COVERAGE=1` environment variable.

When enabled:
- Coverage data is collected in memory during execution
- Data persists throughout the program lifetime
- Access via `coverage.get_coverage_sdn()` or `coverage.save_coverage_data()`
- Data is NOT automatically saved to a file

Override the output location:

```bash
SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT=/tmp/my_coverage.json cargo test
```

### Decision Coverage

Tracks whether boolean decisions (if/while/match) evaluate to both true and false:

```simple
fn check_positive(n: i32) -> bool:
    if n > 0:
        return true
    else:
        return false

# For full decision coverage, call with both positive and negative values
check_positive(5)     # true branch
check_positive(-5)    # false branch
```

### Condition Coverage

Tracks individual operands in compound boolean expressions:

```simple
fn validate(age: i32, score: i32) -> bool:
    if (age >= 18) && (score > 50):  # Two conditions tracked separately
        return true
    else:
        return false

# Full condition coverage requires all combinations:
validate(20, 60)    # age: true,  score: true
validate(20, 40)    # age: true,  score: false
validate(15, 60)    # age: false, score: true
validate(15, 40)    # age: false, score: false
```

---

## Compiled Coverage

Enable coverage instrumentation at compile time:

```bash
simple compile src/main.spl --coverage
simple compile src/main.spl --coverage-output=my_coverage.sdn
```

The compiler inserts probes at:
- **Decision points**: `if`, `while`, `assert`, `assume`, compound boolean results
- **Condition points**: Individual operands in `&&` and `||` expressions
- **Path points**: Function entry (tracks which functions are executed)

---

## Coverage API

```simple
import std.tooling.coverage as coverage

# Check if coverage is available
if coverage.is_coverage_enabled():
    coverage.clear_coverage()

    # ... run code or tests ...

    # Get coverage as SDN string
    val sdn_report = coverage.get_coverage_sdn()
    print sdn_report

    # Or save to file (.coverage/coverage.sdn by default)
    coverage.save_coverage_data(quiet: false)
```

### API Reference

| Function | Description |
|----------|-------------|
| `is_coverage_enabled() -> bool` | Check if coverage tracking is available |
| `clear_coverage()` | Reset all accumulated coverage data |
| `get_coverage_sdn() -> text` | Get current coverage as SDN string |
| `save_coverage_data(quiet: bool)` | Save to file, optionally print summary |

---

## SDN Report Format

```sdn
version: 1.0

decisions |id, file, line, column, true_count, false_count|
    1, src/math.spl, 10, 5, 42, 17

conditions |decision_id, condition_id, file, line, column, true_count, false_count|
    1, 1, src/math.spl, 10, 5, 42, 17
    1, 2, src/math.spl, 10, 15, 35, 24

paths |path_id, blocks, hit_count|
    1, [0 1 2], 100

summary:
    total_decisions: 2
    covered_decisions: 2
    decision_percent: 100.0
    condition_percent: 100.0
    path_percent: 100.0
```

A decision is "covered" when both true and false branches have been executed. A condition is "covered" when both true and false evaluations have occurred.

---

## Documentation Coverage

The Simple compiler tracks documentation coverage for public APIs.

### Quick Start

```bash
# View doc coverage in stats
bin/simple stats

# JSON output for tooling
bin/simple stats --json

# Extract specific metrics
bin/simple stats --json | jq .documentation.coverage_percent

# Run SDoctest examples
bin/simple test --sdoctest
```

### Documentation Types

**1. Public API Documentation** -- Docstrings for public functions, classes, structs, enums:

```simple
fn parse_config(path: text) -> Config:
    """
    Parse configuration file and return Config struct.

    Args:
        path: Path to configuration file (SDN format)

    Returns:
        Parsed Config struct with validated settings

    @tag:api
    """
```

**2. SDoctest Examples** -- Executable code examples in docstrings:

```simple
fn factorial(n: i64) -> i64:
    """
    Compute factorial of n.

    Examples:
        ```simple
        val result = factorial(5)
        expect(result).to_equal(120)
        ```

    @tag:api
    """
    if n == 0: return 1
    n * factorial(n - 1)
```

**3. Inline Comments** -- For complex expressions (>3 operators, >2 chained calls, deep nesting).

**4. Group Comments** -- Related variables grouped with a comment header:

```simple
# Parser state tracking
var current_token: Token = nil
var peek_token: Token = nil
var token_index = 0
```

### Tag System

| Tag | Purpose |
|-----|---------|
| `@tag:api` | Public API (stable) |
| `@tag:internal` | Internal implementation |
| `@tag:experimental` | Experimental features |
| `@tag:deprecated` | Deprecated code |
| `@tag:critical` | Critical path |
| `@tag:perf` | Performance-sensitive |

### Coverage Thresholds

Configure in `doc_coverage.sdn`:

```sdn
{
  "thresholds": {
    "global": 80,
    "by_tag": {
      "api": 100,
      "critical": 95,
      "experimental": 50
    }
  },
  "exit_on_failure": true
}
```

### Report Formats

| Format | Command | Use Case |
|--------|---------|----------|
| Terminal | `bin/simple stats` | CLI usage |
| JSON | `bin/simple stats --json` | Tooling, CI/CD |
| Markdown | `bin/simple doc-coverage --format=md` | Documentation (planned) |
| CSV | `bin/simple doc-coverage --format=csv` | Spreadsheets (planned) |

---

## SDoctest Enforcement

### Rules for Public APIs

- **Grouped items** (under a comment header) -- at least ONE SDoctest for the group
- **Non-grouped items** -- EACH item needs its own SDoctest

### Grouped Example

```simple
# File operations
#   - file_read
#   - file_write
#   - file_exists
```

One example covering any function in the group satisfies coverage:

```simple
use std.io.{file_read}
val content = file_read("example.txt")
print content
```

### Non-grouped Example

```simple
# Public API:
#   - sqrt
#   - pow
#   - abs
```

Each function needs its own separate SDoctest example.

### Best Practices

- Group related functions to reduce documentation burden
- Write minimal, focused examples
- Place examples in README.md (high-level) or `doc/guide/*.md` (detailed)

---

## CI/CD Integration

### Source Coverage in CI

```bash
# Run tests with coverage
SIMPLE_COVERAGE=1 simple test

# Check threshold
simple coverage check --threshold 80
```

### Documentation Coverage in CI

```bash
# Check doc coverage
bin/simple stats --json > stats.json
COVERAGE=$(jq -r '.documentation.coverage_percent' stats.json)
if [ "$COVERAGE" -lt 80 ]; then
    echo "Documentation coverage below 80%: ${COVERAGE}%"
    exit 1
fi
```

### GitHub Actions Example

```yaml
- name: Check documentation coverage
  run: |
    bin/simple stats --json > coverage.json

- name: Enforce thresholds
  run: |
    COVERAGE=$(jq -r '.documentation.coverage_percent' coverage.json)
    echo "Documentation coverage: ${COVERAGE}%"
    [ "$COVERAGE" -ge 80 ] || exit 1
```

---

## Troubleshooting

### Source coverage always shows 0

Ensure `SIMPLE_COVERAGE=1` is set before running:

```bash
export SIMPLE_COVERAGE=1
cargo test
```

### Coverage data missing after clear

Get coverage data BEFORE clearing:

```simple
val sdn = coverage.get_coverage_sdn()  # Has data
coverage.clear_coverage()              # Now clear
```

### Function not counted as documented

- Docstring must be first line after function declaration
- Must use `"""` triple-quotes
- No blank lines between declaration and docstring

```simple
# Wrong:
fn my_function():

    """This is a docstring"""

# Correct:
fn my_function():
    """This is a docstring"""
```

### SDoctest examples not detected

Must use proper fence syntax with `simple` language tag:

```simple
"""
Examples:
    ```simple
    val result = my_function(5)
    expect(result).to_equal(10)
    ```
"""
```

### Rust vs Simple coverage

All `cargo llvm-cov` metrics apply to Rust code only. Simple source coverage uses its own instrumentation system via MIR probes and the `SIMPLE_COVERAGE` environment variable.
