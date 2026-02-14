# Documentation Coverage User Guide

**Complete guide to using Simple's documentation coverage tools.**

---

## Overview

The Simple compiler provides comprehensive documentation coverage tracking to help maintain high-quality, well-documented code. The system tracks multiple types of documentation:

- **Public API documentation** - Docstrings for public functions, classes, structs, enums
- **SDoctest examples** - Executable code examples in docstrings
- **Inline comments** - Comments for complex expressions and logic
- **Group comments** - Documentation for related variable clusters
- **Tag classification** - Categorize documentation with `@tag:name`

### Current Implementation Status

**Working:**
- ✅ `bin/simple stats` - Shows documentation coverage metrics
- ✅ `bin/simple stats --json` - JSON output for tooling
- ✅ Coverage tracking infrastructure (scanner, analysis, types)
- ✅ SDoctest integration (`bin/simple test --sdoctest`)

**In Development:**
- 🔧 `bin/simple build --warn-docs` - Needs field name fix
- 🔧 `bin/simple doc-coverage` - Needs field name fix
- 🔧 Report formatting (JSON/CSV/Markdown) - Planned

**Workaround:** Use `bin/simple stats` for all coverage metrics until the commands are fixed.

---

## Quick Start

> **Note:** The `doc-coverage` command is currently under development. Use `bin/simple stats` for coverage metrics until the command is fully operational.

### View Coverage Statistics

```bash
# Show doc coverage in stats output
bin/simple stats

# JSON format (for tooling integration)
bin/simple stats --json

# Extract specific metrics with jq
bin/simple stats --json | jq .documentation.coverage_percent
```

### Check Documentation During Build

> **Status:** The `--warn-docs` flag exists but needs a minor bug fix (field name issue). Use `bin/simple stats` for now.

```bash
# Run doc coverage checks during build - IN DEVELOPMENT
# bin/simple build --warn-docs

# Current workaround: Check stats before/after changes
bin/simple stats | grep "Documented:"

# Example planned output:
# Checking documentation coverage...
# Scanning 247 source files...
#
# Warning: Missing documentation
# File: src/std/array.spl:42
# Function: chunk_by
# Severity: warn
#
# Summary: 3 files with warnings, 12 total warnings
```

### Generate Coverage Reports

> **Coming Soon:** The `doc-coverage` command format options are in development. Current workaround: use `bin/simple stats --json` and parse the `.documentation` field.

```bash
# Terminal report (default) - IN DEVELOPMENT
# bin/simple doc-coverage

# Current workaround: Use stats command
bin/simple stats
bin/simple stats --json
bin/simple stats --json | jq .documentation

# Markdown report (for documentation) - PLANNED
# bin/simple doc-coverage --format=md > COVERAGE.md

# JSON report (for CI/CD integration) - USE STATS
bin/simple stats --json > stats.json

# CSV report (for spreadsheets) - PLANNED
# bin/simple doc-coverage --format=csv > coverage.csv

# Show only undocumented items - PLANNED
# bin/simple doc-coverage --missing
```

---

## Documentation Types

### 1. Public API Documentation

Public functions, classes, and structs should have docstrings:

```simple
fn parse_config(path: text) -> Config:
    """
    Parse configuration file and return Config struct.

    Args:
        path: Path to configuration file (SDN format)

    Returns:
        Parsed Config struct with validated settings

    Raises:
        Returns nil if file doesn't exist or parsing fails

    @tag:api
    """
    # Implementation...
```

**Detection:** Automatically detects all public items (exported or in public modules).

**Severity Levels:**
- **error** - Public API function with no documentation
- **warn** - Public API with partial documentation
- **info** - Non-public function without documentation

### 2. SDoctest Examples

Executable documentation examples using SDoctest syntax:

```simple
fn factorial(n: i64) -> i64:
    """
    Compute factorial of n.

    Examples:
        ```simple
        val result = factorial(5)
        expect(result).to_equal(120)

        val zero = factorial(0)
        expect(zero).to_equal(1)
        ```

    @tag:api
    """
    if n == 0:
        return 1
    n * factorial(n - 1)
```

**Benefits:**
- Documentation stays synchronized with code
- Examples are tested automatically
- Users see working code snippets

**Running SDoctest:**
```bash
# Run all SDoctest examples
bin/simple test --sdoctest

# List all SDoctest blocks
bin/simple test --sdoctest --list

# Run specific environment
bin/simple test --sdoctest --sdoctest-env=interpreter
```

### 3. Inline Comments

Complex expressions should have inline comments explaining the logic:

```simple
fn compute_score(hits: i64, total: i64, bonus: i64) -> i64:
    # Calculate base percentage (0-100)
    val base = (hits * 100) / total

    # Apply diminishing returns to bonus (log scale)
    val bonus_factor = if bonus > 0: log2(bonus + 1) else: 0

    # Final score caps at 150 to prevent inflation
    val raw_score = base + (bonus_factor * 10)
    if raw_score > 150: 150 else: raw_score
```

**When to add inline comments:**
- Complex mathematical expressions
- Bit manipulation operations
- State machine transitions
- Business logic with non-obvious rules
- Performance-critical optimizations

**Warning triggers:**
- Assignment from complex expression (>3 operators)
- Chained method calls (>2 methods)
- Deeply nested conditionals (>2 levels)

### 4. Group Comments

Related variables should be grouped with a comment:

```simple
# Parser state tracking
var current_token: Token = nil
var peek_token: Token = nil
var token_index = 0
var error_count = 0

# Symbol table management
var symbols: [Symbol] = []
var scope_stack: [Scope] = []
var current_scope: Scope = nil

# Configuration flags
var allow_warnings = true
var strict_mode = false
var max_errors = 10
```

**Detected patterns:**
- **config** - Configuration-related variables
- **state** - State tracking variables
- **constants** - Related constant definitions
- **cache** - Caching-related variables
- **buffer** - Buffer management
- **counter** - Counter/accumulator variables
- **flag** - Boolean flag groups

**Benefits:**
- Improves code organization
- Makes module structure clear
- Helps new contributors understand code

---

## Tag System

Tags categorize documentation for filtering and reporting.

### Standard Tags

| Tag | Purpose | Example Use Case |
|-----|---------|------------------|
| `@tag:api` | Public API (stable) | Functions in stdlib, exported APIs |
| `@tag:internal` | Internal implementation | Helper functions, private modules |
| `@tag:experimental` | Experimental features | Unstable APIs, RFC implementations |
| `@tag:deprecated` | Deprecated code | Functions scheduled for removal |
| `@tag:critical` | Critical path | Performance-critical functions |
| `@tag:perf` | Performance-sensitive | Hot loops, optimized algorithms |

### Tag Naming Conventions

**Format:** `@tag:category` (lowercase, alphanumeric + hyphen)

**Good:**
- `@tag:api`
- `@tag:internal`
- `@tag:socket-impl`
- `@tag:parser-core`

**Bad:**
- `@tag:API` (uppercase)
- `@tag:my_tag` (underscore)
- `@tag:this is a tag` (spaces)

### Using Tags in Reports

```bash
# Filter by tag
bin/simple doc-coverage --tag=api

# Show only critical path functions
bin/simple doc-coverage --tag=critical --missing

# JSON output for tag-based metrics
bin/simple stats --json | jq '.documentation.by_tag'
```

---

## Coverage Thresholds

Set minimum documentation coverage requirements:

### Configuration File: `doc_coverage.sdn`

```sdn
{
  "thresholds": {
    "global": 80,
    "by_kind": {
      "function": 90,
      "class": 85,
      "struct": 70
    },
    "by_module": {
      "stdlib": 95,
      "core": 90,
      "app": 75
    },
    "by_tag": {
      "api": 100,
      "critical": 95,
      "experimental": 50
    }
  },
  "exit_on_failure": true
}
```

### Running with Thresholds

```bash
# Check against thresholds (exits with code 1 if below)
bin/simple doc-coverage --threshold-check

# CI/CD integration
if ! bin/simple doc-coverage --threshold-check; then
    echo "Documentation coverage below threshold!"
    exit 1
fi
```

---

## Report Formats

### Terminal Format

**Human-readable output for CLI usage:**

```
Documentation Coverage Report
=============================

Overall Coverage: 87% (247/284 items)

By Kind:
  function:  92% (180/196)
  struct:    85% (34/40)
  class:     78% (23/29)
  enum:      95% (18/19)

By Module:
  stdlib:    94% (120/128)
  core:      89% (67/75)
  app:       74% (60/81)

Missing Documentation (37 items):
  src/std/array.spl:chunk_by
  src/std/string.spl:levenshtein
  src/core/parser.spl:parse_match_arm
  ...
```

### JSON Format

**Structured data for tooling integration:**

```json
{
  "total_items": 284,
  "documented_items": 247,
  "coverage_percent": 87,
  "by_kind": {
    "function": {"total": 196, "documented": 180, "percent": 92},
    "struct": {"total": 40, "documented": 34, "percent": 85}
  },
  "by_module": {
    "stdlib": {"total": 128, "documented": 120, "percent": 94}
  },
  "missing": [
    {"file": "src/std/array.spl", "name": "chunk_by", "kind": "function"}
  ]
}
```

### Markdown Format

**Documentation-ready report:**

```markdown
# Documentation Coverage Report

**Overall:** 87% (247/284 items)

## Coverage by Kind

| Kind | Total | Documented | Coverage |
|------|-------|------------|----------|
| function | 196 | 180 | 92% |
| struct | 40 | 34 | 85% |

## Missing Documentation

- `src/std/array.spl:chunk_by` (function)
- `src/std/string.spl:levenshtein` (function)
```

### CSV Format

**Spreadsheet-ready data:**

```csv
file,name,kind,is_documented,has_sdoctest
src/std/array.spl,map,function,true,true
src/std/array.spl,filter,function,true,true
src/std/array.spl,chunk_by,function,false,false
```

---

## CI/CD Integration

### GitHub Actions Example

```yaml
name: Documentation Coverage

on: [push, pull_request]

jobs:
  doc-coverage:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3

      - name: Check documentation coverage
        run: |
          bin/simple doc-coverage --format=json > coverage.json

      - name: Enforce thresholds
        run: |
          bin/simple doc-coverage --threshold-check

      - name: Upload coverage report
        uses: actions/upload-artifact@v3
        with:
          name: doc-coverage
          path: coverage.json

      - name: Comment on PR
        if: github.event_name == 'pull_request'
        run: |
          COVERAGE=$(jq -r '.coverage_percent' coverage.json)
          echo "Documentation coverage: ${COVERAGE}%" >> $GITHUB_STEP_SUMMARY
```

### Pre-commit Hook Example

```bash
#!/bin/bash
# .git/hooks/pre-commit

# Check only changed files
CHANGED_FILES=$(git diff --cached --name-only --diff-filter=ACM | grep '\.spl$')

if [ -n "$CHANGED_FILES" ]; then
    echo "Checking documentation coverage for changed files..."

    # Run coverage check
    if ! bin/simple build --warn-docs; then
        echo "❌ Documentation coverage check failed!"
        echo "Add documentation to new/modified functions before committing."
        exit 1
    fi
fi

echo "✅ Documentation coverage check passed"
exit 0
```

---

## Best Practices

### 1. Document Public APIs First

Focus on user-facing functions before internal implementation:

```simple
# HIGH PRIORITY - public API
fn read_config(path: text) -> Config:
    """Parse configuration from SDN file. @tag:api"""
    # ...

# LOWER PRIORITY - internal helper
fn _validate_config_field(field: text, value: text) -> bool:
    # Internal validation (can document later)
    # ...
```

### 2. Add SDoctest Examples for Complex Functions

```simple
fn merge_sorted_arrays(a: [i64], b: [i64]) -> [i64]:
    """
    Merge two sorted arrays into single sorted array.

    Examples:
        ```simple
        val result = merge_sorted_arrays([1, 3, 5], [2, 4, 6])
        expect(result).to_equal([1, 2, 3, 4, 5, 6])
        ```

    @tag:api
    """
    # ...
```

### 3. Use Inline Comments for Non-Obvious Logic

```simple
# ❌ BAD - obvious comment
val total = a + b  # Add a and b

# ✅ GOOD - explains WHY
val total = a + b  # Sum must exclude tax for wholesale customers
```

### 4. Group Related Variables

```simple
# ❌ BAD - scattered variables
var count = 0
var name = ""
var max_count = 100
var description = ""

# ✅ GOOD - grouped by purpose
# Counter state
var count = 0
var max_count = 100

# Display information
var name = ""
var description = ""
```

### 5. Tag Appropriately

```simple
# ✅ GOOD - clear categorization
fn parse_json(text: text) -> Dict:
    """Parse JSON string. @tag:api"""
    _internal_parse(text)  # Uses @tag:internal helper

# ❌ BAD - everything marked api
fn _debug_print_tokens():
    """Debug helper. @tag:api"""  # Should be @tag:internal
```

---

## Common Patterns

### Pattern 1: API Function with Examples

```simple
fn split_words(text: text) -> [text]:
    """
    Split text into words by whitespace.

    Examples:
        ```simple
        val words = split_words("hello world")
        expect(words).to_equal(["hello", "world"])
        ```

    Args:
        text: Input string to split

    Returns:
        Array of words (whitespace removed)

    @tag:api
    """
    text.split(" ")
```

### Pattern 2: Internal Helper with Inline Comments

```simple
fn _parse_escape_sequence(chars: [text], index: i64) -> (text, i64):
    # Handle \n, \t, \r escape sequences
    val char = chars[index]
    if char == "n":
        return ("\n", index + 1)
    elif char == "t":
        return ("\t", index + 1)

    # Default: return character unchanged
    (char, index + 1)
```

### Pattern 3: Struct with Field Documentation

```simple
struct Config:
    """
    Application configuration.

    @tag:api
    """
    # Server settings
    host: text
    port: i64

    # Performance tuning
    max_connections: i64
    timeout_ms: i64

    # Feature flags
    enable_caching: bool
    debug_mode: bool
```

---

## Troubleshooting

### "No source files found"

**Problem:** `doc-coverage` reports 0 files scanned.

**Solution:**
```bash
# Check you're in project root
pwd  # Should show /home/user/project

# Verify source files exist
ls src/std/*.spl

# Run from correct directory
cd /path/to/project
bin/simple doc-coverage
```

### "Function not counted as documented"

**Problem:** Function has docstring but shows as undocumented.

**Causes:**
1. Docstring must be first line after function declaration
2. Must use `"""` triple-quotes
3. Must not have blank lines before docstring

```simple
# ❌ WRONG - blank line before docstring
fn my_function():

    """This is a docstring"""

# ✅ CORRECT - docstring immediately after declaration
fn my_function():
    """This is a docstring"""
```

### "SDoctest examples not detected"

**Problem:** Examples in docstring not counted.

**Solution:** Use proper fence syntax:
```simple
"""
Examples:
    ```simple
    val result = my_function(5)
    expect(result).to_equal(10)
    ```
"""
```

**Note:** Must have:
- Empty line after "Examples:"
- Opening fence: ` ```simple`
- Closing fence: ` ``` `
- Proper indentation (4 spaces for fence, 8 for code)

### "High false-positive rate for inline comments"

**Problem:** System warns about missing inline comments for simple code.

**Solution:** Tune warning thresholds in `doc_coverage.sdn`:
```sdn
{
  "inline_comment_thresholds": {
    "complexity_threshold": 5,  # Require comments for 5+ operators (was 3)
    "chain_threshold": 3        # Require comments for 3+ chained calls (was 2)
  }
}
```

---

## Integration with Other Tools

### Statistics Integration

Documentation metrics are included in `bin/simple stats`:

```bash
# View all statistics
bin/simple stats

# Extract doc coverage percentage
bin/simple stats --json | jq .documentation.coverage_percent

# Check if below threshold
COVERAGE=$(bin/simple stats --json | jq .documentation.coverage_percent)
if [ $COVERAGE -lt 80 ]; then
    echo "Coverage below 80%: ${COVERAGE}%"
fi
```

### Build System Integration

```bash
# Run during build
bin/simple build --warn-docs

# Combine with other checks
bin/simple build lint --warn-docs check
```

### Test Integration

```bash
# Run SDoctest examples
bin/simple test --sdoctest

# Run SDoctest + unit tests
bin/simple test
bin/simple test --sdoctest
```

---

## Advanced Usage

### Custom Tag Hierarchies

```simple
fn critical_path_function():
    """
    Core algorithm used in hot path.

    @tag:critical
    @tag:perf
    @tag:api
    """
```

### Module-Level Documentation

```simple
# At top of module file
"""
Array utility functions.

This module provides functional array operations similar to
JavaScript's Array methods and Python's list comprehensions.

@tag:api
@tag:stdlib
"""

fn map(arr: [i64], fn: fn(i64) -> i64) -> [i64]:
    # ...
```

### Conditional Documentation

```simple
fn experimental_feature():
    """
    Experimental sorting algorithm (unstable API).

    WARNING: This API may change in future versions.
    Use at your own risk.

    @tag:experimental
    """
```

---

## Reference

### Coverage Metrics

| Metric | Description | Formula |
|--------|-------------|---------|
| **Overall Coverage** | Percentage of documented items | `(documented / total) * 100` |
| **By Kind Coverage** | Coverage per item type | Per function/struct/class/enum |
| **By Module Coverage** | Coverage per module category | Per stdlib/core/app/lib |
| **By Tag Coverage** | Coverage per tag | Per @tag:name |
| **SDoctest Coverage** | Functions with examples | Functions with SDoctest blocks |

### Exit Codes

| Code | Meaning |
|------|---------|
| 0 | Success (above threshold) |
| 1 | Below threshold or errors |

### File Locations

| Path | Purpose |
|------|---------|
| `src/app/doc_coverage/` | Implementation |
| `doc/guide/documentation_coverage.md` | This guide |
| `test/unit/app/doc_coverage/` | Tests |
| `doc_coverage.sdn` | Configuration (optional) |

---

## See Also

- **SDoctest Guide:** `doc/guide/sdoctest.md` (executable documentation)
- **Style Guide:** `doc/guide/coding_style.md` (documentation conventions)
- **Testing Guide:** `doc/guide/comprehensive_testing.md` (test documentation)
- **Implementation Report:** `doc/report/doc_coverage_reporting_implementation_2026-02-14.md`

---

**Last Updated:** 2026-02-14
