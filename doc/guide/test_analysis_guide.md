# Test Analysis Tool - Quick Start Guide

A Simple language CLI tool for analyzing test failures and prioritizing feature implementation.

## Installation

The tool is built into the Simple compiler. No separate installation needed!

```bash
# Build Simple (if not already built)
cd /home/ormastes/dev/pub/simple
cargo build

# Tool is ready to use
./target/debug/simple_old test-analysis help
```

## Quick Start

### 1. Analyze All Failures

```bash
./target/debug/simple_old test-analysis analyze
```

**Output shows:**
- Total failed tests
- Breakdown by error type
- Top features needed (prioritized)

### 2. Get Detailed Failure Information

```bash
./target/debug/simple_old test-analysis details --limit=10
```

**Filter by category:**
```bash
./target/debug/simple_old test-analysis details --category=Unit --limit=5
```

### 3. Classify a Specific Error

```bash
./target/debug/simple_old test-analysis classify "parse error: expected Fn, found Static"
```

### 4. Extract Needed Features

```bash
./target/debug/simple_old test-analysis extract "expected expression, found At"
```

## Common Workflows

### Daily Development

```bash
# Run tests
./target/debug/simple_old test

# Quick check on failures
./target/debug/simple_old test-analysis analyze

# Focus on your area
./target/debug/simple_old test-analysis details --category=Unit
```

### Feature Planning

```bash
# Get comprehensive analysis
./target/debug/simple_old test-analysis analyze > analysis.txt

# Review top features
head -50 analysis.txt

# Implement highest priority features first
# (Those marked "Critical" with 10+ tests blocked)
```

### Debugging Specific Errors

```bash
# Get all parse errors
./target/debug/simple_old test-analysis details --category=System | grep "parse_error"

# Classify the error
./target/debug/simple_old test-analysis classify "your error message here"

# See what feature is needed
./target/debug/simple_old test-analysis extract "your error message here"
```

## Output Examples

### Analyze Command

```
============================================================
FAILURE ANALYSIS REPORT
============================================================

Total Failed Tests: 95

--- Failures by Error Type ---

| Error Type       | Count | Percentage |
|------------------|-------|------------|
| parse_error      | 65    | 68% |
| semantic_error   | 15    | 16% |
| timeout          | 8     | 8% |
| file_not_found   | 7     | 7% |

--- Most Needed Features ---

| Feature                  | Tests | Priority |
|--------------------------|-------|----------|
| dict_literal_syntax      | 15    | Critical |
| matrix_multiplication    | 12    | Critical |
| static_fields            | 8     | High |
| xor_keyword              | 7     | High |
| default_parameters       | 3     | Medium |
...
```

### Details Command

```
=== Failed Test Details ===

------------------------------------------------------------
Test: test_static_spec
File: tmp/test_static_spec.spl
Category: Unit
Error Type: parse_error
Needed Features: static_fields

Error Message:
  parse error: expected Fn, found Static
------------------------------------------------------------
...
```

### Classify Command

```
=== Error Classification ===
Type: parse_error
Description: Syntax parsing error

Error Message:
  parse error: expected Fn, found Static
```

### Extract Command

```
=== Feature Extraction ===
Found 1 needed features:
  - static_fields: Static field declarations
```

## Priority Levels

| Symbol | Priority | Tests Blocked | Action |
|--------|----------|---------------|--------|
| 🔴 | Critical | 10+ | Implement ASAP |
| 🟠 | High | 5-9 | Next sprint |
| 🟡 | Medium | 2-4 | Backlog |
| 🟢 | Low | 1 | Nice to have |

## Tips and Tricks

### 1. Save Analysis for Later

```bash
./target/debug/simple_old test-analysis analyze > /tmp/test-analysis.txt
less /tmp/test-analysis.txt
```

### 2. Focus on One Error Type

```bash
./target/debug/simple_old test-analysis details | grep "parse_error" -A 5
```

### 3. Count Features Needed

```bash
./target/debug/simple_old test-analysis analyze | grep "Critical" | wc -l
```

### 4. Quick Priority Check

```bash
./target/debug/simple_old test-analysis analyze | grep -E "Critical|High" | head -10
```

### 5. Integration with Git

```bash
# Before committing
./target/debug/simple_old test-analysis analyze | grep "Critical"

# If Critical features are blocking, reconsider commit
```

## Database Files

The tool reads from:
- **`doc/test/test_db.sdn`** - Test execution results (updated by `simple test`)

You can specify a custom database:
```bash
./target/debug/simple_old test-analysis analyze --db=/path/to/custom/test_db.sdn
```

## Troubleshooting

### "Error: Failed to read test database"

**Cause:** Database file doesn't exist or path is wrong

**Solution:**
```bash
# Run tests first to generate database
./target/debug/simple_old test

# Check file exists
ls -la doc/test/test_db.sdn

# Or specify correct path
./target/debug/simple_old test-analysis analyze --db=doc/test/test_db.sdn
```

### "Error: No tests table found"

**Cause:** Database file is empty or corrupted

**Solution:**
```bash
# Regenerate database
./target/debug/simple_old test

# Verify file content
head doc/test/test_db.sdn
```

### "No specific features identified"

**Cause:** Error message doesn't match known patterns

**Solution:**
- This is normal for some errors
- The error is still classified by type
- Add new patterns if needed (edit `src/app/test_analysis/main.spl`)

## Advanced Usage

### Custom Database Path

```bash
# Use different database
./target/debug/simple_old test-analysis analyze --db=/custom/path/test_db.sdn
```

### Combining with Other Tools

```bash
# Pipe to jq for JSON processing (future feature)
./target/debug/simple_old test-analysis analyze --json | jq '.features'

# Grep for specific patterns
./target/debug/simple_old test-analysis details | grep "matrix"

# Count specific error types
./target/debug/simple_old test-analysis details | grep "Error Type:" | sort | uniq -c
```

### Scripting

```bash
#!/bin/bash
# check-critical-failures.sh

OUTPUT=$(./target/debug/simple_old test-analysis analyze)

CRITICAL_COUNT=$(echo "$OUTPUT" | grep "Critical" | wc -l)

if [ "$CRITICAL_COUNT" -gt 5 ]; then
    echo "WARNING: $CRITICAL_COUNT critical features blocking tests!"
    echo "$OUTPUT" | grep "Critical"
    exit 1
fi

echo "OK: Only $CRITICAL_COUNT critical features"
exit 0
```

## See Also

- **Full Documentation:** `doc/report/test_analysis_simple_implementation.md`
- **MCP Tools:** `doc/report/mcp_failure_analysis_implementation.md`
- **Test Framework:** `doc/spec/testing_framework_spec.md`
- **SDN Format:** `doc/spec/sdn_format.md`

## Support

For issues or questions:
1. Check the test output: `./target/debug/simple_old test-analysis help`
2. Review the documentation in `doc/report/`
3. File an issue in the Simple project repository
