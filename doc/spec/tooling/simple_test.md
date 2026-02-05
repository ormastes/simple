# simple_test - BDD Test Runner

## Overview

Runs BDD-style spec tests with nice formatted output, timing, and summary.

## Usage

```bash
simple_test                        # Run all tests in test/
simple_test test/unit/             # Run tests in directory
simple_test test/main_spec.spl     # Run single test file
simple_test --filter "json"        # Run tests matching pattern
simple_test --watch                # Watch mode (rerun on changes)
simple_test --verbose              # Show all test output
simple_test --json                 # JSON output for CI
```

## Options

| Flag | Description |
|------|-------------|
| `--filter <pattern>` | Run only tests matching pattern |
| `--watch` | Watch mode, rerun on file changes |
| `--verbose` | Show all output including passing |
| `--json` | JSON output format |
| `--parallel` | Run tests in parallel |
| `--timeout <ms>` | Test timeout (default: 5000) |
| `--fail-fast` | Stop on first failure |

## Output Format

### Default (Pretty)

```
simple_test v0.1.0

Running tests...

  core/json_spec.spl
    ✓ parse should handle empty object (2ms)
    ✓ parse should handle nested objects (5ms)
    ✗ parse should handle unicode (3ms)
      Expected: "こんにちは"
      Received: "???????"
    ✓ stringify should format numbers (1ms)

  core/string_spec.spl
    ✓ split should work with delimiter (1ms)
    ✓ trim should remove whitespace (0ms)
    ✓ replace should handle multiple (2ms)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Tests:  6 passed, 1 failed, 7 total
Time:   14ms
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### JSON

```json
{
  "suites": [
    {
      "file": "core/json_spec.spl",
      "tests": [
        {
          "name": "parse should handle empty object",
          "status": "passed",
          "duration_ms": 2
        },
        {
          "name": "parse should handle unicode",
          "status": "failed",
          "duration_ms": 3,
          "error": {
            "expected": "こんにちは",
            "received": "???????"
          }
        }
      ]
    }
  ],
  "summary": {
    "passed": 6,
    "failed": 1,
    "skipped": 0,
    "total": 7,
    "duration_ms": 14
  }
}
```

## Test File Format

```simple
"""
Tests for JSON module
"""

import spec.{describe, it, expect, before_each, after_each}
import core.json

describe "JSON.parse":
    before_each:
        # Setup code

    it "should handle empty object":
        let result = json.parse("{}")
        expect(result).to_be_ok()
        expect(result.unwrap()).to_equal({})

    it "should handle arrays":
        let result = json.parse("[1, 2, 3]")
        expect(result.unwrap()).to_equal([1, 2, 3])

describe "JSON.stringify":
    it "should format objects":
        let obj = {"name": "test"}
        expect(json.stringify(obj)).to_equal('{"name":"test"}')
```

## Implementation Notes

1. Discover test files: `*_spec.spl`, `*_test.spl`
2. Parse spec DSL (describe, it, expect)
3. Run each test, capture output and timing
4. Format results with colors (if terminal)
5. Calculate summary statistics
6. Return exit code (0 = pass, 1 = fail)

## Watch Mode

```bash
$ simple_test --watch

Watching for changes...

[15:42:01] Running tests...
Tests: 7 passed, 0 failed

[15:42:15] File changed: src/core/json.spl
[15:42:15] Running tests...
Tests: 6 passed, 1 failed
```

## Dependencies

- `native_fs_read_string` - File reading
- `sys_get_args` - Command-line arguments
- File watcher (for --watch mode)

## Exit Codes

| Code | Meaning |
|------|---------|
| 0 | All tests passed |
| 1 | Some tests failed |
| 2 | Error (file not found, parse error) |
