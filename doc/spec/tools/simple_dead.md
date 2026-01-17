# simple_dead - Dead Code Detector

## Overview

Finds unused code: functions, classes, variables, and imports that are never referenced.

## Usage

```bash
simple_dead .                      # Find all dead code
simple_dead . --functions          # Only unused functions
simple_dead . --imports            # Only unused imports
simple_dead . --variables          # Only unused variables
simple_dead . --exclude-tests      # Ignore test files
simple_dead . --json               # JSON output
```

## Options

| Flag | Description |
|------|-------------|
| `--functions` | Only check unused functions |
| `--classes` | Only check unused classes |
| `--imports` | Only check unused imports |
| `--variables` | Only check unused variables |
| `--exclude-tests` | Ignore *_spec.spl, *_test.spl |
| `--exclude <pattern>` | Exclude files matching pattern |
| `--json` | JSON output format |

## Output Format

### Default

```
Dead Code Report
================

Unused Functions (5):
  src/utils.spl:23: fn deprecated_helper()
  src/utils.spl:45: fn old_format()
  src/parser.spl:156: fn unused_optimization()
  src/server.spl:89: fn debug_dump()
  src/server.spl:112: fn test_stub()

Unused Classes (2):
  src/models.spl:34: class OldUser
  src/models.spl:78: class DeprecatedConfig

Unused Imports (8):
  src/main.spl:3: import core.debug
  src/server.spl:5: import net.websocket
  src/handler.spl:2: import core.regex
  ...

Unused Variables (3):
  src/config.spl:12: let DEBUG_MODE = true
  src/utils.spl:5: let VERSION = "0.1.0"
  src/server.spl:15: let MAX_RETRIES = 3

Summary:
  Functions: 5 unused
  Classes: 2 unused
  Imports: 8 unused
  Variables: 3 unused
  Total: 18 items
```

### JSON

```json
{
  "unused_functions": [
    {
      "file": "src/utils.spl",
      "line": 23,
      "name": "deprecated_helper",
      "signature": "fn deprecated_helper()"
    }
  ],
  "unused_classes": [...],
  "unused_imports": [...],
  "unused_variables": [...],
  "summary": {
    "functions": 5,
    "classes": 2,
    "imports": 8,
    "variables": 3,
    "total": 18
  }
}
```

## Detection Logic

### Unused Functions

1. Collect all function definitions
2. Collect all function calls and references
3. Functions with no references are unused
4. Exclude: `main`, `pub` functions, test functions

### Unused Classes

1. Collect all class definitions
2. Collect all class instantiations and type references
3. Classes with no references are unused
4. Exclude: `pub` classes

### Unused Imports

1. Collect all import statements
2. Check if imported names are used in file
3. Imports with no usage are unused

### Unused Variables

1. Collect all `let` declarations at module level
2. Check if variables are referenced
3. Variables with no references are unused
4. Exclude: `_` prefixed variables

## Implementation Notes

1. Two-pass analysis:
   - Pass 1: Collect all definitions
   - Pass 2: Collect all references
2. Build reference graph
3. Find unreferenced items
4. Filter by visibility and patterns

## False Positive Handling

Some code is intentionally unused:
- Public API (`pub`) - may be used externally
- Main entry point (`fn main`)
- Test code (in `*_spec.spl`)
- Variables prefixed with `_`

## Dependencies

- `native_fs_read_string` - File reading
- `sys_get_args` - Command-line arguments

## Examples

```bash
# Find unused imports for cleanup
$ simple_dead . --imports

# Check before release (strict)
$ simple_dead . --exclude-tests

# CI integration
$ simple_dead . --json | jq '.summary.total'
```

## Exit Codes

| Code | Meaning |
|------|---------|
| 0 | No dead code found |
| 1 | Dead code found |
| 2 | Error |
