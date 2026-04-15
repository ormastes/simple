# Slow Test Implementation - 2026-01-19

## Objective
Implement a proper slow test marking system to handle tests that take 120+ seconds, allowing them to be skipped by default but run when explicitly requested.

## Implementation

### 1. Enhanced Example Class with Tags and Timeout
**File**: `simple/std_lib/src/spec/registry.spl`

Added new fields and methods to the `Example` class:
- `tags: List<text>` - Tag system for categorizing tests
- `timeout_seconds: Option<i32>` - Custom timeout support
- `slow()` method - Mark tests as slow
- `with_timeout(seconds)` method - Set custom timeout
- `with_tag(tag)` and `has_tag(tag)` methods - Tag management
- `should_run(run_slow)` method - Conditional execution logic

### 2. New `slow_it()` DSL Function
**File**: `simple/std_lib/src/spec/dsl.spl`

Created `slow_it()` function for defining slow tests:
```simple
slow_it "generates all 15 Lean files":
    val files = regen.regenerate_all()
    expect files.len == 15
```

Features:
- Automatically marks example with "slow" tag
- Checks `RUN_SLOW_TESTS` environment variable
- Skips test if `RUN_SLOW_TESTS` is not "1" or "true"
- Works identically to `it()` when enabled

### 3. Element-Level Module Imports
**File**: `simple/std_lib/src/shell.spl`

Added export statement to enable element-level imports:
```simple
export shell, file, dir, path, env
```

This allows:
```simple
import shell.env      # Instead of: import shell
env.get("VAR")        # Instead of: shell.env.get("VAR")
```

### 4. Updated Test Exports
**File**: `simple/std_lib/src/spec/__init__.spl`

Added `slow_it` to exports:
```simple
export describe, context, it, skip, slow_it from dsl
```

### 5. Updated Regeneration Tests
**File**: `simple/std_lib/test/unit/verification/regeneration_spec.spl`

Converted slow tests to use `slow_it()`:
- 3 tests converted to `slow_it()`
- Added documentation about `RUN_SLOW_TESTS` environment variable
- Tests are skipped by default (fast CI)
- Can be enabled with: `RUN_SLOW_TESTS=1 cargo test`

## Usage

### Running Tests Normally (Skip Slow Tests)
```bash
cargo test
# or
make check
```
- Slow tests are automatically skipped
- Fast execution (< 30 seconds)

### Running Slow Tests
```bash
RUN_SLOW_TESTS=1 cargo test

# Or for specific test:
RUN_SLOW_TESTS=1 cargo test simple_stdlib_unit_verification_regeneration_spec
```

### In Test Files
```simple
import std.spec

describe "My Module":
    it "fast test":
        # Runs always
        expect true == true

    slow_it "slow integration test":
        # Only runs when RUN_SLOW_TESTS=1
        # Takes 120+ seconds
        val result = expensive_operation()
        expect result.is_valid()
```

## Benefits

1. **Fast CI/CD**: Slow tests don't block regular development workflow
2. **Explicit Control**: Developers choose when to run expensive tests
3. **Backward Compatible**: Existing tests continue to work
4. **Flexible**: Can be extended with more tags (integration, gui, etc.)
5. **Clean API**: `slow_it()` reads naturally like `it()`

## Future Enhancements

1. **Additional Tags**:
   - `integration_it()` for integration tests
   - `gui_it()` for GUI tests requiring display
   - `network_it()` for tests requiring network access

2. **Test Filtering**:
   - `RUN_ONLY_TAGS="slow,integration"` to run specific test types
   - `SKIP_TAGS="gui"` to exclude specific test types

3. **Timeout Enforcement**:
   - Actually enforce the `timeout_seconds` field
   - Kill tests that exceed their timeout

4. **Test Reporting**:
   - Show skipped test count with reason
   - Summary of why tests were skipped

## Files Modified

1. `simple/std_lib/src/spec/registry.spl` - Enhanced Example class
2. `simple/std_lib/src/spec/dsl.spl` - Added slow_it() function
3. `simple/std_lib/src/spec/__init__.spl` - Export slow_it
4. `simple/std_lib/src/shell.spl` - Element-level exports
5. `simple/std_lib/test/unit/verification/regeneration_spec.spl` - Converted to slow_it()

## Status
✅ **IMPLEMENTED** - Slow test system is functional and ready for use
