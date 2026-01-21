# Test Safe Mode

## Problem

When listing or running tests (especially with `--only-skipped --list`), some test files may:
- Hang indefinitely during evaluation
- Crash the entire test runner
- Cause timeouts that affect all subsequent tests

Since all tests normally run in the same process with a single interpreter instance, one problematic test file can bring down the entire test run.

## Solution: Safe Mode

Safe mode runs each test file in a separate process with a configurable timeout. This provides:

1. **Process Isolation**: Each test file runs in its own process
2. **Timeout Protection**: Tests that hang are automatically killed
3. **Crash Resilience**: A crash in one test doesn't affect others
4. **Progress Tracking**: Shows which test is currently running
5. **Continuous Execution**: The test runner continues even if some tests fail/timeout

## Usage

### Basic Safe Mode

```bash
# Run tests in safe mode with default 30-second timeout per file
./target/debug/simple test --safe-mode

# Run with custom timeout (in seconds)
./target/debug/simple test --safe-mode --timeout 5
```

### Safe Mode with List

```bash
# List all tests safely (each file gets 3 seconds to list its tests)
./target/debug/simple test --safe-mode --timeout 3 --list

# List only skipped tests safely
./target/debug/simple test --safe-mode --timeout 3 --only-skipped --list
```

### Safe Mode with Filters

```bash
# Run tests in a specific directory
./target/debug/simple test --safe-mode test/lib/std/unit/collections

# Run with tag filters
./target/debug/simple test --safe-mode --tag=integration

# Run only slow tests
./target/debug/simple test --safe-mode --timeout 60 --only-slow
```

## Performance Considerations

### Trade-offs

**Advantages:**
- Complete isolation prevents cascading failures
- Timeouts prevent indefinite hangs
- Progress is visible (shows N/total for each test)

**Disadvantages:**
- **Slower**: Each test file spawns a new process and interpreter
- **Overhead**: Process creation and initialization adds 1-2 seconds per file
- **Resource usage**: More memory due to multiple processes

### Expected Run Times

With default settings:
- **Single test file**: ~2-8 seconds (process spawn + test execution)
- **Small test suite** (10 files): ~20-80 seconds
- **Full test suite** (369 files): ~10-20 minutes

### When to Use Safe Mode

✅ **Use safe mode when:**
- Debugging test hangs or crashes
- Listing tests with problematic filters (`--only-skipped`)
- Running untrusted or experimental test files
- You need guaranteed isolation between tests
- Some tests are known to hang or crash

❌ **Don't use safe mode when:**
- Running a well-tested suite quickly
- You need fast feedback during development
- Running a small number of known-good tests
- Performance is critical

## Examples

### Example 1: Debug Hanging Tests

```bash
# Find which test is hanging by running with a short timeout
./target/debug/simple test --safe-mode --timeout 3 test/problematic_area

# Output shows exactly which test times out:
# [5/10] test/problematic_area/hanging_test.spl
#   FAILED (3001ms)
#   Error: Test timed out after 3 seconds
```

### Example 2: List Skipped Tests Safely

```bash
# Original problem: this would hang indefinitely
./target/debug/simple test --only-skipped --list  # ❌ HANGS

# Solution: use safe mode
./target/debug/simple test --safe-mode --timeout 2 --only-skipped --list  # ✅ WORKS
```

### Example 3: Run Subset of Tests

```bash
# Run a specific directory's tests in safe mode
./target/debug/simple test --safe-mode --timeout 5 test/lib/std/unit/collections

# Output:
# Simple Test Runner v0.1.0
#
# [1/1] test/lib/std/unit/collections/list_compact_spec.spl
#   ✓ All tests passed!
```

## Implementation Details

### How It Works

1. **Discovery Phase**: Normal (same process)
   - Test files are discovered using filesystem walk
   - Tag filtering happens at file level
   - No interpreter is created in safe mode

2. **Execution Phase**: Isolated (separate processes)
   - For each test file:
     - Spawn `./target/debug/simple <test_file.spl>` as subprocess
     - Set timeout based on `--timeout` flag
     - Capture stdout/stderr
     - Parse output for test results
     - Kill process if timeout exceeded

3. **Result Collection**: Normal (same process)
   - Aggregate results from all subprocesses
   - Generate summary report
   - Update databases (if not in list mode)

### Environment Variables

Safe mode automatically propagates these environment variables to subprocesses:
- `SIMPLE_TEST_MODE`: Set to "list" when `--list` is used
- `SIMPLE_TEST_FILTER`: Set to "slow" or "skipped" based on flags
- `SIMPLE_TEST_SHOW_TAGS`: Set to "1" when `--show-tags` is used

### Timeout Behavior

When a test times out:
- Process is killed with SIGKILL (Unix) or taskkill (Windows)
- Test is marked as FAILED
- Error message: "Test timed out after N seconds"
- Test runner continues with next test

## Flags

| Flag | Description | Default |
|------|-------------|---------|
| `--safe-mode` | Enable safe mode (alias: `--safe`) | Off |
| `--timeout N` | Timeout in seconds per test file | 30 |

## Troubleshooting

### Tests timeout in safe mode but not normally

**Cause**: Tests that depend on shared state or the full test suite context may fail in isolation.

**Solution**: Ensure each test file is self-contained and doesn't depend on:
- Global state from other tests
- Specific execution order
- Test suite-level initialization

### Safe mode is too slow

**Cause**: Process spawn overhead for each test file.

**Solutions**:
1. Reduce timeout: `--timeout 2` (faster, but may miss slow tests)
2. Filter tests: Run only specific directories or tags
3. Don't use safe mode for routine development testing

### All tests are failing with "No runner available"

**Cause**: Internal error in test runner logic.

**Solution**: Report as bug - this shouldn't happen in safe mode.

## See Also

- [Test Filtering](./test_filtering.md) - Filter tests by tags, patterns, etc.
- [Test Runner Options](../test_runner.md) - All available test flags
- [Debugging Tests](./debugging_tests.md) - Debug hanging or failing tests
