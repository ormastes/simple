# Test Listing Performance Issue - 2026-01-22

## Problem

`./target/release/simple test --only-skipped --list` hangs/takes extremely long time.

## Root Cause

The test runner's list mode still executes every single test file to discover which tests are skipped. With ~8,000 tests across many files, this is very slow.

**Code path:**
1. `run_tests()` sets `SIMPLE_TEST_MODE=list` environment variable
2. But still calls `execute_test_files()` which iterates through ALL test files
3. For each file, calls `runner.run_file(path)` - actually executes the .spl file
4. The Simple code reads `SIMPLE_TEST_MODE` and lists instead of running, but the file still needs to be parsed and executed

**Problem location:** `src/rust/driver/src/cli/test_runner/runner.rs:207-278`

```rust
fn execute_test_files(...) {
    for (idx, path) in test_files.iter().enumerate() {
        // This runs EVERY file, even in list mode!
        let result = run_test_file(runner, path);  // Executes the file
        ...
    }
}
```

## Why It's Slow

- **7,909 total tests** across many files
- **List mode** still parses + executes each file (just doesn't run test bodies)
- **No caching** of test metadata
- **No AST-only parsing** for listing

## Quick Fix

Limit the scope when using `--only-skipped --list`:

```bash
# Instead of scanning all files:
./target/release/simple test --only-skipped --list  # SLOW

# Scan specific files/directories:
./target/release/simple test test/lib/std/unit/ --only-skipped --list
./target/release/simple test path/to/specific_spec.spl --only-skipped --list
```

## Better Solution (Future Work)

### Option 1: Fast List Mode (AST parsing only)
```rust
fn execute_test_files(...) {
    if options.list || options.list_ignored {
        // Fast path: parse AST only, don't execute
        return list_tests_fast(test_files, options);
    }
    // Normal path: execute files
    ...
}

fn list_tests_fast(test_files: &[PathBuf], options: &TestOptions) -> ... {
    // Parse .spl files for 'it', 'slow_it', 'describe' blocks
    // Extract test names and tags
    // Don't run any code
}
```

### Option 2: Test Index/Cache
```rust
// Cache test metadata in .simple/test_index.json
{
    "path/to/test.spl": {
        "tests": [
            {"name": "should work", "tags": ["unit"], "line": 10},
            {"name": "slow test", "tags": ["slow"], "line": 20}
        ],
        "last_modified": "2026-01-22T..."
    }
}
```

Then listing is just reading the index, only re-parsing changed files.

### Option 3: Use Test Database
The test database (`doc/test/test_db.sdn`) already tracks all tests:

```rust
fn list_tests_from_db(options: &TestOptions) -> Vec<TestInfo> {
    // Read doc/test/test_db.sdn
    // Filter by tags (skip, slow, etc.)
    // Return test names without executing anything
}
```

## Recommended Immediate Action

**Document the limitation:**

```bash
# ⚠️ SLOW - scans all test files
./target/release/simple test --only-skipped --list

# ✅ FAST - limit scope
./target/release/simple test test/lib/std/unit/ --only-skipped --list

# ✅ Or use test database
cat doc/test/test_db.sdn | grep skip
```

## Implementation Priority

- **P0 (Immediate):** Document limitation in `--help` and README
- **P1 (Next sprint):** Implement fast list mode (AST parsing only)
- **P2 (Future):** Add test index/cache for instant listing

## Workaround for Users

### Current Best Practice

```bash
# 1. Use test database for quick lookup
cat doc/test/test_db.sdn | grep '"skip"'

# 2. Or limit scope to specific directories
./target/release/simple test test/lib/std/unit/syntax/ --only-skipped --list

# 3. Or just run tests with filter (fast enough)
./target/release/simple test --only-skipped  # Runs only skipped tests
```

### Why Test Database Works

The test database is updated after every test run and contains:
- All test names
- Test tags (skip, slow, etc.)
- Pass/fail status
- Timing data

No execution needed - just parse the SDN file.

## Status

- **Issue:** Identified root cause
- **Workaround:** Use scoped paths or test database
- **Fix:** Not implemented yet (requires refactoring)
- **Priority:** P1 (next sprint)

---

**Date:** 2026-01-22
**Reporter:** Claude Code
**Affected Versions:** All
**Impact:** Medium (workarounds available)
