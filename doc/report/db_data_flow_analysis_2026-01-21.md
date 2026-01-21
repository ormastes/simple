# Test Database Data Flow Analysis

## How Data Flows from SSpec to Database

### Current Flow (File-Level Tracking)

```
┌─────────────────────────────────────────────────────────────┐
│ 1. SSpec Test File (*.spl)                                  │
│    - Contains: it, ignore_it, slow_it, skip tests           │
└─────────────────────┬───────────────────────────────────────┘
                      │
                      ▼
┌─────────────────────────────────────────────────────────────┐
│ 2. Simple Test Runner Executes File                         │
│    $ ./target/release/simple test test/my_spec.spl          │
└─────────────────────┬───────────────────────────────────────┘
                      │
                      ▼
┌─────────────────────────────────────────────────────────────┐
│ 3. SSpec Executor (executor.spl) Runs Tests                 │
│    - Counts: passed, failed, pending (skipped), ignored     │
│    - Outputs summary string                                  │
└─────────────────────┬───────────────────────────────────────┘
                      │
                      ▼
┌─────────────────────────────────────────────────────────────┐
│ 4. SSpec Output (STDOUT)                                    │
│    "7 examples, 0 failures, 0 pending, 4 ignored"           │
│    "Finished in 0.5s"                                        │
└─────────────────────┬───────────────────────────────────────┘
                      │
                      ▼
┌─────────────────────────────────────────────────────────────┐
│ 5. Rust Test Runner (execution.rs)                          │
│    - parse_test_output() extracts counts                    │
│    - Creates TestFileResult { passed, failed, skipped,      │
│                                ignored, duration_ms }        │
└─────────────────────┬───────────────────────────────────────┘
                      │
                      ▼
┌─────────────────────────────────────────────────────────────┐
│ 6. Test DB Update (test_db_update.rs)                       │
│    - convert_result_to_db() → TestStatus                    │
│    - Priority: Failed > Ignored > Passed > Skipped          │
└─────────────────────┬───────────────────────────────────────┘
                      │
                      ▼
┌─────────────────────────────────────────────────────────────┐
│ 7. Database Update (test_db.rs)                             │
│    - update_test_result() creates/updates ONE record        │
│    - Saves to: doc/test/test_db.sdn                         │
└─────────────────────┬───────────────────────────────────────┘
                      │
                      ▼
┌─────────────────────────────────────────────────────────────┐
│ 8. Database Entry (SDN format)                              │
│    test_file, test_name, status, timing, history, ...       │
│    ONE ROW PER FILE (not per individual test)               │
└─────────────────────────────────────────────────────────────┘
```

## Problem: File-Level vs Test-Level Tracking

### Current Behavior
```
File: test/my_spec.spl
  - Contains: 3 passing + 4 ignored tests
  - Database: ONE entry with status = "ignored"
  - Result: Can't see individual ignored tests
```

### What We Need
```
File: test/my_spec.spl
  - Contains: 3 passing + 4 ignored tests
  - Database: 7 entries (one per test)
  - Result: Can see each ignored test individually
```

## Why Only 1 Entry Per File?

Looking at `test_db_update.rs`:

```rust
pub fn update_test_database(
    test_files: &[PathBuf],        // List of test FILES
    results: &[TestFileResult],    // One result PER FILE
    all_tests_run: bool,
) -> Result<(), String> {
    for (test_path, result) in test_files.iter().zip(results.iter()) {
        let test_id = test_path.to_str().unwrap_or("unknown");
        // Creates ONE database entry per file
        test_db::update_test_result(
            &mut test_db,
            &test_id,          // File path as ID
            &test_name,        // File stem as name
            // ...
        );
    }
}
```

**Key Issue:** The loop iterates over FILES, not individual tests.

## Solutions

### Option 1: Parse Individual Tests from Output (Recommended)

SSpec needs to output individual test information, not just counts.

**Current Output:**
```
7 examples, 0 failures, 0 pending, 4 ignored
```

**Needed Output (JSON or structured format):**
```json
{
  "tests": [
    {"name": "regular passing test", "status": "passed", "duration_ms": 5},
    {"name": "first slow test", "status": "ignored", "duration_ms": 0},
    {"name": "second slow test", "status": "ignored", "duration_ms": 0},
    ...
  ],
  "summary": {"total": 7, "passed": 3, "failed": 0, "ignored": 4}
}
```

**Implementation:**
1. Add JSON formatter to SSpec (formatters/json.spl exists!)
2. Use `--format=json` flag in test runner
3. Parse JSON output to get individual test details
4. Create one TestFileResult per test (or extend structure)

### Option 2: Query SSpec Registry Directly

After test execution, query the test registry for individual test details.

**Pseudocode:**
```rust
// After running test file
let test_results = query_sspec_registry(test_path)?;
for test_result in test_results {
    update_test_result(
        &mut test_db,
        &test_result.id,
        &test_result.name,
        test_result.status,
        // ...
    );
}
```

### Option 3: Use Existing --list Flag

Check if `--list` and `--list-ignored` flags expose individual tests:

```bash
$ ./target/release/simple test --list test/my_spec.spl
$ ./target/release/simple test --list-ignored test/my_spec.spl
```

## Checking Current Capabilities

Let me check what the test runner already supports:

```rust
// From types.rs (modified)
pub struct TestOptions {
    pub list: bool,              // List tests without running
    pub list_ignored: bool,      // List ignored tests only
    pub only_slow: bool,         // Run only slow tests
    pub only_skipped: bool,      // Run only skipped tests
    pub show_tags: bool,         // Show tags in output
    // ...
}
```

These flags suggest per-test information IS available!

## Recommended Approach

### Phase 1: Use --list-ignored to Get Individual Tests

```bash
$ ./target/release/simple test --list-ignored test/my_spec.spl
# Expected output: List of individual ignored tests
```

If this works, we can:
1. Parse the list output
2. Create individual database entries
3. Update status for each test

### Phase 2: Use --format=json for Complete Data

```bash
$ ./target/release/simple test --format=json test/my_spec.spl
```

Parse JSON to get:
- Test name
- Test status (passed/failed/ignored/skipped)
- Test duration
- Test tags
- Error messages

### Phase 3: Create Per-Test Database Entries

Modify `update_test_database()`:

```rust
pub fn update_test_database(
    test_files: &[PathBuf],
    results: &[TestFileResult],
    all_tests_run: bool,
) -> Result<(), String> {
    for (test_path, result) in test_files.iter().zip(results.iter()) {
        // NEW: Get individual test details
        let individual_tests = get_individual_test_results(test_path, result)?;

        for test_result in individual_tests {
            test_db::update_test_result(
                &mut test_db,
                &format!("{}::{}", test_path, test_result.name), // Unique ID
                &test_result.name,
                test_path.to_str().unwrap(),
                &categorize_test(test_path),
                test_result.status,
                test_result.duration_ms,
                test_result.failure,
                all_tests_run,
            );
        }
    }
}
```

## Current Status

- ✅ File-level tracking works
- ✅ Counts (passed, failed, skipped, ignored) are correct
- ❌ Individual test details not captured
- ❌ Can't see which specific tests are ignored

## Next Steps

1. **Test --list-ignored flag:**
   ```bash
   ./target/release/simple test --list-ignored
   ```

2. **Test --format=json flag:**
   ```bash
   ./target/release/simple test --format=json test/integration/spec/runner_spec.spl
   ```

3. **Implement per-test parsing** if JSON format works

4. **Update database schema** to support per-test entries:
   ```
   test_id: "test_file.spl::test_name"  (instead of just file path)
   ```

## Expected Result

After implementation:

```bash
$ cat doc/test/test_db.sdn
tests |test_id, test_name, ..., status, ...|
    test/my_spec.spl::regular passing test, regular passing test, ..., passed, ...
    test/my_spec.spl::first slow test, first slow test, ..., ignored, ...
    test/my_spec.spl::second slow test, second slow test, ..., ignored, ...
    test/my_spec.spl::third slow test, third slow test, ..., ignored, ...
    test/my_spec.spl::fourth slow test, fourth slow test, ..., ignored, ...
```

```bash
$ grep "ignored" doc/test/test_result.md
| 🔕 Ignored | 4 | 57.1% |
```

And we can see individual ignored tests:
```markdown
## 🔕 Ignored Tests (4)

- test/my_spec.spl::first slow test
- test/my_spec.spl::second slow test
- test/my_spec.spl::third slow test
- test/my_spec.spl::fourth slow test
```
