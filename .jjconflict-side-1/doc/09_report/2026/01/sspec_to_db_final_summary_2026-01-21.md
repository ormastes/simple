# SSpec to Database Integration - Final Summary

## Date: 2026-01-21

## Question: How does database data come from SSpec tests?

### Answer: File-Level Tracking (Current Implementation)

Currently, the database tracks **ONE entry per test FILE**, not per individual test.

## Data Flow Diagram

```
SSpec Test File
    ↓
Contains: 3 passing tests + 4 ignore_it tests with "slow"
    ↓
Simple Test Runner executes file
    ↓
SSpec outputs: "7 examples, 0 failures, 0 pending, 4 ignored"
    ↓
Rust parser: parse_test_output() → (passed=3, failed=0, skipped=0, ignored=4)
    ↓
Creates: TestFileResult { passed: 3, failed: 0, skipped: 0, ignored: 4, ... }
    ↓
convert_result_to_db() checks priority:
  - If failed > 0 → TestStatus::Failed
  - Else if ignored > 0 → TestStatus::Ignored  ✅
  - Else if passed > 0 → TestStatus::Passed
  - Else if skipped > 0 → TestStatus::Skipped
    ↓
Creates ONE database entry:
  test_id: "test/my_spec.spl"
  status: "ignored"
  (ignored field: 4)
    ↓
Saved to: doc/test/test_db.sdn
```

## Current Behavior

### What We Get:
```sdn
tests |test_id, ..., status, ...|
    test/my_spec.spl, my_spec, ..., ignored, ...
```

**ONE row** for the entire file, with status = "ignored" because `ignored > 0`.

### What We DON'T Get:
- Individual test names
- Which specific tests are ignored
- Per-test timing
- Per-test failure details

## Why Only File-Level Tracking?

### Code Evidence (test_db_update.rs:11-53)

```rust
pub fn update_test_database(
    test_files: &[PathBuf],        // Array of FILE paths
    results: &[TestFileResult],    // One result PER FILE
    all_tests_run: bool,
) -> Result<(), String> {
    // Loop over FILES
    for (test_path, result) in test_files.iter().zip(results.iter()) {
        let test_id = test_path.to_str().unwrap();  // File path as ID
        let test_name = test_path.file_stem().unwrap();  // File name

        // Create ONE entry per file
        test_db::update_test_result(
            &mut test_db,
            &test_id,      // e.g., "test/my_spec.spl"
            &test_name,    // e.g., "my_spec"
            // ...
        );
    }
}
```

**Key:** The function iterates over `test_files` (file paths), not individual tests.

## What Would Need to Change for Per-Test Tracking

### Option 1: Use --list-ignored Flag ✅ (Available)

New CLI flags added to `TestOptions`:
- `--list`: List tests without running
- `--list-ignored`: List ignored tests only
- `--only-slow`: Run only slow tests
- `--only-skipped`: Run only skipped tests
- `--show-tags`: Show tags in output

**Usage:**
```bash
$ ./target/release/simple test --list-ignored test/my_spec.spl
# Expected: List of individual ignored test names
```

**Implementation needed:**
1. Run test file with `--list-ignored`
2. Parse output to get individual test names
3. Create separate database entries for each test

### Option 2: Use --format=json ✅ (Exists in SSpec)

SSpec has JSON formatter (`formatters/json.spl`):

```bash
$ ./target/release/simple test --format=json test/my_spec.spl
```

**Expected output:**
```json
{
  "tests": [
    {"name": "regular passing test", "status": "passed", "duration_ms": 5},
    {"name": "first slow test", "status": "ignored", "duration_ms": 0},
    {"name": "second slow test", "status": "ignored", "duration_ms": 0},
    ...
  ],
  "summary": {"total": 7, "passed": 3, "ignored": 4}
}
```

**Advantage:** Complete per-test data in structured format.

### Option 3: Modify parse_test_output() to Parse Test Names

Currently parses:
```
"7 examples, 0 failures, 0 pending, 4 ignored"
```

Could parse individual test lines if SSpec outputs them:
```
✓ regular passing test
✓ another passing test
○ first slow test (ignored)
○ second slow test (ignored)
...
7 examples, 0 failures, 0 pending, 4 ignored
```

## Recommended Solution

### Phase 1: Use --list-ignored (Quickest)

```rust
// In test_db_update.rs
pub fn update_test_database_with_individual_tests(
    test_files: &[PathBuf],
    results: &[TestFileResult],
    runner: &Runner,  // NEW: Need runner to list tests
) -> Result<(), String> {
    for (test_path, result) in test_files.iter().zip(results.iter()) {
        if result.ignored > 0 {
            // Get individual ignored test names
            let ignored_tests = runner.list_ignored_tests(test_path)?;

            for test_name in ignored_tests {
                test_db::update_test_result(
                    &mut test_db,
                    &format!("{}::{}", test_path, test_name),  // Unique ID
                    &test_name,
                    test_path.to_str().unwrap(),
                    &categorize_test(test_path),
                    TestStatus::Ignored,
                    0.0,  // No duration for ignored tests
                    None,
                    all_tests_run,
                );
            }
        }

        // Similar for passed, failed, skipped...
    }
}
```

### Phase 2: Use JSON Format (Best Long-term)

```rust
pub fn update_test_database_from_json(
    test_files: &[PathBuf],
    runner: &Runner,
) -> Result<(), String> {
    for test_path in test_files {
        // Run with JSON output
        let json_output = runner.run_with_json_format(test_path)?;
        let test_results: TestResults = serde_json::from_str(&json_output)?;

        for test in test_results.tests {
            test_db::update_test_result(
                &mut test_db,
                &format!("{}::{}", test_path, test.name),
                &test.name,
                test_path.to_str().unwrap(),
                &categorize_test(test_path),
                convert_status(&test.status),
                test.duration_ms,
                test.failure,
                all_tests_run,
            );
        }
    }
}
```

## Expected Result After Implementation

### Database (doc/test/test_db.sdn):
```sdn
tests |test_id, test_name, test_file, category, status, ...|
    test/my_spec.spl::regular passing test, regular passing test, test/my_spec.spl, Unit, passed, ...
    test/my_spec.spl::another passing test, another passing test, test/my_spec.spl, Unit, passed, ...
    test/my_spec.spl::final passing test, final passing test, test/my_spec.spl, Unit, passed, ...
    test/my_spec.spl::first slow test, first slow test, test/my_spec.spl, Unit, ignored, ...
    test/my_spec.spl::second slow test, second slow test, test/my_spec.spl, Unit, ignored, ...
    test/my_spec.spl::third slow test, third slow test, test/my_spec.spl, Unit, ignored, ...
    test/my_spec.spl::fourth slow test, fourth slow test, test/my_spec.spl, Unit, ignored, ...
```

**7 rows** - one per individual test

### Report (doc/test/test_result.md):
```markdown
## 🔕 Ignored Tests (4)

| Test Name | File | Category |
|-----------|------|----------|
| first slow test | test/my_spec.spl | Unit |
| second slow test | test/my_spec.spl | Unit |
| third slow test | test/my_spec.spl | Unit |
| fourth slow test | test/my_spec.spl | Unit |
```

## Current Status

- ✅ **Infrastructure:** Complete (ignored field, parsing, TestStatus::Ignored)
- ✅ **File-level tracking:** Works (one entry per file with ignored count)
- ❌ **Per-test tracking:** Not implemented (need to parse individual tests)
- ✅ **CLI flags:** Available (--list-ignored, --format=json)
- ⏳ **Integration:** Needs implementation

## Next Steps

1. **Test --list-ignored flag:**
   ```bash
   ./target/release/simple test --list-ignored test/integration/spec/runner_spec.spl
   ```

2. **Parse output** to extract individual test names

3. **Modify update_test_database()** to create per-test entries

4. **Alternative:** Use --format=json for complete structured data

## Summary

**How data flows from SSpec to DB:**
1. SSpec outputs test summary: "N examples, M failures, P pending, I ignored"
2. Rust parses counts into TestFileResult
3. convert_result_to_db() maps to TestStatus based on priority
4. ONE database entry created per file (not per test)
5. Status = "ignored" if any tests were ignored

**To get 4 individual ignored tests in DB:**
- Need to parse individual test names (using --list-ignored or --format=json)
- Create separate database entries for each test
- Use test_id format: "file_path::test_name"

**Current limitation:**
- Database shows file has ignored tests
- Database does NOT show which specific 4 tests are ignored
- This requires parsing individual test output, not just summary counts
