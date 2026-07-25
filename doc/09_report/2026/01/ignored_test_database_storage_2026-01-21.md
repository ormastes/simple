# Ignored Test Database Storage Analysis

**Date:** 2026-01-21
**Question:** Are long/slow tests (slow_it) and ignored tests (ignore_it) stored in the database?
**Answer:** **YES** - Both types are stored with `status="ignored"` in `test_db.sdn`

---

## Data Flow: Test Execution → Database

### Complete Flow Diagram

```
┌─────────────────────────────────────────────────────────────┐
│  1. Simple Language Layer (Test Definition)                 │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  ignore_it "disabled test":      slow_it "long test":       │
│      pass                             pass                   │
│      ↓                                ↓                      │
│  Example.ignore()              Example.slow()               │
│  is_ignored = true             tags.push("slow")            │
│                                is_ignored = false            │
└───────────────────┬─────────────────────────────────────────┘
                    │
                    ▼
┌─────────────────────────────────────────────────────────────┐
│  2. Test Execution (executor.spl)                           │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  execute_example(example, group):                           │
│      if example.is_ignored:                                 │
│          result.mark_ignored()  ────────┐                   │
│          return result                  │                   │
│                                         │                   │
│      if not example.should_run():       │                   │
│          result.mark_skipped()  ────────┼──────┐            │
│          return result                  │      │            │
│                                         │      │            │
│      # Run the test                     │      │            │
│      if success:                        │      │            │
│          result.mark_passed()  ─────────┼──────┼───┐        │
│      else:                              │      │   │        │
│          result.mark_failed()  ─────────┼──────┼───┼───┐    │
│                                         │      │   │   │    │
└─────────────────────────────────────────┼──────┼───┼───┼────┘
                                          │      │   │   │
                    ┌─────────────────────┘      │   │   │
                    │     ┌──────────────────────┘   │   │
                    │     │     ┌────────────────────┘   │
                    │     │     │     ┌──────────────────┘
                    ▼     ▼     ▼     ▼
┌─────────────────────────────────────────────────────────────┐
│  3. Result Aggregation (ExecutionResults)                   │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  ignored_count() = results.filter(\r: r.is_ignored()).len() │
│  passed_count()  = results.filter(\r: r.is_passed()).len()  │
│  failed_count()  = results.filter(\r: r.is_failed()).len()  │
│  pending_count() = results.filter(\r: r.is_pending()).len() │
│                                                              │
│  summary():                                                  │
│      "Finished in {duration}s"                              │
│      "{total} examples, {failed} failures,                  │
│       {pending} pending, {ignored} ignored"                 │
│                                                              │
└───────────────────┬─────────────────────────────────────────┘
                    │
                    ▼ Output string
┌─────────────────────────────────────────────────────────────┐
│  4. Rust Driver (execution.rs)                              │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  parse_test_output(output):                                 │
│      Extract: "N examples, M failures, P pending, I ignored"│
│      ↓                                                       │
│      numbers = [N, M, P, I]                                 │
│      total = N                                              │
│      failed = M                                             │
│      pending = P                                            │
│      ignored = I  ◄── CAPTURED HERE                         │
│      passed = N - M - P - I                                 │
│                                                              │
│  TestFileResult {                                           │
│      path,                                                  │
│      passed,                                                │
│      failed,                                                │
│      skipped: pending,                                      │
│      ignored: I,  ◄── STORED HERE                           │
│      duration_ms,                                           │
│      error                                                  │
│  }                                                          │
│                                                              │
└───────────────────┬─────────────────────────────────────────┘
                    │
                    ▼ TestFileResult
┌─────────────────────────────────────────────────────────────┐
│  5. Database Update (test_db_update.rs)                     │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  convert_result_to_db(result):                              │
│      if result.error.is_some():                             │
│          return (TestStatus::Failed, failure_info)          │
│      elif result.failed > 0:                                │
│          return (TestStatus::Failed, failure_info)          │
│      elif result.ignored > 0:  ◄── CHECK HERE               │
│          return (TestStatus::Ignored, None)  ◄── SET STATUS │
│      elif result.passed > 0:                                │
│          return (TestStatus::Passed, None)                  │
│      elif result.skipped > 0:                               │
│          return (TestStatus::Skipped, None)                 │
│      else:                                                  │
│          return (TestStatus::Skipped, None)                 │
│                                                              │
└───────────────────┬─────────────────────────────────────────┘
                    │
                    ▼ (TestStatus::Ignored, None)
┌─────────────────────────────────────────────────────────────┐
│  6. Database Storage (test_db.rs)                           │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  update_test_result(db, test_id, ..., status, ...):        │
│      test.status = status  ◄── Set to TestStatus::Ignored  │
│      test.execution_history.total_runs += 1                │
│      match status:                                          │
│          TestStatus::Passed => history.passed += 1          │
│          TestStatus::Failed => history.failed += 1          │
│          _ => {}  ◄── Ignored not counted in pass/fail     │
│                                                              │
│      run_result = match status:                             │
│          TestStatus::Ignored => "ignore"                    │
│          ...                                                │
│      history.last_10_runs.insert(0, run_result)            │
│                                                              │
│  save_test_db(path, db):                                   │
│      Serialize to SDN format:                               │
│          tests |test_id, ..., status, ...|                  │
│              test_001, ..., ignored, ...  ◄── WRITTEN HERE  │
│                                                              │
└───────────────────┬─────────────────────────────────────────┘
                    │
                    ▼ doc/test/test_db.sdn
┌─────────────────────────────────────────────────────────────┐
│  7. Documentation Generation (test_db.rs)                   │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  generate_test_result_docs(db, output_dir):                │
│      Count by status:                                       │
│          ignored = records.filter(|t|                       │
│              t.status == TestStatus::Ignored).count()       │
│                                                              │
│      Write to doc/test/test_result.md:                     │
│          ## Summary                                         │
│          | Status | Count | Percentage |                   │
│          | 🔕 Ignored | {ignored} | {pct}% |  ◄── DISPLAYED │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

---

## Database Schema

### TestRecord Structure

```rust
pub struct TestRecord {
    pub test_id: String,
    pub test_name: String,
    pub test_file: String,
    pub category: String,

    // Status stored here
    pub status: TestStatus,  // Passed | Failed | Skipped | Ignored
    pub last_run: String,

    pub execution_history: ExecutionHistory {
        total_runs: usize,
        passed: usize,
        failed: usize,
        last_10_runs: Vec<String>,  // ["ignore", "pass", "fail", ...]
        flaky: bool,
        failure_rate_pct: f64,
    },

    // ... timing, links, etc.
}
```

### TestStatus Enum

```rust
pub enum TestStatus {
    Passed,
    Failed,
    Skipped,
    Ignored,  // ◄── Used for both slow_it and ignore_it
}
```

### SDN File Format

**File:** `doc/test/test_db.sdn`

```sdn
tests |test_id, test_name, test_file, category, status, last_run, ...|
    test/lib/std/unit/verification/regeneration_spec.spl, regeneration_spec, test/lib/std/unit/verification/regeneration_spec.spl, Unit, ignored, 2026-01-21T10:30:00Z, ...
    test/01_unit/spec/dsl_spec.spl, dsl_spec, test/01_unit/spec/dsl_spec.spl, Unit, ignored, 2026-01-21T10:31:00Z, ...
```

---

## Key Behaviors

### 1. Both slow_it and ignore_it Result in TestStatus::Ignored

**ignore_it:**
```simple
ignore_it "intentionally disabled":
    expect(broken()).to work()
```
- Sets `example.is_ignored = true`
- **Never runs** (skipped at execution time)
- Counted in `ignored_count()`
- Database: `status="ignored"`

**slow_it:**
```simple
slow_it "takes 5 minutes":
    benchmark_heavy_operation()
```
- Adds "slow" tag
- **Skipped by default** (unless `--only-slow` flag)
- When skipped, counted in `ignored_count()`
- Database: `status="ignored"` (when not run)

### 2. File-Level Status Priority

The `convert_result_to_db()` function uses priority order:

```rust
if result.error.is_some()    → TestStatus::Failed
elif result.failed > 0        → TestStatus::Failed
elif result.ignored > 0       → TestStatus::Ignored  ◄── HERE
elif result.passed > 0        → TestStatus::Passed
elif result.skipped > 0       → TestStatus::Skipped
else                          → TestStatus::Skipped
```

**Important:** The entire test **file** gets one status, not individual tests.

**Example:**
```simple
describe "Mixed Tests":
    it "passes":               # Passed
        expect(1).to eq(1)

    ignore_it "disabled":      # Ignored
        pass

    slow_it "slow test":       # Ignored (if not running slow tests)
        pass
```

**Result:**
- If slow tests are NOT run: `result.ignored = 2` → File status = `Ignored`
- If slow tests ARE run: `result.passed = 2, result.ignored = 1` → File status = `Ignored` (still!)

This means **ignored tests take precedence over passed tests** in file status.

### 3. Execution History Tracking

When a test is marked `Ignored`:

```rust
test.execution_history.total_runs += 1
// But NOT incremented:
// test.execution_history.passed
// test.execution_history.failed

test.execution_history.last_10_runs.insert(0, "ignore")
```

**Last 10 runs might look like:**
```
["ignore", "ignore", "pass", "pass", "ignore", "pass", "fail", "pass", "pass", "pass"]
```

**Flaky detection:** Ignored runs are NOT considered in flaky test detection (only pass/fail).

### 4. Documentation Display

**doc/test/test_result.md:**

```markdown
## Summary

| Status | Count | Percentage |
|--------|-------|-----------|
| ✅ Passed | 582 | 73.6% |
| ❌ Failed | 3 | 0.4% |
| ⏭️ Skipped | 203 | 25.7% |
| 🔕 Ignored | 2 | 0.3% |

## 🔕 Ignored Tests

Tests that are intentionally disabled (ignore_it) or slow (slow_it):
- test/lib/std/unit/verification/regeneration_spec.spl
- test/01_unit/spec/dsl_spec.spl
```

---

## When Are Tests NOT Stored as Ignored?

### Case 1: slow_it Tests Run with --only-slow

```bash
./target/debug/simple test --only-slow
```

- `slow_it` tests **run normally**
- Results are `passed` or `failed`, not `ignored`
- Database: `status="passed"` or `status="failed"`

### Case 2: Mixed File with Failures

```simple
describe "Tests":
    it "fails":
        expect(1).to eq(2)  # FAILS

    ignore_it "disabled":
        pass
```

**Result:**
- `result.failed = 1, result.ignored = 1`
- File status = `Failed` (failure takes precedence)
- Database: `status="failed"`

---

## Checking Database Contents

### Query Ignored Tests

```bash
# Check test_db.sdn for ignored tests
grep -E "^\s+.*ignored" doc/test/test_db.sdn

# Count ignored tests
grep -E "^\s+.*ignored" doc/test/test_db.sdn | wc -l

# View test result summary
head -50 doc/test/test_result.md | grep -A 10 "Summary"
```

### Example Query Result

```sdn
tests |test_id, test_name, test_file, category, status, ...|
    test/lib/std/unit/verification/regeneration_spec.spl, regeneration_spec, test/lib/std/unit/verification/regeneration_spec.spl, Unit, ignored, 2026-01-21T10:30:45.123Z, "", "{\"total_runs\":5,\"passed\":0,\"failed\":0,\"last_10_runs\":[\"ignore\",\"ignore\",\"ignore\",\"ignore\",\"ignore\"],\"flaky\":false,\"failure_rate_pct\":0.0}", ...
```

---

## Debug Logging

With `SIMPLE_TEST_DEBUG=detailed`, you'll see:

```
[DEBUG:Execution] Running test: test/lib/std/unit/verification/regeneration_spec.spl
[DEBUG:Execution]   Exit code: 0
[DEBUG:Execution]   Duration: 234ms
[DEBUG:Parsing] Found summary line: "5 examples, 0 failures, 0 pending, 3 ignored"
[DEBUG:Parsing] Parsed counts: total=5, passed=2, failed=0, pending=0, ignored=3
[DEBUG:TestDB]     Test: test/lib/std/unit/verification/regeneration_spec.spl
[DEBUG:TestDB]       Status transition: Passed -> Ignored
[DEBUG:TestDB]       Execution history: 5 runs, 0 passed, 0 failed (0.0% failure rate)
[DEBUG:TestDB]       Note: Ignored runs not counted in pass/fail
```

---

## Summary

**Q: Are long/slow tests (slow_it) stored in the database?**
**A: YES** - When not run (default behavior), they're stored with `status="ignored"`

**Q: Are ignore_it tests stored in the database?**
**A: YES** - They're always stored with `status="ignored"` (never run)

**Q: Can I query the database to see all ignored tests?**
**A: YES** - Search `doc/test/test_db.sdn` for `status` field containing "ignored"

**Q: Does the database distinguish between slow_it and ignore_it?**
**A: NO** - Both use the same `TestStatus::Ignored`. However, the `tags` field in the test record would show "slow" for `slow_it` tests.

**Q: What about execution history?**
**A: YES** - The `last_10_runs` field tracks "ignore" status, so you can see historical patterns like `["ignore", "ignore", "pass", "ignore", ...]`

---

## Related Files

- **Status Enum**: `src/rust/driver/src/test_db.rs:105`
- **Database Storage**: `src/rust/driver/src/test_db.rs:404` (serialize), `:328` (parse)
- **Result Conversion**: `src/rust/driver/src/cli/test_runner/test_db_update.rs:113-115`
- **Output Parsing**: `src/rust/driver/src/cli/test_runner/execution.rs:112`
- **Summary Generation**: `src/lib/std/src/spec/runner/executor.spl:179`
- **Documentation**: `src/rust/driver/src/test_db.rs:701,738`
