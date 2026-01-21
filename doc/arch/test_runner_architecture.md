# Test Runner Architecture

**Generated:** 2026-01-21
**Version:** 1.0

## Overview

The Simple test runner is a hybrid system that executes both Simple language tests (`.spl` files) and Rust tests, collects results, and updates multiple tracking databases. This document describes the complete architecture, data flow, and database recording mechanisms.

---

## Table of Contents

1. [System Components](#system-components)
2. [Test Types & Status Flow](#test-types--status-flow)
3. [Execution Pipeline](#execution-pipeline)
4. [Data Flow Architecture](#data-flow-architecture)
5. [Database Recording](#database-recording)
6. [Debug Logging Gates](#debug-logging-gates)
7. [Key Implementation Files](#key-implementation-files)

---

## System Components

### High-Level Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                       Test Discovery                         │
│  - Find test files (*.spl, *.rs)                            │
│  - Apply filters (tags, patterns, levels)                   │
└───────────────────┬─────────────────────────────────────────┘
                    │
                    ▼
┌─────────────────────────────────────────────────────────────┐
│                    Test Execution Layer                      │
│  ┌──────────────────┐      ┌──────────────────┐            │
│  │  Simple Tests    │      │   Rust Tests     │            │
│  │  (Interpreter)   │      │   (cargo test)   │            │
│  └────────┬─────────┘      └────────┬─────────┘            │
│           │                         │                        │
│           └─────────┬───────────────┘                        │
└─────────────────────┼──────────────────────────────────────┘
                      │
                      ▼
┌─────────────────────────────────────────────────────────────┐
│                  Result Collection                           │
│  - Parse test output (pass/fail/skip/ignore)                │
│  - Extract timing data                                       │
│  - Capture error messages                                    │
└───────────────────┬─────────────────────────────────────────┘
                    │
                    ▼
┌─────────────────────────────────────────────────────────────┐
│                 Database Update Layer                        │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐      │
│  │  Test DB     │  │  Feature DB  │  │  Bug DB      │      │
│  │  test_db.sdn │  │ feature_db.sdn│  │ bug_db.sdn  │      │
│  └──────────────┘  └──────────────┘  └──────────────┘      │
└───────────────────┬─────────────────────────────────────────┘
                    │
                    ▼
┌─────────────────────────────────────────────────────────────┐
│              Documentation Generation                        │
│  - test_result.md (test results + timing analysis)          │
│  - feature.md (feature status by category)                  │
│  - bug_report.md (known bugs + reproducibility)             │
└─────────────────────────────────────────────────────────────┘
```

---

## Test Types & Status Flow

### Test Result States

| State | Source | Meaning | Database Status |
|-------|--------|---------|----------------|
| **Passed** | Simple/Rust | Test executed successfully | `TestStatus::Passed` |
| **Failed** | Simple/Rust | Test execution failed (assertion/error) | `TestStatus::Failed` |
| **Skipped** | Simple | Not yet implemented (skip tag) | `TestStatus::Skipped` |
| **Ignored** | Simple→Rust | Intentionally disabled (slow_it → #[ignore]) | `TestStatus::Ignored` |
| **Pending** | Simple | No implementation body | `TestStatus::Skipped` |

### How Each Status is Generated

#### 1. Passed Tests
**Simple Tests:**
```
Simple Test File (*.spl)
  ↓
Interpreter executes test
  ↓
No assertions fail, no panics
  ↓
TestResult::mark_passed(duration)
  ↓
TestStatus::Passed in DB
```

**Rust Tests:**
```
Rust Test (in compiler/runtime)
  ↓
cargo test execution
  ↓
Exit code 0
  ↓
TestStatus::Passed in DB
```

#### 2. Failed Tests
**Simple Tests:**
```
Simple Test File (*.spl)
  ↓
Interpreter executes test
  ↓
Assertion fails OR panic occurs
  ↓
TestResult::mark_failed(error_msg, duration)
  ↓
TestStatus::Failed + TestFailure record in DB
```

**Error information captured:**
- `error_message`: Full error text
- `location`: file:line
- `stack_trace`: Call stack (if available)

#### 3. Skipped Tests (Skip Tag)
**Simple Tests:**
```
Test with skip tag in SSpec
  ↓
Example { tags: ["skip"], ... }
  ↓
TestFilter::matches_example() returns false
  ↓
TestResult::mark_skipped()
  ↓
TestStatus::Skipped in DB
```

**Note:** Skipped tests represent **unimplemented features** that should eventually pass.

#### 4. Ignored Tests (slow_it)
**Simple Tests:**
```
slow_it "expensive test": ...
  ↓
SSpec generates Rust with #[ignore] attribute
  ↓
Unless --only-slow flag: skipped at Rust level
  ↓
TestResult::mark_ignored()
  ↓
TestStatus::Ignored in DB
```

**Rust Tests:**
```
#[ignore]
#[test]
fn test_name() { ... }
  ↓
cargo test (without --ignored)
  ↓
Test not executed
  ↓
TestStatus::Ignored in DB
```

---

## Execution Pipeline

### Phase 1: Test Discovery
**File:** `src/rust/driver/src/cli/test_runner/test_discovery.rs`

```rust
fn discover_tests(path: &Path, level: TestLevel) -> Vec<PathBuf>
```

**Steps:**
1. Walk directory tree from `path`
2. Find files matching patterns:
   - `*_spec.spl` (SSpec test files)
   - `*_test.spl` (Simple test files)
3. Apply level filter (unit/integration/system)
4. Return list of test file paths

**Debug checkpoint:** Test file list collected

---

### Phase 2: Test Execution
**File:** `src/rust/driver/src/cli/test_runner/execution.rs`

#### Simple Test Execution

```rust
pub fn run_test_file_with_options(
    runner: &Runner,
    path: &Path,
    options: &TestOptions
) -> TestFileResult
```

**Process:**
1. **Start timer** - `Instant::now()`
2. **Build CLI arguments** from options:
   - `--list` (list mode)
   - `--only-slow` (run slow tests)
   - `--only-skipped` (run skipped tests)
   - `--tag=<tag>` (filter by tag)
3. **Execute via interpreter:**
   ```rust
   runner.run_file_interpreted_with_args(path, args)
   ```
4. **Capture exit code:**
   - Exit code 0 → At least one test passed
   - Exit code != 0 → At least one test failed
5. **Measure duration**
6. **Return TestFileResult:**
   ```rust
   TestFileResult {
       path: PathBuf,
       passed: usize,    // Count of passed tests
       failed: usize,    // Count of failed tests
       skipped: usize,   // Count of skipped tests
       ignored: usize,   // Count of ignored tests
       duration_ms: u64, // Total execution time
       error: Option<String>, // Error if test file failed to run
   }
   ```

**Debug checkpoints:**
- Before execution: Test file path, options
- After execution: Exit code, duration, counts

#### Simple Test Internal Flow (Inside Interpreter)

**File:** `src/lib/std/src/spec/runner/executor.spl`

```
TestExecutor::execute_example(example, group)
  │
  ├─ Check if ignored (example.is_ignored)
  │    ↓ YES → mark_ignored() → return
  │    ↓ NO  → continue
  │
  ├─ Check if should run (filters, tags, slow flag)
  │    ↓ NO  → mark_skipped() → return
  │    ↓ YES → continue
  │
  ├─ Check if pending (no implementation)
  │    ↓ YES → mark_pending() → return
  │    ↓ NO  → continue
  │
  ├─ Execute hooks (before_each)
  │
  ├─ Execute test with error handling
  │    ├─ Start timer
  │    ├─ Run example.run()
  │    ├─ Capture success/failure
  │    └─ Stop timer
  │
  ├─ Update result:
  │    ├─ Success → mark_passed(duration)
  │    └─ Failure → mark_failed(message, duration)
  │
  └─ Execute hooks (after_each)
```

**Debug checkpoints:**
- Test filtering decisions (why skipped/ignored)
- Hook execution
- Test execution start/end
- Result capture

---

### Phase 3: Result Parsing
**File:** `src/rust/driver/src/cli/test_runner/execution.rs`

```rust
pub fn parse_test_output(output: &str) -> (usize, usize, usize, usize)
```

**Input format:**
```
N examples, M failures, P pending, I ignored
```

**Parsing logic:**
1. Find line containing "examples"
2. Extract all numbers from line
3. Parse into: `(total, failed, pending, ignored)`
4. Calculate passed: `total - failed - pending - ignored`

**Example:**
```
Input:  "10 examples, 2 failures, 1 pending, 3 ignored"
Output: (passed=4, failed=2, pending=1, ignored=3)
```

**Debug checkpoint:** Parsed counts vs raw output

---

### Phase 4: Result Aggregation
**File:** `src/rust/driver/src/cli/test_runner/runner.rs`

```rust
fn execute_test_files(...) -> (Vec<TestFileResult>, totals...)
```

**Aggregation:**
```rust
for path in test_files {
    let result = run_test_file_with_options(runner, path, options);

    total_passed  += result.passed;
    total_failed  += result.failed;
    total_skipped += result.skipped;
    total_ignored += result.ignored;

    results.push(result);
}
```

**Debug checkpoint:** Running totals after each file

---

## Data Flow Architecture

### Complete Data Flow Diagram

```
┌─────────────────────────────────────────────────────────────┐
│                     DISCOVERY PHASE                          │
└───────────────────┬─────────────────────────────────────────┘
                    │
                    ▼ test_files: Vec<PathBuf>
┌─────────────────────────────────────────────────────────────┐
│                    EXECUTION PHASE                           │
│                                                              │
│  For each test_file in test_files:                          │
│                                                              │
│  ┌────────────────────────────────────┐                     │
│  │  Simple Test Execution             │                     │
│  │  (Interpreter)                     │                     │
│  │                                    │                     │
│  │  ┌──────────────────────────────┐ │                     │
│  │  │ TestExecutor.run()           │ │                     │
│  │  │   ↓                          │ │                     │
│  │  │ For each example:            │ │                     │
│  │  │   - Check ignore flag        │ │                     │
│  │  │   - Apply filters            │ │                     │
│  │  │   - Execute with timing      │ │                     │
│  │  │   - Capture result           │ │                     │
│  │  │   ↓                          │ │                     │
│  │  │ TestResult {                 │ │                     │
│  │  │   status: Passed/Failed/     │ │                     │
│  │  │           Skipped/Ignored    │ │                     │
│  │  │   duration_ms                │ │                     │
│  │  │   error_message              │ │                     │
│  │  │ }                            │ │                     │
│  │  └──────────────┬───────────────┘ │                     │
│  │                 │                  │                     │
│  │                 ▼ ExecutionResults │                     │
│  │  ┌──────────────────────────────┐ │                     │
│  │  │ Format output:               │ │                     │
│  │  │ "N examples, M failures,     │ │                     │
│  │  │  P pending, I ignored"       │ │                     │
│  │  └──────────────┬───────────────┘ │                     │
│  └─────────────────┼──────────────────┘                     │
│                    │                                         │
│                    ▼ Output string                           │
│  ┌────────────────────────────────────┐                     │
│  │  Rust Driver Layer                 │                     │
│  │  (execution.rs)                    │                     │
│  │                                    │                     │
│  │  parse_test_output(output)         │                     │
│  │    ↓                               │                     │
│  │  TestFileResult {                  │                     │
│  │    path,                           │                     │
│  │    passed: usize,                  │                     │
│  │    failed: usize,                  │                     │
│  │    skipped: usize,                 │                     │
│  │    ignored: usize,                 │                     │
│  │    duration_ms: u64,               │                     │
│  │    error: Option<String>           │                     │
│  │  }                                 │                     │
│  └────────────────┬───────────────────┘                     │
│                   │                                          │
└───────────────────┼──────────────────────────────────────────┘
                    │
                    ▼ results: Vec<TestFileResult>
┌─────────────────────────────────────────────────────────────┐
│                  DATABASE UPDATE PHASE                       │
│                                                              │
│  ┌──────────────────────────────────────────────┐           │
│  │  test_db_update::update_test_database()      │           │
│  │                                              │           │
│  │  For each (test_path, result):              │           │
│  │    - Create test_id from path               │           │
│  │    - Categorize test (unit/integration/sys) │           │
│  │    - Convert to database types:             │           │
│  │                                              │           │
│  │      convert_result_to_db(result)           │           │
│  │        ↓                                     │           │
│  │      if result.error.is_some():             │           │
│  │        → (Failed, TestFailure {...})        │           │
│  │      elif result.failed > 0:                │           │
│  │        → (Failed, TestFailure {...})        │           │
│  │      elif result.ignored > 0:               │           │
│  │        → (Ignored, None)                    │           │
│  │      elif result.passed > 0:                │           │
│  │        → (Passed, None)                     │           │
│  │      else:                                  │           │
│  │        → (Skipped, None)                    │           │
│  │                                              │           │
│  │    - Update or insert record:               │           │
│  │      test_db::update_test_result(           │           │
│  │        db, test_id, name, file, category,   │           │
│  │        status, duration, failure, ...       │           │
│  │      )                                       │           │
│  └──────────────────┬───────────────────────────┘           │
│                     │                                        │
│                     ▼ Updated TestDb                         │
│  ┌──────────────────────────────────────────────┐           │
│  │  test_db::save_test_db()                     │           │
│  │    ↓                                         │           │
│  │  Serialize to SDN format:                    │           │
│  │    tests |test_id, status, duration, ...|    │           │
│  │        test_001, passed, 45.2, ...          │           │
│  │        test_002, failed, 12.1, ...          │           │
│  │    ↓                                         │           │
│  │  Write to: doc/test/test_db.sdn             │           │
│  └──────────────────┬───────────────────────────┘           │
│                     │                                        │
│  ┌──────────────────▼───────────────────────────┐           │
│  │  feature_db::update_feature_database()       │           │
│  │    ↓                                         │           │
│  │  - Filter SSpec files (*_spec.spl)          │           │
│  │  - Extract feature definitions from tests    │           │
│  │  - Link to test results (pass/fail)         │           │
│  │  - Write to: doc/feature/feature_db.sdn     │           │
│  └──────────────────┬───────────────────────────┘           │
│                     │                                        │
└─────────────────────┼────────────────────────────────────────┘
                      │
                      ▼
┌─────────────────────────────────────────────────────────────┐
│             DOCUMENTATION GENERATION PHASE                   │
│                                                              │
│  ┌──────────────────────────────────────────────┐           │
│  │  test_db::generate_test_result_docs()        │           │
│  │    ↓                                         │           │
│  │  Generate from TestDb:                       │           │
│  │    - Summary (passed/failed/skipped/ignored) │           │
│  │    - Failed tests with details               │           │
│  │    - Timing analysis (regressions, variance) │           │
│  │    - Action items                            │           │
│  │    ↓                                         │           │
│  │  Write to: doc/test/test_result.md          │           │
│  └──────────────────────────────────────────────┘           │
│                                                              │
│  ┌──────────────────────────────────────────────┐           │
│  │  feature_db::generate_feature_docs()         │           │
│  │    ↓                                         │           │
│  │  Generate from FeatureDb:                    │           │
│  │    - Feature index by category               │           │
│  │    - Pending features (failed/in_progress)   │           │
│  │    - Per-category feature lists              │           │
│  │    ↓                                         │           │
│  │  Write to: doc/feature/*.md                 │           │
│  └──────────────────────────────────────────────┘           │
└─────────────────────────────────────────────────────────────┘
```

---

## Database Recording

### Test Database (test_db.sdn)

**Location:** `doc/test/test_db.sdn`
**Updated:** Every test run
**Implementation:** `src/rust/driver/src/test_db.rs`

#### Record Structure

```rust
pub struct TestRecord {
    // Identification
    pub test_id: String,         // Unique ID (file path)
    pub test_name: String,        // Display name
    pub test_file: String,        // Source file path
    pub category: String,         // Unit/Integration/System

    // Status
    pub status: TestStatus,       // Passed/Failed/Skipped/Ignored
    pub last_run: String,         // ISO 8601 timestamp

    // Failure information
    pub failure: Option<TestFailure>,

    // Execution history
    pub execution_history: ExecutionHistory,

    // Timing statistics
    pub timing: TimingData,

    // Links
    pub related_bugs: Vec<String>,
    pub related_features: Vec<String>,

    // Metadata
    pub tags: Vec<String>,
    pub valid: bool,
}
```

#### Update Process

```rust
pub fn update_test_result(
    db: &mut TestDb,
    test_id: &str,
    test_name: &str,
    test_file: &str,
    category: &str,
    status: TestStatus,
    duration_ms: f64,
    failure: Option<TestFailure>,
    all_tests_run: bool,
)
```

**Steps:**
1. **Find or create record** - `db.records.entry(test_id)`
2. **Update status** - `test.status = status`
3. **Update execution history:**
   - Increment `total_runs`
   - Increment `passed` or `failed` counter
   - Add to `last_10_runs` (circular buffer)
   - Calculate `failure_rate_pct`
   - Detect flaky tests
4. **Update timing data:**
   - Add run to `history.runs` (circular buffer)
   - Detect outliers (MAD/IQR/ZScore)
   - Compute statistics (median, mean, std_dev, percentiles)
   - Update baseline if significant change
5. **Set failure info** - if status == Failed
6. **Mark valid** - `test.valid = true`

**Debug checkpoints:**
- Record lookup (new vs existing)
- Status transition
- History update
- Timing update
- Baseline recalculation

---

### Feature Database (feature_db.sdn)

**Location:** `doc/feature/feature_db.sdn`
**Updated:** Every test run
**Implementation:** `src/rust/driver/src/feature_db.rs`

#### Update Process

```rust
pub fn update_feature_database(
    test_files: &[PathBuf],
    results: &mut Vec<TestFileResult>,
    total_failed: &mut usize,
)
```

**Steps:**
1. **Filter SSpec files** - `test_files.filter(|p| p.ends_with("_spec.spl"))`
2. **Identify failed specs** - `results.filter(|r| r.failed > 0)`
3. **Call unified update:**
   ```rust
   crate::feature_db::update_feature_db_from_sspec(
       &feature_db_path,
       &sspec_files,
       &failed_specs
   )
   ```
4. **Extract features from SSpec files:**
   - Parse `feature "name": ...` blocks
   - Extract scenarios and examples
   - Link to test results
5. **Update feature status:**
   - All tests pass → `FeatureStatus::Complete`
   - Some tests fail → `FeatureStatus::InProgress`
   - No tests → `FeatureStatus::Planned`
6. **Write to database**

**Debug checkpoints:**
- SSpec file filtering
- Feature extraction
- Status determination
- Database write

---

### Bug Database (bug_db.sdn)

**Location:** `doc/bug/bug_db.sdn`
**Updated:** Manual (via `simple bug-add`)
**Implementation:** `src/rust/driver/src/bug_db.rs`

#### Record Structure

```rust
pub struct BugRecord {
    pub bug_id: String,
    pub title: String,
    pub status: BugStatus,              // Open/InProgress/Fixed/Closed
    pub priority: Priority,             // P0/P1/P2/P3
    pub severity: Severity,             // Critical/Major/Minor/Trivial
    pub reproducible_by: Vec<String>,   // REQUIRED: Test IDs
    pub timing_impact: Option<TimingImpact>,
    pub build_impact: Option<BuildImpact>,
    pub related_tests: Vec<String>,
    pub resolution: Option<BugResolution>,
}
```

**Linking to Tests:**
- Bug MUST have `reproducible_by` test IDs
- Tests can have `related_bugs` pointing to bug IDs
- Bidirectional linkage for traceability

**Debug checkpoints:**
- Bug creation with test links
- Status transitions
- Resolution recording

---

## Debug Logging Gates

### Log Levels

```rust
// Define in src/rust/driver/src/cli/test_runner/types.rs
pub enum DebugLevel {
    None,      // No debug output
    Basic,     // High-level phases
    Detailed,  // Per-test information
    Trace,     // Full data flow
}
```

### Environment Variable

```bash
export SIMPLE_TEST_DEBUG=trace  # none/basic/detailed/trace
```

### Debug Logging Checkpoints

#### Phase 1: Discovery
```rust
[DEBUG:Discovery] Found 142 test files in test/
[DEBUG:Discovery]   Unit tests: 98
[DEBUG:Discovery]   Integration tests: 44
[DEBUG:Discovery] Applied filters:
[DEBUG:Discovery]   - Tag filter: integration
[DEBUG:Discovery]   - Result: 44 files to run
```

#### Phase 2: Execution
```rust
[DEBUG:Execution] Running test: test/integration/api_spec.spl
[DEBUG:Execution]   Options: --tag=integration
[DEBUG:Execution]   Start time: 2026-01-21T10:30:45Z
[DEBUG:Execution]   Exit code: 0
[DEBUG:Execution]   Duration: 234ms
[DEBUG:Execution]   Raw output: "15 examples, 0 failures, 2 pending, 0 ignored"
[DEBUG:Execution]   Parsed: passed=13, failed=0, pending=2, ignored=0
```

#### Phase 3: Result Collection
```rust
[DEBUG:Collection] Aggregating results from 44 files
[DEBUG:Collection]   Total passed: 582
[DEBUG:Collection]   Total failed: 3
[DEBUG:Collection]   Total skipped: 45
[DEBUG:Collection]   Total ignored: 12
```

#### Phase 4: Database Update
```rust
[DEBUG:TestDB] Updating test database: doc/test/test_db.sdn
[DEBUG:TestDB]   Test: test/integration/api_spec.spl
[DEBUG:TestDB]     Status: Passed → Passed (no change)
[DEBUG:TestDB]     Duration: 234ms (baseline: 220ms, +6.4%)
[DEBUG:TestDB]     Execution history: 47 runs, 46 passed, 1 failed (2.1% failure rate)
[DEBUG:TestDB]     Flaky: No
[DEBUG:TestDB]     Timing: Updated baseline (significant change: 6.4%)
[DEBUG:TestDB]   Written 142 records to database

[DEBUG:FeatureDB] Updating feature database: doc/feature/feature_db.sdn
[DEBUG:FeatureDB]   Found 87 SSpec files
[DEBUG:FeatureDB]   Extracted 234 features
[DEBUG:FeatureDB]   Feature status:
[DEBUG:FeatureDB]     Complete: 187 (79.9%)
[DEBUG:FeatureDB]     InProgress: 32 (13.7%)
[DEBUG:FeatureDB]     Planned: 15 (6.4%)
[DEBUG:FeatureDB]   Written to database
```

#### Phase 5: Documentation Generation
```rust
[DEBUG:DocGen] Generating test result documentation
[DEBUG:DocGen]   Source: doc/test/test_db.sdn (142 records)
[DEBUG:DocGen]   Output: doc/test/test_result.md
[DEBUG:DocGen]   Sections:
[DEBUG:DocGen]     - Summary (pass/fail/skip/ignore counts)
[DEBUG:DocGen]     - Failed tests: 3
[DEBUG:DocGen]     - Performance regressions: 5
[DEBUG:DocGen]     - High variance tests: 8
[DEBUG:DocGen]     - Action items: 3
[DEBUG:DocGen]   Written 2,847 lines
```

### Implementation Location

Debug logs will be added to these files:
- `src/rust/driver/src/cli/test_runner/runner.rs`
- `src/rust/driver/src/cli/test_runner/execution.rs`
- `src/rust/driver/src/cli/test_runner/test_db_update.rs`
- `src/rust/driver/src/test_db.rs`
- `src/rust/driver/src/feature_db.rs`

---

## Key Implementation Files

### Rust Driver Layer

| File | Purpose | Key Functions |
|------|---------|--------------|
| `types.rs` | Data structures | `TestOptions`, `TestFileResult`, `TestRunResult` |
| `runner.rs` | Main orchestration | `run_tests()`, `execute_test_files()` |
| `execution.rs` | Test execution | `run_test_file_with_options()`, `parse_test_output()` |
| `test_db_update.rs` | DB updates | `update_test_database()`, `convert_result_to_db()` |
| `feature_db.rs` | Feature tracking | `update_feature_database()` |
| `test_discovery.rs` | File discovery | `discover_tests()`, `matches_tag()` |

### Database Layer

| File | Purpose | Key Functions |
|------|---------|--------------|
| `test_db.rs` | Test tracking | `load_test_db()`, `save_test_db()`, `update_test_result()` |
| `feature_db.rs` | Feature tracking | `load_feature_db()`, `update_feature_db_from_sspec()` |
| `bug_db.rs` | Bug tracking | `load_bug_db()`, `save_bug_db()`, linkage to tests |
| `unified_db.rs` | Cross-DB queries | Unified views across all databases |

### Simple Language Layer

| File | Purpose | Key Classes |
|------|---------|------------|
| `spec/runner/executor.spl` | Test execution | `TestExecutor`, `TestResult`, `ExecutionResults` |
| `spec/runner/cli.spl` | CLI interface | `TestCli`, argument parsing |
| `spec/registry.spl` | Test registration | `ExampleGroup`, `Example`, global registry |
| `spec/dsl.spl` | Test DSL | `it()`, `slow_it()`, `describe()`, expectations |

---

## Summary

The test runner is a **multi-layered architecture** that:

1. **Discovers** tests from the filesystem
2. **Executes** them via interpreter or cargo test
3. **Collects** results with detailed status (Passed/Failed/Skipped/Ignored)
4. **Records** results in three specialized databases (test/feature/bug)
5. **Generates** documentation automatically

**Key insight:** Test status flows through multiple transformations:
- Simple language level: `TestStatus` enum in executor
- Rust driver level: `TestFileResult` with counts
- Database level: `TestRecord` with full history

**Debug logging** traces this flow at configurable levels (none/basic/detailed/trace), making it easy to diagnose issues in test execution, result parsing, or database recording.

---

**Next Steps:**
1. Implement debug logging with environment variable gate
2. Add timing instrumentation for each phase
3. Create database integrity checks
4. Add visualization of data flow in dashboard
