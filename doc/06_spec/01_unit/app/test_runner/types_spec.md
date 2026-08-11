# Types Specification

> <details>

<!-- sdn-diagram:id=types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

types_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 34 | 34 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Types Specification

## Scenarios

### TestExecutionMode

#### creates Interpreter variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = TestExecutionMode.Interpreter
expect(mode == TestExecutionMode.Interpreter).to_equal(true)
```

</details>

#### creates Smf variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = TestExecutionMode.Smf
expect(mode == TestExecutionMode.Smf).to_equal(true)
```

</details>

#### creates Native variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = TestExecutionMode.Native
expect(mode == TestExecutionMode.Native).to_equal(true)
```

</details>

#### distinguishes Interpreter from Smf

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = TestExecutionMode.Interpreter
val b = TestExecutionMode.Smf
expect(a == b).to_equal(false)
```

</details>

#### distinguishes Interpreter from Native

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = TestExecutionMode.Interpreter
val b = TestExecutionMode.Native
expect(a == b).to_equal(false)
```

</details>

#### distinguishes Smf from Native

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = TestExecutionMode.Smf
val b = TestExecutionMode.Native
expect(a == b).to_equal(false)
```

</details>

#### compares equal variants

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = TestExecutionMode.Native
val b = TestExecutionMode.Native
expect(a == b).to_equal(true)
```

</details>

### TestLevel

#### creates All variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val level = TestLevel.All
expect(level == TestLevel.All).to_equal(true)
```

</details>

#### creates Unit variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val level = TestLevel.Unit
expect(level == TestLevel.Unit).to_equal(true)
```

</details>

#### creates Integration variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val level = TestLevel.Integration
expect(level == TestLevel.Integration).to_equal(true)
```

</details>

#### creates System variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val level = TestLevel.System
expect(level == TestLevel.System).to_equal(true)
```

</details>

#### distinguishes Unit from Integration

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TestLevel.Unit == TestLevel.Integration).to_equal(false)
```

</details>

#### distinguishes All from System

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TestLevel.All == TestLevel.System).to_equal(false)
```

</details>

### OutputFormat

#### creates Default variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fmt = OutputFormat.Default
expect(fmt == OutputFormat.Default).to_equal(true)
```

</details>

#### creates Doc variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fmt = OutputFormat.Doc
expect(fmt == OutputFormat.Doc).to_equal(true)
```

</details>

#### distinguishes Default from Doc

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(OutputFormat.Default == OutputFormat.Doc).to_equal(false)
```

</details>

### TestFileResult

#### creates a result with all fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = TestFileResult(
    path: "test/example_spec.spl",
    passed: 10,
    failed: 0,
    skipped: 2,
    pending: 1,
    duration_ms: 500,
    error: "",
    timed_out: false
)
expect(r.path).to_equal("test/example_spec.spl")
expect(r.passed).to_equal(10)
expect(r.failed).to_equal(0)
expect(r.skipped).to_equal(2)
expect(r.pending).to_equal(1)
expect(r.duration_ms).to_equal(500)
expect(r.error).to_equal("")
expect(r.timed_out).to_equal(false)
```

</details>

#### is_ok returns true when no failures and no error and not timed out

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = TestFileResult(
    path: "passing.spl",
    passed: 5,
    failed: 0,
    skipped: 0,
    pending: 0,
    duration_ms: 100,
    error: "",
    timed_out: false
)
expect(file_result_is_ok(r)).to_equal(true)
```

</details>

#### is_ok returns false when there are failures

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = TestFileResult(
    path: "failing.spl",
    passed: 3,
    failed: 2,
    skipped: 0,
    pending: 0,
    duration_ms: 200,
    error: "",
    timed_out: false
)
expect(file_result_is_ok(r)).to_equal(false)
```

</details>

#### is_ok returns false when there is an error message

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = TestFileResult(
    path: "error.spl",
    passed: 0,
    failed: 0,
    skipped: 0,
    pending: 0,
    duration_ms: 50,
    error: "parse error on line 5",
    timed_out: false
)
expect(file_result_is_ok(r)).to_equal(false)
```

</details>

#### is_ok returns false when timed out

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = TestFileResult(
    path: "slow.spl",
    passed: 0,
    failed: 0,
    skipped: 0,
    pending: 0,
    duration_ms: 120000,
    error: "",
    timed_out: true
)
expect(file_result_is_ok(r)).to_equal(false)
```

</details>

#### is_ok returns false when both failed and error

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = TestFileResult(
    path: "bad.spl",
    passed: 1,
    failed: 1,
    skipped: 0,
    pending: 0,
    duration_ms: 300,
    error: "runtime error",
    timed_out: false
)
expect(file_result_is_ok(r)).to_equal(false)
```

</details>

#### is_ok returns false when all bad conditions

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = TestFileResult(
    path: "worst.spl",
    passed: 0,
    failed: 5,
    skipped: 0,
    pending: 0,
    duration_ms: 120000,
    error: "crash",
    timed_out: true
)
expect(file_result_is_ok(r)).to_equal(false)
```

</details>

#### handles zero counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = TestFileResult(
    path: "empty.spl",
    passed: 0,
    failed: 0,
    skipped: 0,
    pending: 0,
    duration_ms: 0,
    error: "",
    timed_out: false
)
expect(file_result_is_ok(r)).to_equal(true)
expect(r.passed).to_equal(0)
```

</details>

#### stores skipped count separately from failures

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = TestFileResult(
    path: "skipped.spl",
    passed: 0,
    failed: 0,
    skipped: 10,
    pending: 5,
    duration_ms: 10,
    error: "",
    timed_out: false
)
expect(file_result_is_ok(r)).to_equal(true)
expect(r.skipped).to_equal(10)
expect(r.pending).to_equal(5)
```

</details>

### TestRunResult

#### creates a result with aggregate counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = TestRunResult(
    total_passed: 100,
    total_failed: 0,
    total_skipped: 5,
    total_pending: 3,
    total_timed_out: 0,
    total_duration_ms: 5000
)
expect(r.total_passed).to_equal(100)
expect(r.total_failed).to_equal(0)
expect(r.total_skipped).to_equal(5)
expect(r.total_pending).to_equal(3)
expect(r.total_timed_out).to_equal(0)
expect(r.total_duration_ms).to_equal(5000)
```

</details>

#### is_ok returns true when no failures and no timeouts

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = TestRunResult(
    total_passed: 50,
    total_failed: 0,
    total_skipped: 2,
    total_pending: 1,
    total_timed_out: 0,
    total_duration_ms: 3000
)
expect(run_result_is_ok(r)).to_equal(true)
```

</details>

#### is_ok returns false when there are failures

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = TestRunResult(
    total_passed: 48,
    total_failed: 2,
    total_skipped: 0,
    total_pending: 0,
    total_timed_out: 0,
    total_duration_ms: 3000
)
expect(run_result_is_ok(r)).to_equal(false)
```

</details>

#### is_ok returns false when there are timeouts

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = TestRunResult(
    total_passed: 49,
    total_failed: 0,
    total_skipped: 0,
    total_pending: 0,
    total_timed_out: 1,
    total_duration_ms: 125000
)
expect(run_result_is_ok(r)).to_equal(false)
```

</details>

#### is_ok returns false when both failures and timeouts

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = TestRunResult(
    total_passed: 40,
    total_failed: 5,
    total_skipped: 0,
    total_pending: 0,
    total_timed_out: 3,
    total_duration_ms: 360000
)
expect(run_result_is_ok(r)).to_equal(false)
```

</details>

#### handles all zeros

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = TestRunResult(
    total_passed: 0,
    total_failed: 0,
    total_skipped: 0,
    total_pending: 0,
    total_timed_out: 0,
    total_duration_ms: 0
)
expect(run_result_is_ok(r)).to_equal(true)
```

</details>

### SkipFeatureInfo

#### creates with all fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = SkipFeatureInfo(
    file_path: "test/feature/language/pattern_matching_spec.spl",
    title: "Pattern Matching Exhaustiveness",
    feature_ids: "PM-001,PM-002",
    category: "pattern_matching",
    status: "planned"
)
expect(info.file_path).to_equal("test/feature/language/pattern_matching_spec.spl")
expect(info.title).to_equal("Pattern Matching Exhaustiveness")
expect(info.feature_ids).to_equal("PM-001,PM-002")
expect(info.category).to_equal("pattern_matching")
expect(info.status).to_equal("planned")
```

</details>

#### handles empty fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = SkipFeatureInfo(
    file_path: "",
    title: "",
    feature_ids: "",
    category: "",
    status: ""
)
expect(info.file_path).to_equal("")
expect(info.title).to_equal("")
```

</details>

#### handles various status values

<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val planned = SkipFeatureInfo(
    file_path: "a.spl",
    title: "Feature A",
    feature_ids: "F-001",
    category: "core",
    status: "planned"
)
expect(planned.status).to_equal("planned")

val in_progress = SkipFeatureInfo(
    file_path: "b.spl",
    title: "Feature B",
    feature_ids: "F-002",
    category: "core",
    status: "in_progress"
)
expect(in_progress.status).to_equal("in_progress")

val blocked = SkipFeatureInfo(
    file_path: "c.spl",
    title: "Feature C",
    feature_ids: "F-003",
    category: "core",
    status: "blocked"
)
expect(blocked.status).to_equal("blocked")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_runner/types_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TestExecutionMode
- TestLevel
- OutputFormat
- TestFileResult
- TestRunResult
- SkipFeatureInfo

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 34 |
| Active scenarios | 34 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
