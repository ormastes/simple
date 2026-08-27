# Types Specification

> Tests covering TestExecutionMode, TestLevel, OutputFormat, TestFileResult, TestRunResult, SkipFeatureInfo.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 34 | 34 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Types Specification

## Scenarios

### TestExecutionMode

#### creates Interpreter variant

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates Interpreter variant
   - Expected: mode equals `TestExecutionMode.Interpreter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates Interpreter variant")
val mode = TestExecutionMode.Interpreter
expect(mode).to_equal(TestExecutionMode.Interpreter)
```

</details>

#### creates Smf variant

- creates Smf variant
   - Expected: mode equals `TestExecutionMode.Smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates Smf variant")
val mode = TestExecutionMode.Smf
expect(mode).to_equal(TestExecutionMode.Smf)
```

</details>

#### creates Native variant

- creates Native variant
   - Expected: mode equals `TestExecutionMode.Native`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates Native variant")
val mode = TestExecutionMode.Native
expect(mode).to_equal(TestExecutionMode.Native)
```

</details>

#### distinguishes Interpreter from Smf

- distinguishes Interpreter from Smf


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("distinguishes Interpreter from Smf")
val a = TestExecutionMode.Interpreter
val b = TestExecutionMode.Smf
expect(a).to_not_equal(b)
```

</details>

#### distinguishes Interpreter from Native

- distinguishes Interpreter from Native


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("distinguishes Interpreter from Native")
val a = TestExecutionMode.Interpreter
val b = TestExecutionMode.Native
expect(a).to_not_equal(b)
```

</details>

#### distinguishes Smf from Native

- distinguishes Smf from Native


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("distinguishes Smf from Native")
val a = TestExecutionMode.Smf
val b = TestExecutionMode.Native
expect(a).to_not_equal(b)
```

</details>

#### compares equal variants

- compares equal variants
   - Expected: a equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares equal variants")
val a = TestExecutionMode.Native
val b = TestExecutionMode.Native
expect(a).to_equal(b)
```

</details>

### TestLevel

#### creates All variant

- creates All variant
   - Expected: level equals `TestLevel.All`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates All variant")
val level = TestLevel.All
expect(level).to_equal(TestLevel.All)
```

</details>

#### creates Unit variant

- creates Unit variant
   - Expected: level equals `TestLevel.Unit`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates Unit variant")
val level = TestLevel.Unit
expect(level).to_equal(TestLevel.Unit)
```

</details>

#### creates Integration variant

- creates Integration variant
   - Expected: level equals `TestLevel.Integration`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates Integration variant")
val level = TestLevel.Integration
expect(level).to_equal(TestLevel.Integration)
```

</details>

#### creates System variant

- creates System variant
   - Expected: level equals `TestLevel.System`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates System variant")
val level = TestLevel.System
expect(level).to_equal(TestLevel.System)
```

</details>

#### distinguishes Unit from Integration

- distinguishes Unit from Integration


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("distinguishes Unit from Integration")
expect(TestLevel.Unit).to_not_equal(TestLevel.Integration)
```

</details>

#### distinguishes All from System

- distinguishes All from System


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("distinguishes All from System")
expect(TestLevel.All).to_not_equal(TestLevel.System)
```

</details>

### OutputFormat

#### creates Text variant

- creates Text variant
   - Expected: fmt equals `OutputFormat.Text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates Text variant")
val fmt = OutputFormat.Text
expect(fmt).to_equal(OutputFormat.Text)
```

</details>

#### creates Doc variant

- creates Doc variant
   - Expected: fmt equals `OutputFormat.Doc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates Doc variant")
val fmt = OutputFormat.Doc
expect(fmt).to_equal(OutputFormat.Doc)
```

</details>

#### distinguishes Text from Doc

- distinguishes Text from Doc


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("distinguishes Text from Doc")
expect(OutputFormat.Text).to_not_equal(OutputFormat.Doc)
```

</details>

### TestFileResult

#### creates a result with all fields

- creates a result with all fields
   - Expected: r.path equals `test/example_spec.spl`
   - Expected: r.passed equals `10`
   - Expected: r.failed equals `0`
   - Expected: r.skipped equals `2`
   - Expected: r.pending equals `1`
   - Expected: r.duration_ms equals `500`
   - Expected: r.error equals ``
   - Expected: r.timed_out is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a result with all fields")
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

- is_ok returns true when no failures and no error and not timed out
   - Expected: file_result_is_ok(r) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_ok returns true when no failures and no error and not timed out")
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

- is_ok returns false when there are failures
   - Expected: file_result_is_ok(r) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_ok returns false when there are failures")
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

- is_ok returns false when there is an error message
   - Expected: file_result_is_ok(r) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_ok returns false when there is an error message")
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

- is_ok returns false when timed out
   - Expected: file_result_is_ok(r) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_ok returns false when timed out")
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

- is_ok returns false when both failed and error
   - Expected: file_result_is_ok(r) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_ok returns false when both failed and error")
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

- is_ok returns false when all bad conditions
   - Expected: file_result_is_ok(r) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_ok returns false when all bad conditions")
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

- handles zero counts
   - Expected: file_result_is_ok(r) is true
   - Expected: r.passed equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles zero counts")
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

- stores skipped count separately from failures
   - Expected: file_result_is_ok(r) is true
   - Expected: r.skipped equals `10`
   - Expected: r.pending equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores skipped count separately from failures")
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

- creates a result with aggregate counts
   - Expected: r.total_passed equals `100`
   - Expected: r.total_failed equals `0`
   - Expected: r.total_skipped equals `5`
   - Expected: r.total_pending equals `3`
   - Expected: r.total_timed_out equals `0`
   - Expected: r.total_duration_ms equals `5000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a result with aggregate counts")
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

- is_ok returns true when no failures and no timeouts
   - Expected: run_result_is_ok(r) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_ok returns true when no failures and no timeouts")
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

- is_ok returns false when there are failures
   - Expected: run_result_is_ok(r) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_ok returns false when there are failures")
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

- is_ok returns false when there are timeouts
   - Expected: run_result_is_ok(r) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_ok returns false when there are timeouts")
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

- is_ok returns false when both failures and timeouts
   - Expected: run_result_is_ok(r) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_ok returns false when both failures and timeouts")
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

- handles all zeros
   - Expected: run_result_is_ok(r) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles all zeros")
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

- creates with all fields
   - Expected: info.file_path equals `test/feature/language/pattern_matching_spec.spl`
   - Expected: info.title equals `Pattern Matching Exhaustiveness`
   - Expected: info.feature_ids equals `PM-001,PM-002`
   - Expected: info.category equals `pattern_matching`
   - Expected: info.status equals `planned`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates with all fields")
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

- handles empty fields
   - Expected: info.file_path equals ``
   - Expected: info.title equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty fields")
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

- handles various status values
   - Expected: planned.status equals `planned`
   - Expected: in_progress.status equals `in_progress`
   - Expected: blocked.status equals `blocked`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles various status values")
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
| Source | `test/unit/app/test_runner/types_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering TestExecutionMode, TestLevel, OutputFormat, TestFileResult, TestRunResult, SkipFeatureInfo.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d3b0361ba20c7468695d068ab4007622b48b754198f46d51af0390096cf430e1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d3b0361ba20c7468695d068ab4007622b48b754198f46d51af0390096cf430e1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d3b0361ba20c7468695d068ab4007622b48b754198f46d51af0390096cf430e1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/test_runner/types_spec.spl
mirror: doc/06_spec/unit/app/test_runner/types_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/test_runner/types_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/test_runner/types_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/test_runner/types_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 14 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/test_runner/types_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates Interpreter variant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/test_runner/types_spec.spl:100:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates Smf variant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/test_runner/types_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates Native variant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
