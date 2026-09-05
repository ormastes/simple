# debug_assistant_spec

> Debug Assistant Tests

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# debug_assistant_spec

Debug Assistant Tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/engine/debug_assistant_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Debug Assistant Tests

Tests DiagnosticReport construction, entry tracking, severity checks,
and DebugAssistant diagnosis functions for physics, scene, and performance.

## Scenarios

### DiagnosticReport

### new

#### creates an empty report with summary

- creates an empty report with summary
   - Expected: report.summary equals `test summary`
   - Expected: report.entry_count() equals `0.to_i32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates an empty report with summary")
val report = DiagnosticReport.new("test summary")
expect(report.summary).to_equal("test summary")
expect(report.entry_count()).to_equal(0.to_i32())
```

</details>

### add_entry

#### adds diagnostic entries

- adds diagnostic entries
   - Expected: report.entry_count() equals `1.to_i32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds diagnostic entries")
var report = DiagnosticReport.new("test")
report.add_entry(DiagnosticEntry(
    category: "physics",
    issue: "no gravity",
    severity: "warning",
    suggestion: "enable gravity"
))
expect(report.entry_count()).to_equal(1.to_i32())
```

</details>

### has_errors

#### returns false when no errors

- returns false when no errors
   - Expected: report.has_errors() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false when no errors")
var report = DiagnosticReport.new("clean")
report.add_entry(DiagnosticEntry(
    category: "a", issue: "b", severity: "warning", suggestion: "c"
))
expect(report.has_errors()).to_equal(false)
```

</details>

#### returns true when an error entry exists

- returns true when an error entry exists
   - Expected: report.has_errors() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true when an error entry exists")
var report = DiagnosticReport.new("broken")
report.add_entry(DiagnosticEntry(
    category: "a", issue: "b", severity: "error", suggestion: "c"
))
expect(report.has_errors()).to_equal(true)
```

</details>

### has_warnings

#### returns false when no warnings

- returns false when no warnings
   - Expected: report.has_warnings() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false when no warnings")
val report = DiagnosticReport.new("clean")
expect(report.has_warnings()).to_equal(false)
```

</details>

#### returns true when a warning entry exists

- returns true when a warning entry exists
   - Expected: report.has_warnings() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true when a warning entry exists")
var report = DiagnosticReport.new("warn")
report.add_entry(DiagnosticEntry(
    category: "a", issue: "b", severity: "warning", suggestion: "c"
))
expect(report.has_warnings()).to_equal(true)
```

</details>

### to_text

#### contains report header and summary

- contains report header and summary


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains report header and summary")
val report = DiagnosticReport.new("my summary")
val txt = report.to_text()
expect(txt).to_contain("Diagnostic Report")
expect(txt).to_contain("my summary")
```

</details>

#### contains entry details

- contains entry details


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains entry details")
var report = DiagnosticReport.new("details test")
report.add_entry(DiagnosticEntry(
    category: "physics",
    issue: "no colliders",
    severity: "error",
    suggestion: "add CollisionShape"
))
val txt = report.to_text()
expect(txt).to_contain("[error]")
expect(txt).to_contain("physics")
expect(txt).to_contain("no colliders")
expect(txt).to_contain("add CollisionShape")
```

</details>

### DebugAssistant

### new

#### starts with zero known issues

- starts with zero known issues
   - Expected: da.known_issue_count() equals `0.to_i64()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with zero known issues")
val da = DebugAssistant.new()
expect(da.known_issue_count()).to_equal(0.to_i64())
```

</details>

### add_known_issue

#### registers known issue patterns

- registers known issue patterns
   - Expected: da.known_issue_count() equals `2.to_i64()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registers known issue patterns")
var da = DebugAssistant.new()
da.add_known_issue("null pointer in physics")
da.add_known_issue("texture not found")
expect(da.known_issue_count()).to_equal(2.to_i64())
```

</details>

### diagnose_physics

#### warns when no physics bodies

- warns when no physics bodies
   - Expected: report.has_warnings() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns when no physics bodies")
val da = DebugAssistant.new()
val report = da.diagnose_physics(0, true, false)
expect(report.has_warnings()).to_equal(true)
expect(report.entry_count()).to_be_greater_than(0.to_i32())
```

</details>

#### errors when bodies exist but no colliders

- errors when bodies exist but no colliders
   - Expected: report.has_errors() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("errors when bodies exist but no colliders")
val da = DebugAssistant.new()
val report = da.diagnose_physics(5, true, false)
expect(report.has_errors()).to_equal(true)
```

</details>

#### reports info when gravity is disabled

- reports info when gravity is disabled


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports info when gravity is disabled")
val da = DebugAssistant.new()
val report = da.diagnose_physics(5, false, true)
expect(report.entry_count()).to_be_greater_than(0.to_i32())
```

</details>

#### produces no entries for healthy config

- produces no entries for healthy config
   - Expected: report.entry_count() equals `0.to_i32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces no entries for healthy config")
val da = DebugAssistant.new()
val report = da.diagnose_physics(5, true, true)
expect(report.entry_count()).to_equal(0.to_i32())
```

</details>

### diagnose_scene

#### warns on empty scene

- warns on empty scene
   - Expected: report.has_warnings() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns on empty scene")
val da = DebugAssistant.new()
val report = da.diagnose_scene(0, 0)
expect(report.has_warnings()).to_equal(true)
```

</details>

#### warns on orphan nodes

- warns on orphan nodes
   - Expected: report.has_warnings() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns on orphan nodes")
val da = DebugAssistant.new()
val report = da.diagnose_scene(50, 3)
expect(report.has_warnings()).to_equal(true)
```

</details>

#### warns on very large scene

- warns on very large scene
   - Expected: report.has_warnings() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns on very large scene")
val da = DebugAssistant.new()
val report = da.diagnose_scene(20000, 0)
expect(report.has_warnings()).to_equal(true)
```

</details>

#### produces no warnings for healthy scene

- produces no warnings for healthy scene
   - Expected: report.has_warnings() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces no warnings for healthy scene")
val da = DebugAssistant.new()
val report = da.diagnose_scene(100, 0)
expect(report.has_warnings()).to_equal(false)
```

</details>

### diagnose_performance

#### errors when FPS is below 30

- errors when FPS is below 30
   - Expected: report.has_errors() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("errors when FPS is below 30")
val da = DebugAssistant.new()
val report = da.diagnose_performance(15.0, 100, 50000)
expect(report.has_errors()).to_equal(true)
```

</details>

#### warns when FPS is between 30 and 60

- warns when FPS is between 30 and 60
   - Expected: report.has_warnings() is true
   - Expected: report.has_errors() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns when FPS is between 30 and 60")
val da = DebugAssistant.new()
val report = da.diagnose_performance(45.0, 100, 50000)
expect(report.has_warnings()).to_equal(true)
expect(report.has_errors()).to_equal(false)
```

</details>

#### warns on high draw call count

- warns on high draw call count
   - Expected: report.has_warnings() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns on high draw call count")
val da = DebugAssistant.new()
val report = da.diagnose_performance(60.0, 2000, 50000)
expect(report.has_warnings()).to_equal(true)
```

</details>

#### warns on high triangle count

- warns on high triangle count
   - Expected: report.has_warnings() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns on high triangle count")
val da = DebugAssistant.new()
val report = da.diagnose_performance(60.0, 100, 2000000)
expect(report.has_warnings()).to_equal(true)
```

</details>

#### produces no issues for healthy performance

- produces no issues for healthy performance
   - Expected: report.entry_count() equals `0.to_i32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces no issues for healthy performance")
val da = DebugAssistant.new()
val report = da.diagnose_performance(60.0, 500, 500000)
expect(report.entry_count()).to_equal(0.to_i32())
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
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

- Canonical SPipe generation for source `bc545de0d714a980693a453e4fb06de401802c0e5f4e86df22b8c102ea6575bc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bc545de0d714a980693a453e4fb06de401802c0e5f4e86df22b8c102ea6575bc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bc545de0d714a980693a453e4fb06de401802c0e5f4e86df22b8c102ea6575bc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/engine/debug_assistant_spec.spl
mirror: doc/06_spec/unit/lib/engine/debug_assistant_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/engine/debug_assistant_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/engine/debug_assistant_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/engine/debug_assistant_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates an empty report with summary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/engine/debug_assistant_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'adds diagnostic entries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/engine/debug_assistant_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns false when no errors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
