# debug_assistant_spec

> Debug Assistant Tests

<!-- sdn-diagram:id=debug_assistant_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=debug_assistant_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

debug_assistant_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=debug_assistant_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/01_unit/lib/engine/debug_assistant_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Debug Assistant Tests

Tests DiagnosticReport construction, entry tracking, severity checks,
and DebugAssistant diagnosis functions for physics, scene, and performance.

## Scenarios

### DiagnosticReport

### new

#### creates an empty report with summary

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = DiagnosticReport.new("test summary")
expect(report.summary).to_equal("test summary")
expect(report.entry_count()).to_equal(0.to_i32())
```

</details>

### add_entry

#### adds diagnostic entries

1. var report = DiagnosticReport new
   - Expected: report.entry_count() equals `1.to_i32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var report = DiagnosticReport new
   - Expected: report.has_errors() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var report = DiagnosticReport.new("clean")
report.add_entry(DiagnosticEntry(
    category: "a", issue: "b", severity: "warning", suggestion: "c"
))
expect(report.has_errors()).to_equal(false)
```

</details>

#### returns true when an error entry exists

1. var report = DiagnosticReport new
   - Expected: report.has_errors() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var report = DiagnosticReport.new("broken")
report.add_entry(DiagnosticEntry(
    category: "a", issue: "b", severity: "error", suggestion: "c"
))
expect(report.has_errors()).to_equal(true)
```

</details>

### has_warnings

#### returns false when no warnings

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = DiagnosticReport.new("clean")
expect(report.has_warnings()).to_equal(false)
```

</details>

#### returns true when a warning entry exists

1. var report = DiagnosticReport new
   - Expected: report.has_warnings() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var report = DiagnosticReport.new("warn")
report.add_entry(DiagnosticEntry(
    category: "a", issue: "b", severity: "warning", suggestion: "c"
))
expect(report.has_warnings()).to_equal(true)
```

</details>

### to_text

#### contains report header and summary

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = DiagnosticReport.new("my summary")
val txt = report.to_text()
expect(txt).to_contain("Diagnostic Report")
expect(txt).to_contain("my summary")
```

</details>

#### contains entry details

1. var report = DiagnosticReport new


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val da = DebugAssistant.new()
expect(da.known_issue_count()).to_equal(0.to_i64())
```

</details>

### add_known_issue

#### registers known issue patterns

1. var da = DebugAssistant new
2. da add known issue
3. da add known issue
   - Expected: da.known_issue_count() equals `2.to_i64()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var da = DebugAssistant.new()
da.add_known_issue("null pointer in physics")
da.add_known_issue("texture not found")
expect(da.known_issue_count()).to_equal(2.to_i64())
```

</details>

### diagnose_physics

#### warns when no physics bodies

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val da = DebugAssistant.new()
val report = da.diagnose_physics(0, true, false)
expect(report.has_warnings()).to_equal(true)
expect(report.entry_count()).to_be_greater_than(0.to_i32())
```

</details>

#### errors when bodies exist but no colliders

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val da = DebugAssistant.new()
val report = da.diagnose_physics(5, true, false)
expect(report.has_errors()).to_equal(true)
```

</details>

#### reports info when gravity is disabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val da = DebugAssistant.new()
val report = da.diagnose_physics(5, false, true)
expect(report.entry_count()).to_be_greater_than(0.to_i32())
```

</details>

#### produces no entries for healthy config

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val da = DebugAssistant.new()
val report = da.diagnose_physics(5, true, true)
expect(report.entry_count()).to_equal(0.to_i32())
```

</details>

### diagnose_scene

#### warns on empty scene

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val da = DebugAssistant.new()
val report = da.diagnose_scene(0, 0)
expect(report.has_warnings()).to_equal(true)
```

</details>

#### warns on orphan nodes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val da = DebugAssistant.new()
val report = da.diagnose_scene(50, 3)
expect(report.has_warnings()).to_equal(true)
```

</details>

#### warns on very large scene

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val da = DebugAssistant.new()
val report = da.diagnose_scene(20000, 0)
expect(report.has_warnings()).to_equal(true)
```

</details>

#### produces no warnings for healthy scene

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val da = DebugAssistant.new()
val report = da.diagnose_scene(100, 0)
expect(report.has_warnings()).to_equal(false)
```

</details>

### diagnose_performance

#### errors when FPS is below 30

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val da = DebugAssistant.new()
val report = da.diagnose_performance(15.0, 100, 50000)
expect(report.has_errors()).to_equal(true)
```

</details>

#### warns when FPS is between 30 and 60

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val da = DebugAssistant.new()
val report = da.diagnose_performance(45.0, 100, 50000)
expect(report.has_warnings()).to_equal(true)
expect(report.has_errors()).to_equal(false)
```

</details>

#### warns on high draw call count

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val da = DebugAssistant.new()
val report = da.diagnose_performance(60.0, 2000, 50000)
expect(report.has_warnings()).to_equal(true)
```

</details>

#### warns on high triangle count

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val da = DebugAssistant.new()
val report = da.diagnose_performance(60.0, 100, 2000000)
expect(report.has_warnings()).to_equal(true)
```

</details>

#### produces no issues for healthy performance

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
