# Task Daemon Collector Specification

> Tests covering _parse_task_file: key=value parsing, collect_task_daemon_tasks: file-system read.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Task Daemon Collector Specification

## Scenarios

### _parse_task_file: key=value parsing

#### parses id field

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses id field
   - Expected: task.id equals `abc-123`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses id field")
val content = "id=abc-123\ncommand=bin/simple test\nstatus=working\n"
val task = _parse_task_file("abc-123.task", content)
expect(task.id).to_equal("abc-123")
```

</details>

#### parses command field

- parses command field
   - Expected: task.command equals `bin/simple build`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses command field")
val content = "id=task-1\ncommand=bin/simple build\nstatus=completed\n"
val task = _parse_task_file("task-1.task", content)
expect(task.command).to_equal("bin/simple build")
```

</details>

#### maps status=working to TaskState.Active

- maps status=working to TaskState.Active
   - Expected: task_state_name(task.state) equals `active`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps status=working to TaskState.Active")
val content = "id=t1\ncommand=echo hi\nstatus=working\n"
val task = _parse_task_file("t1.task", content)
expect(task_state_name(task.state)).to_equal("active")
```

</details>

#### maps status=completed to TaskState.Completed

- maps status=completed to TaskState.Completed
   - Expected: task_state_name(task.state) equals `done`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps status=completed to TaskState.Completed")
val content = "id=t2\ncommand=echo done\nstatus=completed\n"
val task = _parse_task_file("t2.task", content)
expect(task_state_name(task.state)).to_equal("done")
```

</details>

#### maps status=failed to TaskState.Failed

- maps status=failed to TaskState.Failed
   - Expected: task_state_name(task.state) equals `failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps status=failed to TaskState.Failed")
val content = "id=t3\ncommand=false\nstatus=failed\n"
val task = _parse_task_file("t3.task", content)
expect(task_state_name(task.state)).to_equal("failed")
```

</details>

#### maps status=cancelled to TaskState.Cancelled

- maps status=cancelled to TaskState.Cancelled
   - Expected: task_state_name(task.state) equals `cancelled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps status=cancelled to TaskState.Cancelled")
val content = "id=t4\ncommand=cancel\nstatus=cancelled\n"
val task = _parse_task_file("t4.task", content)
expect(task_state_name(task.state)).to_equal("cancelled")
```

</details>

#### sets kind to TaskKind.Job

- sets kind to TaskKind.Job
   - Expected: task_kind_name(task.kind) equals `job`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets kind to TaskKind.Job")
val content = "id=t5\ncommand=run\nstatus=working\n"
val task = _parse_task_file("t5.task", content)
expect(task_kind_name(task.kind)).to_equal("job")
```

</details>

#### handles missing fields gracefully (no crash)

- handles missing fields gracefully (no crash)
   - Expected: task.id equals `t6`
   - Expected: task.command equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles missing fields gracefully (no crash)")
val content = "id=t6\n"
val task = _parse_task_file("t6.task", content)
expect(task.id).to_equal("t6")
expect(task.command).to_equal("")
```

</details>

#### handles empty content without crashing

- handles empty content without crashing
   - Expected: task.id.len() >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty content without crashing")
val task = _parse_task_file("empty.task", "")
expect(task.id.len() >= 0).to_equal(true)
```

</details>

### collect_task_daemon_tasks: file-system read

#### returns a list (possibly empty if no task daemon dir)

- returns a list (possibly empty if no task daemon dir)
   - Expected: tasks.len() >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns a list (possibly empty if no task daemon dir)")
val tasks = collect_task_daemon_tasks()
expect(tasks.len() >= 0).to_equal(true)
```

</details>

#### all returned tasks have kind Job

- all returned tasks have kind Job
   - Expected: task_kind_name(task.kind) equals `job`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all returned tasks have kind Job")
val tasks = collect_task_daemon_tasks()
for task in tasks:
    expect(task_kind_name(task.kind)).to_equal("job")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_dashboard/collectors/task_daemon_collector_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering _parse_task_file: key=value parsing, collect_task_daemon_tasks: file-system read.
- _parse_task_file: key=value parsing
- collect_task_daemon_tasks: file-system read

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `b5eada5a0d5773e0fd1a9daa893d63b7364db472926d5fb9174d895eacd64577`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b5eada5a0d5773e0fd1a9daa893d63b7364db472926d5fb9174d895eacd64577`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b5eada5a0d5773e0fd1a9daa893d63b7364db472926d5fb9174d895eacd64577`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/llm_dashboard/collectors/task_daemon_collector_spec.spl
mirror: doc/06_spec/01_unit/app/llm_dashboard/collectors/task_daemon_collector_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/llm_dashboard/collectors/task_daemon_collector_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_dashboard/collectors/task_daemon_collector_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_dashboard/collectors/task_daemon_collector_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses id field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_dashboard/collectors/task_daemon_collector_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses command field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_dashboard/collectors/task_daemon_collector_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps status=working to TaskState.Active' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
