# Task Error Surfacing Specification

> Tests covering HostScheduler death-reason API (W2-5 structural), HostScheduler death bookkeeping (W2-5 behavioural), Task identity stamp for death reasons (W2-5 behavioural).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Task Error Surfacing Specification

## Scenarios

### HostScheduler death-reason API (W2-5 structural)

#### TaskDeathRecord struct exists with required fields

- TaskDeathRecord struct exists with required fields
   - Expected: src contains `struct TaskDeathRecord`
   - Expected: src contains `task_key: text`
   - Expected: src contains `task_id: usize`
   - Expected: src contains `reason: text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("TaskDeathRecord struct exists with required fields")
val src = sched_src()
expect(src.contains("struct TaskDeathRecord")).to_equal(true)
expect(src.contains("task_key: text")).to_equal(true)
expect(src.contains("task_id: usize")).to_equal(true)
expect(src.contains("reason: text")).to_equal(true)
```

</details>

#### HostScheduler has death_records field

- HostScheduler has death_records field
   - Expected: src contains `death_records: [TaskDeathRecord]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("HostScheduler has death_records field")
val src = sched_src()
expect(src.contains("death_records: [TaskDeathRecord]")).to_equal(true)
```

</details>

#### HostTask has task_error field

- HostTask has task_error field
   - Expected: src contains `task_error: text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("HostTask has task_error field")
val src = sched_src()
expect(src.contains("task_error: text")).to_equal(true)
```

</details>

#### last_death_reason accessor exists

- last_death_reason accessor exists
   - Expected: src contains `fn last_death_reason() -> text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("last_death_reason accessor exists")
val src = sched_src()
expect(src.contains("fn last_death_reason() -> text")).to_equal(true)
```

</details>

#### death_count accessor exists

- death_count accessor exists
   - Expected: src contains `fn death_count() -> usize`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("death_count accessor exists")
val src = sched_src()
expect(src.contains("fn death_count() -> usize")).to_equal(true)
```

</details>

#### mark_task_error method exists

- mark_task_error method exists
   - Expected: src contains `me mark_task_error(task_id: usize, error_text: text)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("mark_task_error method exists")
val src = sched_src()
expect(src.contains("me mark_task_error(task_id: usize, error_text: text)")).to_equal(true)
```

</details>

#### death record is pushed on task completion with non-empty task_error

- death record is pushed on task completion with non-empty task_error
   - Expected: src contains `self.death_records = self.death_records.push(rec)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("death record is pushed on task completion with non-empty task_error")
val src = sched_src()
expect(src.contains("self.death_records = self.death_records.push(rec)")).to_equal(true)
```

</details>

#### current_unified_task_key stamps death records

- current_unified_task_key stamps death records
   - Expected: src contains `current_unified_task_key`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("current_unified_task_key stamps death records")
val src = sched_src()
expect(src.contains("current_unified_task_key")).to_equal(true)
```

</details>

#### run_result_task surfaces Err to handle (H3)

- run_result_task surfaces Err to handle (H3)
   - Expected: src contains `me run_result_task<T>`
   - Expected: src contains `fn() -> Result<T, text>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("run_result_task surfaces Err to handle (H3)")
val src = runtime_src()
expect(src.contains("me run_result_task<T>")).to_equal(true)
expect(src.contains("fn() -> Result<T, text>")).to_equal(true)
```

</details>

#### drain_result_errors populates AsyncError.JoinError

- drain_result_errors populates AsyncError.JoinError
   - Expected: src contains `AsyncError.JoinError`
   - Expected: src contains `me drain_result_errors<T>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("drain_result_errors populates AsyncError.JoinError")
val src = runtime_src()
expect(src.contains("AsyncError.JoinError")).to_equal(true)
expect(src.contains("me drain_result_errors<T>")).to_equal(true)
```

</details>

### HostScheduler death bookkeeping (W2-5 behavioural)

#### fresh scheduler has zero death_count

- fresh scheduler has zero death_count
   - Expected: sched.death_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fresh scheduler has zero death_count")
val sched = HostScheduler.new(1)
expect(sched.death_count()).to_equal(0)
```

</details>

#### last_death_reason on fresh scheduler is empty string

- last_death_reason on fresh scheduler is empty string
   - Expected: reason equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("last_death_reason on fresh scheduler is empty string")
val sched = HostScheduler.new(1)
val reason = sched.last_death_reason()
expect(reason).to_equal("")
```

</details>

#### death_records starts empty

- death_records starts empty
   - Expected: sched.death_records.is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("death_records starts empty")
val sched = HostScheduler.new(1)
expect(sched.death_records.is_empty()).to_equal(true)
```

</details>

#### mark_task_error on non-existent task is a no-op (no crash, no death record)

- mark_task_error on non-existent task is a no-op (no crash, no death record)
   - Expected: sched.death_count() equals `0`
   - Expected: sched.last_death_reason() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("mark_task_error on non-existent task is a no-op (no crash, no death record)")
var sched = HostScheduler.new(1)
sched.mark_task_error(999, "phantom-error")
expect(sched.death_count()).to_equal(0)
expect(sched.last_death_reason()).to_equal("")
```

</details>

### Task identity stamp for death reasons (W2-5 behavioural)

#### scheduler-task key is available while scheduler task is active

- scheduler-task key is available while scheduler task is active
   - Expected: key equals `scheduler-task-101`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("scheduler-task key is available while scheduler task is active")
val prev = enter_scheduler_task_id(101)
val key = current_unified_task_key("fallback")
exit_scheduler_task_id(prev)
expect(key).to_equal("scheduler-task-101")
```

</details>

#### current_scheduler_task_key returns fallback when no task active

- current_scheduler_task_key returns fallback when no task active
   - Expected: key equals `no-active-task`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("current_scheduler_task_key returns fallback when no task active")
val key = current_scheduler_task_key("no-active-task")
expect(key).to_equal("no-active-task")
```

</details>

#### death reason key matches the task id entered

- death reason key matches the task id entered
   - Expected: key equals `scheduler-task-42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("death reason key matches the task id entered")
val prev = enter_scheduler_task_id(42)
val key = current_unified_task_key("ignored-fallback")
exit_scheduler_task_id(prev)
expect(key).to_equal("scheduler-task-42")
```

</details>

#### sibling task identity not affected after first task exits

- sibling task identity not affected after first task exits
   - Expected: key equals `scheduler-task-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("sibling task identity not affected after first task exits")
val prev_a = enter_scheduler_task_id(1)
exit_scheduler_task_id(prev_a)
val prev_b = enter_scheduler_task_id(2)
val key = current_unified_task_key("fb")
exit_scheduler_task_id(prev_b)
# sibling task B completed; its key was scheduler-task-2
expect(key).to_equal("scheduler-task-2")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/async_host/task_error_surfacing/task_error_surfacing_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering HostScheduler death-reason API (W2-5 structural), HostScheduler death bookkeeping (W2-5 behavioural), Task identity stamp for death reasons (W2-5 behavioural).
- HostScheduler death-reason API (W2-5 structural)
- HostScheduler death bookkeeping (W2-5 behavioural)
- Task identity stamp for death reasons (W2-5 behavioural)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e7c3e5a7a727e442adc1806ff87dd4c3413a0553d8d8fc09c7da9b5901b85fae`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e7c3e5a7a727e442adc1806ff87dd4c3413a0553d8d8fc09c7da9b5901b85fae`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e7c3e5a7a727e442adc1806ff87dd4c3413a0553d8d8fc09c7da9b5901b85fae`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/nogc_async_mut/async_host/task_error_surfacing/task_error_surfacing_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/async_host/task_error_surfacing/task_error_surfacing_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/async_host/task_error_surfacing/task_error_surfacing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/async_host/task_error_surfacing/task_error_surfacing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/async_host/task_error_surfacing/task_error_surfacing_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_async_mut/async_host/task_error_surfacing/task_error_surfacing_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TaskDeathRecord struct exists with required fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/async_host/task_error_surfacing/task_error_surfacing_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'HostScheduler has death_records field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/async_host/task_error_surfacing/task_error_surfacing_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'HostTask has task_error field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
