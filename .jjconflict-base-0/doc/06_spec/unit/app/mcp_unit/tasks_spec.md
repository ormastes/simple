# Tasks Specification

> Tests covering TaskStatus, TaskPriority, TaskProgress, Task, TaskError, TaskManager.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tasks Specification

## Scenarios

### TaskStatus

#### converts to string

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- converts to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts to string")
expect(TaskStatus.Pending.to_string() == "pending")
expect(TaskStatus.Running.to_string() == "running")
expect(TaskStatus.Completed.to_string() == "completed")
expect(TaskStatus.Failed.to_string() == "failed")
expect(TaskStatus.Cancelled.to_string() == "cancelled")
expect(TaskStatus.TimedOut.to_string() == "timed_out")
```

</details>

#### identifies terminal states

- identifies terminal states


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies terminal states")
expect(not TaskStatus.Pending.is_terminal())
expect(not TaskStatus.Running.is_terminal())
expect(TaskStatus.Completed.is_terminal())
expect(TaskStatus.Failed.is_terminal())
expect(TaskStatus.Cancelled.is_terminal())
expect(TaskStatus.TimedOut.is_terminal())
```

</details>

### TaskPriority

#### converts to string

- converts to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts to string")
expect(TaskPriority.Low.to_string() == "low")
expect(TaskPriority.Normal.to_string() == "normal")
expect(TaskPriority.High.to_string() == "high")
expect(TaskPriority.Critical.to_string() == "critical")
```

</details>

#### converts to numeric

- converts to numeric


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts to numeric")
expect(TaskPriority.Low.to_i64() == 0)
expect(TaskPriority.Normal.to_i64() == 1)
expect(TaskPriority.High.to_i64() == 2)
expect(TaskPriority.Critical.to_i64() == 3)
```

</details>

### TaskProgress

#### creates basic progress

- creates basic progress


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates basic progress")
val progress = TaskProgress(current: 50, total: nil, message: nil, percentage: nil)
expect(progress.current == 50)
```

</details>

#### adds total for percentage

- adds total for percentage


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds total for percentage")
var p0 = TaskProgress(current: 25, total: nil, message: nil, percentage: nil)
val progress = p0.with_total(100)
expect(progress.current == 25)

match progress.total:
    case Some(t):
        expect(t == 100)
    case nil:
        expect(false)

match progress.percentage:
    case Some(p):
        expect(p == 25.0)
    case nil:
        expect(false)
```

</details>

#### adds message

- adds message


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds message")
var p0 = TaskProgress(current: 10, total: nil, message: nil, percentage: nil)
val progress = p0.with_message("Processing...")

match progress.message:
    case Some(m):
        expect(m == "Processing...")
    case nil:
        expect(false)
```

</details>

#### converts to dict

- converts to dict


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts to dict")
var p0 = TaskProgress(current: 50, total: nil, message: nil, percentage: nil)
var p1 = p0.with_total(100)
val progress = p1.with_message("Half done")
val dict = progress.to_dict()

expect(dict.get("current") == 50)
expect(dict.has("total"))
expect(dict.has("message"))
expect(dict.has("percentage"))
```

</details>

### Task

#### creates new task

- creates new task


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates new task")
val task = Task(id: "task_1", operation: "test_operation", status: TaskStatus.Pending, priority: TaskPriority.Normal, timeout_ms: nil, started_at: nil, completed_at: nil, progress: nil, error: nil)
expect(task.id == "task_1")
expect(task.operation == "test_operation")
```

</details>

#### sets priority

- sets priority


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets priority")
var t0 = Task(id: "task_1", operation: "op", status: TaskStatus.Pending, priority: TaskPriority.Normal, timeout_ms: nil, started_at: nil, completed_at: nil, progress: nil, error: nil)
val task = t0.with_priority(TaskPriority.High)
expect(task.priority == TaskPriority.High)
```

</details>

#### sets timeout

- sets timeout


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets timeout")
var t0 = Task(id: "task_1", operation: "op", status: TaskStatus.Pending, priority: TaskPriority.Normal, timeout_ms: nil, started_at: nil, completed_at: nil, progress: nil, error: nil)
val task = t0.with_timeout(5000)

match task.timeout_ms:
    case Some(t):
        expect(t == 5000)
    case nil:
        expect(false)
```

</details>

#### checks running state

- checks running state


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks running state")
var task = Task(id: "task_1", operation: "op", status: TaskStatus.Pending, priority: TaskPriority.Normal, timeout_ms: nil, started_at: nil, completed_at: nil, progress: nil, error: nil)
expect(not task.is_running())

# Simulate starting
task.status = TaskStatus.Running
expect(task.is_running())
```

</details>

#### checks complete state

- checks complete state


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks complete state")
var task = Task(id: "task_1", operation: "op", status: TaskStatus.Pending, priority: TaskPriority.Normal, timeout_ms: nil, started_at: nil, completed_at: nil, progress: nil, error: nil)
expect(not task.is_complete())

task.status = TaskStatus.Completed
expect(task.is_complete())

task.status = TaskStatus.Failed
expect(task.is_complete())
```

</details>

#### converts to dict

- converts to dict


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts to dict")
var t0 = Task(id: "task_1", operation: "test", status: TaskStatus.Pending, priority: TaskPriority.Normal, timeout_ms: nil, started_at: nil, completed_at: nil, progress: nil, error: nil)
val task = t0.with_priority(TaskPriority.High)
val dict = task.to_dict()

expect(dict.get("id") == "task_1")
expect(dict.get("operation") == "test")
expect(dict.get("status") == "pending")
expect(dict.get("priority") == "high")
```

</details>

### TaskError

#### creates error

- creates error


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates error")
val error = TaskError(code: "ERR_001", message: "Something went wrong", retryable: false, details: nil)
expect(error.code == "ERR_001")
expect(error.message == "Something went wrong")
expect(not error.retryable)
```

</details>

#### adds details

- adds details


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds details")
var e0 = TaskError(code: "ERR", message: "msg", retryable: false, details: nil)
val error = e0.with_details("extra info")

match error.details:
    case Some(d):
        expect(d == "extra info")
    case nil:
        expect(false)
```

</details>

#### marks as retryable

- marks as retryable


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("marks as retryable")
var e0 = TaskError(code: "ERR", message: "msg", retryable: false, details: nil)
val error = e0.as_retryable()
expect(error.retryable)
```

</details>

#### converts to MCP error

- converts to MCP error


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts to MCP error")
val error = TaskError(code: "timeout", message: "Operation timed out", retryable: false, details: nil)
val mcp_error = error.to_mcp_error()
expect(mcp_error.category == TaskErrorCategory.Tool)
```

</details>

### TaskManager

#### creates task manager

- creates task manager


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates task manager")
val manager = TaskManager(tasks: {}, running_count: 0, max_concurrent_tasks: 10, next_id: 0)
expect(manager.running_count == 0)
expect(manager.max_concurrent_tasks == 10)
```

</details>

#### creates task

- creates task


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates task")
var manager = TaskManager(tasks: {}, running_count: 0, max_concurrent_tasks: 10, next_id: 0)
val task_id = manager.create_task("test_operation")
expect(task_id.starts_with("task_"))

match manager.get_task(task_id):
    case Some(task):
        expect(task.operation == "test_operation")
    case nil:
        expect(false)
```

</details>

#### creates task with options

- creates task with options


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates task with options")
var manager = TaskManager(tasks: {}, running_count: 0, max_concurrent_tasks: 10, next_id: 0)
val task_id = manager.create_task_with_options(
    "important_op",
    TaskPriority.Critical,
    Some(30000)
)

match manager.get_task(task_id):
    case Some(task):
        expect(task.priority == TaskPriority.Critical)
        match task.timeout_ms:
            case Some(t):
                expect(t == 30000)
            case nil:
                expect(false)
    case nil:
        expect(false)
```

</details>

#### starts task

- starts task


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts task")
var manager = TaskManager(tasks: {}, running_count: 0, max_concurrent_tasks: 10, next_id: 0)
val task_id = manager.create_task("op")

var result = manager.start_task(task_id)
match result:
    case Ok(_):
        expect(true)
    case Err(_):
        expect(false)

match manager.get_task(task_id):
    case Some(task):
        expect(task.status == TaskStatus.Running)
        expect(task.started_at.is_some())
    case nil:
        expect(false)

expect(manager.running_count == 1)
```

</details>

#### updates progress

- updates progress


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("updates progress")
var manager = TaskManager(tasks: {}, running_count: 0, max_concurrent_tasks: 10, next_id: 0)
val task_id = manager.create_task("op")
manager.start_task(task_id)

var result = manager.update_progress(task_id, 50, 100)
match result:
    case Ok(_):
        expect(true)
    case Err(_):
        expect(false)

match manager.get_task(task_id):
    case Some(task):
        match task.progress:
            case Some(p):
                expect(p.current == 50)
            case nil:
                expect(false)
    case nil:
        expect(false)
```

</details>

#### updates progress with message

- updates progress with message


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("updates progress with message")
var manager = TaskManager(tasks: {}, running_count: 0, max_concurrent_tasks: 10, next_id: 0)
val task_id = manager.create_task("op")
manager.start_task(task_id)

var result = manager.update_progress_with_message(task_id, 75, 100, "Almost done")
match result:
    case Ok(_):
        expect(true)
    case Err(_):
        expect(false)
```

</details>

#### completes task

- completes task


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("completes task")
var manager = TaskManager(tasks: {}, running_count: 0, max_concurrent_tasks: 10, next_id: 0)
val task_id = manager.create_task("op")
manager.start_task(task_id)

var result = manager.complete_task(task_id, "success")
match result:
    case Ok(_):
        expect(true)
    case Err(_):
        expect(false)

match manager.get_task(task_id):
    case Some(task):
        expect(task.status == TaskStatus.Completed)
        expect(task.completed_at.is_some())
    case nil:
        expect(false)

expect(manager.running_count == 0)
```

</details>

#### fails task

- fails task


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails task")
var manager = TaskManager(tasks: {}, running_count: 0, max_concurrent_tasks: 10, next_id: 0)
val task_id = manager.create_task("op")
manager.start_task(task_id)

val error = TaskError(code: "ERR", message: "Failed", retryable: false, details: nil)
var result = manager.fail_task(task_id, error)

match result:
    case Ok(_):
        expect(true)
    case Err(_):
        expect(false)

match manager.get_task(task_id):
    case Some(task):
        expect(task.status == TaskStatus.Failed)
        expect(task.error.is_some())
    case nil:
        expect(false)
```

</details>

#### cancels task

- cancels task


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cancels task")
var manager = TaskManager(tasks: {}, running_count: 0, max_concurrent_tasks: 10, next_id: 0)
val task_id = manager.create_task("op")
manager.start_task(task_id)

var result = manager.cancel_task(task_id)
match result:
    case Ok(_):
        expect(true)
    case Err(_):
        expect(false)

match manager.get_task(task_id):
    case Some(task):
        expect(task.status == TaskStatus.Cancelled)
    case nil:
        expect(false)
```

</details>

#### lists all tasks

- lists all tasks


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists all tasks")
var manager = TaskManager(tasks: {}, running_count: 0, max_concurrent_tasks: 10, next_id: 0)
manager.create_task("op1")
manager.create_task("op2")
manager.create_task("op3")

val tasks = manager.list_tasks()
expect(tasks.len() == 3)
```

</details>

#### lists tasks by status

- lists tasks by status


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists tasks by status")
var manager = TaskManager(tasks: {}, running_count: 0, max_concurrent_tasks: 10, next_id: 0)
val id1 = manager.create_task("op1")
val id2 = manager.create_task("op2")
manager.create_task("op3")

manager.start_task(id1)
manager.start_task(id2)

val running = manager.list_tasks_by_status(TaskStatus.Running)
expect(running.len() == 2)

val pending = manager.list_tasks_by_status(TaskStatus.Pending)
expect(pending.len() == 1)
```

</details>

#### respects max concurrent tasks

- respects max concurrent tasks


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("respects max concurrent tasks")
var manager = TaskManager(tasks: {}, running_count: 0, max_concurrent_tasks: 2, next_id: 0)

val id1 = manager.create_task("op1")
val id2 = manager.create_task("op2")
val id3 = manager.create_task("op3")

manager.start_task(id1)
manager.start_task(id2)

var result = manager.start_task(id3)
match result:
    case Ok(_):
        expect(false)
    case Err(e):
        expect(e.category == TaskErrorCategory.RateLimit)
```

</details>

#### cleans up completed tasks

- cleans up completed tasks


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cleans up completed tasks")
var manager = TaskManager(tasks: {}, running_count: 0, max_concurrent_tasks: 10, next_id: 0)
val id1 = manager.create_task("op1")
val id2 = manager.create_task("op2")

manager.start_task(id1)
manager.complete_task(id1, "done")

# Wait a bit for cleanup
manager.cleanup_completed(0)  # Cleanup immediately

expect(manager.list_tasks().len() == 1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/tasks_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering TaskStatus, TaskPriority, TaskProgress, Task, TaskError, TaskManager.
- TaskStatus
- TaskPriority
- TaskProgress
- Task
- TaskError
- TaskManager

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
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

- Canonical SPipe generation for source `f1dae453e05f644503565a1778bf1bc4f6192495f36ccb107393614616d9b4d0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f1dae453e05f644503565a1778bf1bc4f6192495f36ccb107393614616d9b4d0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f1dae453e05f644503565a1778bf1bc4f6192495f36ccb107393614616d9b4d0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/mcp_unit/tasks_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/tasks_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/tasks_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/tasks_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/tasks_spec.spl:299:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts to string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/tasks_spec.spl:309:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'identifies terminal states' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/tasks_spec.spl:320:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts to string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
