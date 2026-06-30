# Tasks Specification

> <details>

<!-- sdn-diagram:id=tasks_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tasks_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tasks_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tasks_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tasks Specification

## Scenarios

### TaskStatus

#### converts to string

- assert true
- assert true
- assert true
- assert true
- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_true(TaskStatus.Pending.to_string() == "pending")
assert_true(TaskStatus.Running.to_string() == "running")
assert_true(TaskStatus.Completed.to_string() == "completed")
assert_true(TaskStatus.Failed.to_string() == "failed")
assert_true(TaskStatus.Cancelled.to_string() == "cancelled")
assert_true(TaskStatus.TimedOut.to_string() == "timed_out")
```

</details>

#### identifies terminal states

- assert false
- assert false
- assert true
- assert true
- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_false(TaskStatus.Pending.is_terminal())
assert_false(TaskStatus.Running.is_terminal())
assert_true(TaskStatus.Completed.is_terminal())
assert_true(TaskStatus.Failed.is_terminal())
assert_true(TaskStatus.Cancelled.is_terminal())
assert_true(TaskStatus.TimedOut.is_terminal())
```

</details>

### TaskPriority

#### converts to string

- assert true
- assert true
- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_true(TaskPriority.Low.to_string() == "low")
assert_true(TaskPriority.Normal.to_string() == "normal")
assert_true(TaskPriority.High.to_string() == "high")
assert_true(TaskPriority.Critical.to_string() == "critical")
```

</details>

#### converts to numeric

- assert true
- assert true
- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_true(TaskPriority.Low.to_i64() == 0)
assert_true(TaskPriority.Normal.to_i64() == 1)
assert_true(TaskPriority.High.to_i64() == 2)
assert_true(TaskPriority.Critical.to_i64() == 3)
```

</details>

### TaskProgress

#### creates basic progress

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val progress = TaskProgress(current: 50, total: nil, message: nil, percentage: nil)
assert_true(progress.current == 50)
```

</details>

#### adds total for percentage

- var p0 = TaskProgress
- assert true
- assert true
- assert true
- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p0 = TaskProgress(current: 25, total: nil, message: nil, percentage: nil)
val progress = p0.with_total(100)
assert_true(progress.current == 25)

match progress.total:
    case Some(t):
        assert_true(t == 100)
    case nil:
        assert_true(false)

match progress.percentage:
    case Some(p):
        assert_true(p == 25.0)
    case nil:
        assert_true(false)
```

</details>

#### adds message

- var p0 = TaskProgress
- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p0 = TaskProgress(current: 10, total: nil, message: nil, percentage: nil)
val progress = p0.with_message("Processing...")

match progress.message:
    case Some(m):
        assert_true(m == "Processing...")
    case nil:
        assert_true(false)
```

</details>

#### converts to dict

- var p0 = TaskProgress
- var p1 = p0 with total
- assert true
- assert true
- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p0 = TaskProgress(current: 50, total: nil, message: nil, percentage: nil)
var p1 = p0.with_total(100)
val progress = p1.with_message("Half done")
val dict = progress.to_dict()

assert_true(dict.get("current") == 50)
assert_true(dict.has("total"))
assert_true(dict.has("message"))
assert_true(dict.has("percentage"))
```

</details>

### Task

#### creates new task

- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val task = Task(id: "task_1", operation: "test_operation", status: TaskStatus.Pending, priority: TaskPriority.Normal, timeout_ms: nil, started_at: nil, completed_at: nil, progress: nil, error: nil)
assert_true(task.id == "task_1")
assert_true(task.operation == "test_operation")
```

</details>

#### sets priority

- var t0 = Task
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t0 = Task(id: "task_1", operation: "op", status: TaskStatus.Pending, priority: TaskPriority.Normal, timeout_ms: nil, started_at: nil, completed_at: nil, progress: nil, error: nil)
val task = t0.with_priority(TaskPriority.High)
assert_true(task.priority == TaskPriority.High)
```

</details>

#### sets timeout

- var t0 = Task
- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t0 = Task(id: "task_1", operation: "op", status: TaskStatus.Pending, priority: TaskPriority.Normal, timeout_ms: nil, started_at: nil, completed_at: nil, progress: nil, error: nil)
val task = t0.with_timeout(5000)

match task.timeout_ms:
    case Some(t):
        assert_true(t == 5000)
    case nil:
        assert_true(false)
```

</details>

#### checks running state

- var task = Task
- assert false
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var task = Task(id: "task_1", operation: "op", status: TaskStatus.Pending, priority: TaskPriority.Normal, timeout_ms: nil, started_at: nil, completed_at: nil, progress: nil, error: nil)
assert_false(task.is_running())

# Simulate starting
task.status = TaskStatus.Running
assert_true(task.is_running())
```

</details>

#### checks complete state

- var task = Task
- assert false
- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var task = Task(id: "task_1", operation: "op", status: TaskStatus.Pending, priority: TaskPriority.Normal, timeout_ms: nil, started_at: nil, completed_at: nil, progress: nil, error: nil)
assert_false(task.is_complete())

task.status = TaskStatus.Completed
assert_true(task.is_complete())

task.status = TaskStatus.Failed
assert_true(task.is_complete())
```

</details>

#### converts to dict

- var t0 = Task
- assert true
- assert true
- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t0 = Task(id: "task_1", operation: "test", status: TaskStatus.Pending, priority: TaskPriority.Normal, timeout_ms: nil, started_at: nil, completed_at: nil, progress: nil, error: nil)
val task = t0.with_priority(TaskPriority.High)
val dict = task.to_dict()

assert_true(dict.get("id") == "task_1")
assert_true(dict.get("operation") == "test")
assert_true(dict.get("status") == "pending")
assert_true(dict.get("priority") == "high")
```

</details>

### TaskError

#### creates error

- assert true
- assert true
- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error = TaskError(code: "ERR_001", message: "Something went wrong", retryable: false, details: nil)
assert_true(error.code == "ERR_001")
assert_true(error.message == "Something went wrong")
assert_false(error.retryable)
```

</details>

#### adds details

- var e0 = TaskError
- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var e0 = TaskError(code: "ERR", message: "msg", retryable: false, details: nil)
val error = e0.with_details("extra info")

match error.details:
    case Some(d):
        assert_true(d == "extra info")
    case nil:
        assert_true(false)
```

</details>

#### marks as retryable

- var e0 = TaskError
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var e0 = TaskError(code: "ERR", message: "msg", retryable: false, details: nil)
val error = e0.as_retryable()
assert_true(error.retryable)
```

</details>

#### converts to MCP error

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error = TaskError(code: "timeout", message: "Operation timed out", retryable: false, details: nil)
val mcp_error = error.to_mcp_error()
assert_true(mcp_error.category == ErrorCategory.Tool)
```

</details>

### TaskManager

#### creates task manager

- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manager = TaskManager(tasks: {}, running_count: 0, max_concurrent_tasks: 10, next_id: 0)
assert_true(manager.running_count == 0)
assert_true(manager.max_concurrent_tasks == 10)
```

</details>

#### creates task

- var manager = TaskManager
- assert true
- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manager = TaskManager(tasks: {}, running_count: 0, max_concurrent_tasks: 10, next_id: 0)
val task_id = manager.create_task("test_operation")
assert_true(task_id.starts_with("task_"))

match manager.get_task(task_id):
    case Some(task):
        assert_true(task.operation == "test_operation")
    case nil:
        assert_true(false)
```

</details>

#### creates task with options

- var manager = TaskManager
- Some
- assert true
- assert true
- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manager = TaskManager(tasks: {}, running_count: 0, max_concurrent_tasks: 10, next_id: 0)
val task_id = manager.create_task_with_options(
    "important_op",
    TaskPriority.Critical,
    Some(30000)
)

match manager.get_task(task_id):
    case Some(task):
        assert_true(task.priority == TaskPriority.Critical)
        match task.timeout_ms:
            case Some(t):
                assert_true(t == 30000)
            case nil:
                assert_true(false)
    case nil:
        assert_true(false)
```

</details>

#### starts task

- var manager = TaskManager
- var result = manager start task
- assert true
- assert true
- assert true
- assert true
- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manager = TaskManager(tasks: {}, running_count: 0, max_concurrent_tasks: 10, next_id: 0)
val task_id = manager.create_task("op")

var result = manager.start_task(task_id)
match result:
    case Ok(_):
        assert_true(true)
    case Err(_):
        assert_true(false)

match manager.get_task(task_id):
    case Some(task):
        assert_true(task.status == TaskStatus.Running)
        assert_true(task.started_at.is_some())
    case nil:
        assert_true(false)

assert_true(manager.running_count == 1)
```

</details>

#### updates progress

- var manager = TaskManager
- manager start task
- var result = manager update progress
- assert true
- assert true
- assert true
- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manager = TaskManager(tasks: {}, running_count: 0, max_concurrent_tasks: 10, next_id: 0)
val task_id = manager.create_task("op")
manager.start_task(task_id)

var result = manager.update_progress(task_id, 50, 100)
match result:
    case Ok(_):
        assert_true(true)
    case Err(_):
        assert_true(false)

match manager.get_task(task_id):
    case Some(task):
        match task.progress:
            case Some(p):
                assert_true(p.current == 50)
            case nil:
                assert_true(false)
    case nil:
        assert_true(false)
```

</details>

#### updates progress with message

- var manager = TaskManager
- manager start task
- var result = manager update progress with message
- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manager = TaskManager(tasks: {}, running_count: 0, max_concurrent_tasks: 10, next_id: 0)
val task_id = manager.create_task("op")
manager.start_task(task_id)

var result = manager.update_progress_with_message(task_id, 75, 100, "Almost done")
match result:
    case Ok(_):
        assert_true(true)
    case Err(_):
        assert_true(false)
```

</details>

#### completes task

- var manager = TaskManager
- manager start task
- var result = manager complete task
- assert true
- assert true
- assert true
- assert true
- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manager = TaskManager(tasks: {}, running_count: 0, max_concurrent_tasks: 10, next_id: 0)
val task_id = manager.create_task("op")
manager.start_task(task_id)

var result = manager.complete_task(task_id, "success")
match result:
    case Ok(_):
        assert_true(true)
    case Err(_):
        assert_true(false)

match manager.get_task(task_id):
    case Some(task):
        assert_true(task.status == TaskStatus.Completed)
        assert_true(task.completed_at.is_some())
    case nil:
        assert_true(false)

assert_true(manager.running_count == 0)
```

</details>

#### fails task

- var manager = TaskManager
- manager start task
- var result = manager fail task
- assert true
- assert true
- assert true
- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manager = TaskManager(tasks: {}, running_count: 0, max_concurrent_tasks: 10, next_id: 0)
val task_id = manager.create_task("op")
manager.start_task(task_id)

val error = TaskError(code: "ERR", message: "Failed", retryable: false, details: nil)
var result = manager.fail_task(task_id, error)

match result:
    case Ok(_):
        assert_true(true)
    case Err(_):
        assert_true(false)

match manager.get_task(task_id):
    case Some(task):
        assert_true(task.status == TaskStatus.Failed)
        assert_true(task.error.is_some())
    case nil:
        assert_true(false)
```

</details>

#### cancels task

- var manager = TaskManager
- manager start task
- var result = manager cancel task
- assert true
- assert true
- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manager = TaskManager(tasks: {}, running_count: 0, max_concurrent_tasks: 10, next_id: 0)
val task_id = manager.create_task("op")
manager.start_task(task_id)

var result = manager.cancel_task(task_id)
match result:
    case Ok(_):
        assert_true(true)
    case Err(_):
        assert_true(false)

match manager.get_task(task_id):
    case Some(task):
        assert_true(task.status == TaskStatus.Cancelled)
    case nil:
        assert_true(false)
```

</details>

#### lists all tasks

- var manager = TaskManager
- manager create task
- manager create task
- manager create task
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manager = TaskManager(tasks: {}, running_count: 0, max_concurrent_tasks: 10, next_id: 0)
manager.create_task("op1")
manager.create_task("op2")
manager.create_task("op3")

val tasks = manager.list_tasks()
assert_true(tasks.len() == 3)
```

</details>

#### lists tasks by status

- var manager = TaskManager
- manager create task
- manager start task
- manager start task
- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manager = TaskManager(tasks: {}, running_count: 0, max_concurrent_tasks: 10, next_id: 0)
val id1 = manager.create_task("op1")
val id2 = manager.create_task("op2")
manager.create_task("op3")

manager.start_task(id1)
manager.start_task(id2)

val running = manager.list_tasks_by_status(TaskStatus.Running)
assert_true(running.len() == 2)

val pending = manager.list_tasks_by_status(TaskStatus.Pending)
assert_true(pending.len() == 1)
```

</details>

#### respects max concurrent tasks

- var manager = TaskManager
- manager start task
- manager start task
- var result = manager start task
- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manager = TaskManager(tasks: {}, running_count: 0, max_concurrent_tasks: 2, next_id: 0)

val id1 = manager.create_task("op1")
val id2 = manager.create_task("op2")
val id3 = manager.create_task("op3")

manager.start_task(id1)
manager.start_task(id2)

var result = manager.start_task(id3)
match result:
    case Ok(_):
        assert_true(false)
    case Err(e):
        assert_true(e.category == ErrorCategory.RateLimit)
```

</details>

#### cleans up completed tasks

- var manager = TaskManager
- manager start task
- manager complete task
- manager cleanup completed
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var manager = TaskManager(tasks: {}, running_count: 0, max_concurrent_tasks: 10, next_id: 0)
val id1 = manager.create_task("op1")
val id2 = manager.create_task("op2")

manager.start_task(id1)
manager.complete_task(id1, "done")

# Wait a bit for cleanup
manager.cleanup_completed(0)  # Cleanup immediately

assert_true(manager.list_tasks().len() == 1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/tasks_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
