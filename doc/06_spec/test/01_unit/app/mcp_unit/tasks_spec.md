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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TaskStatus.Pending.to_string() == "pending")
expect(TaskStatus.Running.to_string() == "running")
expect(TaskStatus.Completed.to_string() == "completed")
expect(TaskStatus.Failed.to_string() == "failed")
expect(TaskStatus.Cancelled.to_string() == "cancelled")
expect(TaskStatus.TimedOut.to_string() == "timed_out")
```

</details>

#### identifies terminal states

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TaskPriority.Low.to_string() == "low")
expect(TaskPriority.Normal.to_string() == "normal")
expect(TaskPriority.High.to_string() == "high")
expect(TaskPriority.Critical.to_string() == "critical")
```

</details>

#### converts to numeric

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TaskPriority.Low.to_i64() == 0)
expect(TaskPriority.Normal.to_i64() == 1)
expect(TaskPriority.High.to_i64() == 2)
expect(TaskPriority.Critical.to_i64() == 3)
```

</details>

### TaskProgress

#### creates basic progress

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val progress = TaskProgress(current: 50, total: nil, message: nil, percentage: nil)
expect(progress.current == 50)
```

</details>

#### adds total for percentage

1. var p0 = TaskProgress


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var p0 = TaskProgress


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var p0 = TaskProgress
2. var p1 = p0 with total


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val task = Task(id: "task_1", operation: "test_operation", status: TaskStatus.Pending, priority: TaskPriority.Normal, timeout_ms: nil, started_at: nil, completed_at: nil, progress: nil, error: nil)
expect(task.id == "task_1")
expect(task.operation == "test_operation")
```

</details>

#### sets priority

1. var t0 = Task


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t0 = Task(id: "task_1", operation: "op", status: TaskStatus.Pending, priority: TaskPriority.Normal, timeout_ms: nil, started_at: nil, completed_at: nil, progress: nil, error: nil)
val task = t0.with_priority(TaskPriority.High)
expect(task.priority == TaskPriority.High)
```

</details>

#### sets timeout

1. var t0 = Task


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var task = Task


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var task = Task(id: "task_1", operation: "op", status: TaskStatus.Pending, priority: TaskPriority.Normal, timeout_ms: nil, started_at: nil, completed_at: nil, progress: nil, error: nil)
expect(not task.is_running())

# Simulate starting
task.status = TaskStatus.Running
expect(task.is_running())
```

</details>

#### checks complete state

1. var task = Task


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var task = Task(id: "task_1", operation: "op", status: TaskStatus.Pending, priority: TaskPriority.Normal, timeout_ms: nil, started_at: nil, completed_at: nil, progress: nil, error: nil)
expect(not task.is_complete())

task.status = TaskStatus.Completed
expect(task.is_complete())

task.status = TaskStatus.Failed
expect(task.is_complete())
```

</details>

#### converts to dict

1. var t0 = Task


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error = TaskError(code: "ERR_001", message: "Something went wrong", retryable: false, details: nil)
expect(error.code == "ERR_001")
expect(error.message == "Something went wrong")
expect(not error.retryable)
```

</details>

#### adds details

1. var e0 = TaskError


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var e0 = TaskError


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var e0 = TaskError(code: "ERR", message: "msg", retryable: false, details: nil)
val error = e0.as_retryable()
expect(error.retryable)
```

</details>

#### converts to MCP error

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error = TaskError(code: "timeout", message: "Operation timed out", retryable: false, details: nil)
val mcp_error = error.to_mcp_error()
expect(mcp_error.category == ErrorCategory.Tool)
```

</details>

### TaskManager

#### creates task manager

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manager = TaskManager(tasks: {}, running_count: 0, max_concurrent_tasks: 10, next_id: 0)
expect(manager.running_count == 0)
expect(manager.max_concurrent_tasks == 10)
```

</details>

#### creates task

1. var manager = TaskManager


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var manager = TaskManager
2. Some


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

1. var manager = TaskManager
2. var result = manager start task


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

1. var manager = TaskManager
2. manager start task
3. var result = manager update progress


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

1. var manager = TaskManager
2. manager start task
3. var result = manager update progress with message


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
        expect(true)
    case Err(_):
        expect(false)
```

</details>

#### completes task

1. var manager = TaskManager
2. manager start task
3. var result = manager complete task


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

1. var manager = TaskManager
2. manager start task
3. var result = manager fail task


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

1. var manager = TaskManager
2. manager start task
3. var result = manager cancel task


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

1. var manager = TaskManager
2. manager create task
3. manager create task
4. manager create task


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
expect(tasks.len() == 3)
```

</details>

#### lists tasks by status

1. var manager = TaskManager
2. manager create task
3. manager start task
4. manager start task


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
expect(running.len() == 2)

val pending = manager.list_tasks_by_status(TaskStatus.Pending)
expect(pending.len() == 1)
```

</details>

#### respects max concurrent tasks

1. var manager = TaskManager
2. manager start task
3. manager start task
4. var result = manager start task


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
        expect(false)
    case Err(e):
        expect(e.category == ErrorCategory.RateLimit)
```

</details>

#### cleans up completed tasks

1. var manager = TaskManager
2. manager start task
3. manager complete task
4. manager cleanup completed


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

expect(manager.list_tasks().len() == 1)
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
