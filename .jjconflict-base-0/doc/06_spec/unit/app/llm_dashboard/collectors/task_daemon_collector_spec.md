# Task Daemon Collector Specification

> <details>

<!-- sdn-diagram:id=task_daemon_collector_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=task_daemon_collector_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

task_daemon_collector_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=task_daemon_collector_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Task Daemon Collector Specification

## Scenarios

### _parse_task_file: key=value parsing

#### parses id field

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "id=abc-123\ncommand=bin/simple test\nstatus=working\n"
val task = _parse_task_file("abc-123.task", content)
expect(task.id).to_equal("abc-123")
```

</details>

#### parses command field

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "id=task-1\ncommand=bin/simple build\nstatus=completed\n"
val task = _parse_task_file("task-1.task", content)
expect(task.command).to_equal("bin/simple build")
```

</details>

#### maps status=working to TaskState.Active

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "id=t1\ncommand=echo hi\nstatus=working\n"
val task = _parse_task_file("t1.task", content)
expect(task_state_name(task.state)).to_equal("active")
```

</details>

#### maps status=completed to TaskState.Completed

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "id=t2\ncommand=echo done\nstatus=completed\n"
val task = _parse_task_file("t2.task", content)
expect(task_state_name(task.state)).to_equal("done")
```

</details>

#### maps status=failed to TaskState.Failed

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "id=t3\ncommand=false\nstatus=failed\n"
val task = _parse_task_file("t3.task", content)
expect(task_state_name(task.state)).to_equal("failed")
```

</details>

#### maps status=cancelled to TaskState.Cancelled

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "id=t4\ncommand=cancel\nstatus=cancelled\n"
val task = _parse_task_file("t4.task", content)
expect(task_state_name(task.state)).to_equal("cancelled")
```

</details>

#### sets kind to TaskKind.Job

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "id=t5\ncommand=run\nstatus=working\n"
val task = _parse_task_file("t5.task", content)
expect(task_kind_name(task.kind)).to_equal("job")
```

</details>

#### handles missing fields gracefully (no crash)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "id=t6\n"
val task = _parse_task_file("t6.task", content)
expect(task.id).to_equal("t6")
expect(task.command).to_equal("")
```

</details>

#### handles empty content without crashing

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val task = _parse_task_file("empty.task", "")
expect(task.id.len() >= 0).to_equal(true)
```

</details>

### collect_task_daemon_tasks: file-system read

#### returns a list (possibly empty if no task daemon dir)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tasks = collect_task_daemon_tasks()
expect(tasks.len() >= 0).to_equal(true)
```

</details>

#### all returned tasks have kind Job

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
