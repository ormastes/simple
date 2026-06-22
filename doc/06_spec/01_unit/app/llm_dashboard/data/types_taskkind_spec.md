# Types Taskkind Specification

> <details>

<!-- sdn-diagram:id=types_taskkind_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=types_taskkind_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

types_taskkind_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=types_taskkind_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Types Taskkind Specification

## Scenarios

### TaskKind.Job variant

#### task_kind_name returns job for TaskKind.Job

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = task_kind_name(TaskKind.Job)
expect(name).to_equal("job")
```

</details>

<details>
<summary>Advanced: existing Loop variant still works</summary>

#### existing Loop variant still works

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(task_kind_name(TaskKind.Loop)).to_equal("loop")
```

</details>


</details>

#### existing Schedule variant still works

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(task_kind_name(TaskKind.Schedule)).to_equal("schedule")
```

</details>

#### existing Daemon variant still works

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(task_kind_name(TaskKind.Daemon)).to_equal("daemon")
```

</details>

#### existing RemoteControl variant still works

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(task_kind_name(TaskKind.RemoteControl)).to_equal("remote")
```

</details>

#### ManagedTask can be constructed with kind Job

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val task = ManagedTask.new("id1", TaskKind.Job, "test job", "bin/simple test")
expect(task_kind_name(task.kind)).to_equal("job")
expect(task.id).to_equal("id1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_dashboard/data/types_taskkind_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TaskKind.Job variant

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
