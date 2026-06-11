# Async Host Task Identity Specification

> <details>

<!-- sdn-diagram:id=async_host_task_identity_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=async_host_task_identity_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

async_host_task_identity_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=async_host_task_identity_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async Host Task Identity Specification

## Scenarios

### async host scheduler task identity

#### uses fallback key outside scheduler polling

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(current_scheduler_task_key("fallback-task")).to_equal("fallback-task")
```

</details>

#### uses scheduler owned task key while entered

- exit scheduler task id
   - Expected: current_scheduler_task_key("fallback-task") equals `fallback-task`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val previous = enter_scheduler_task_id(42)
expect(current_scheduler_task_key("fallback-task")).to_equal("scheduler-task-42")
exit_scheduler_task_id(previous)
expect(current_scheduler_task_key("fallback-task")).to_equal("fallback-task")
```

</details>

#### prefers scheduler task key in unified identity

- exit scheduler task id


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val previous = enter_scheduler_task_id(43)
expect(current_unified_task_key("fallback-task")).to_equal("scheduler-task-43")
exit_scheduler_task_id(previous)
```

</details>

#### restores nested scheduler task identity

- exit scheduler task id
   - Expected: current_scheduler_task_key("fallback-task") equals `scheduler-task-7`
- exit scheduler task id
   - Expected: current_scheduler_task_key("fallback-task") equals `fallback-task`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val outer = enter_scheduler_task_id(7)
expect(current_scheduler_task_key("fallback-task")).to_equal("scheduler-task-7")
val inner = enter_scheduler_task_id(9)
expect(current_scheduler_task_key("fallback-task")).to_equal("scheduler-task-9")
exit_scheduler_task_id(inner)
expect(current_scheduler_task_key("fallback-task")).to_equal("scheduler-task-7")
exit_scheduler_task_id(outer)
expect(current_scheduler_task_key("fallback-task")).to_equal("fallback-task")
```

</details>

#### allocates monotonically increasing scheduler task ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val first = allocate_scheduler_task_id()
val second = allocate_scheduler_task_id()
expect(second).to_equal(first + 1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/async_host_task_identity_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- async host scheduler task identity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
