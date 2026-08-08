# Task Specification

> <details>

<!-- sdn-diagram:id=task_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=task_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

task_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=task_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Task Specification

## Scenarios

### Task

#### TCB.empty has IDLE state and default priority

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = TCB.empty(5)
expect(t.id).to_equal(5)
expect(t.state).to_equal(TASK_STATE_IDLE)
expect(t.priority).to_equal(7)
expect(t.stack_ptr).to_equal(0)
expect(t.name).to_equal("")
```

</details>

#### TCB constructs with all fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = TCB(id: 3, priority: 2, state: TASK_STATE_READY, stack_ptr: 4096, entry_fn: 100, name: "worker")
expect(t.id).to_equal(3)
expect(t.priority).to_equal(2)
expect(t.name).to_equal("worker")
```

</details>

#### task_table_init creates MAX_TASKS empty slots

1. task table init
   - Expected: get_count() equals `0`
   - Expected: get_table_len() equals `16`
   - Expected: first.state equals `TASK_STATE_IDLE`
   - Expected: last.state equals `TASK_STATE_IDLE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
task_table_init()
expect(get_count()).to_equal(0)
expect(get_table_len()).to_equal(16)
val first = task_get(0)
val last = task_get(15)
expect(first.state).to_equal(TASK_STATE_IDLE)
expect(last.state).to_equal(TASK_STATE_IDLE)
```

</details>

#### task_create returns valid id

1. task table init
   - Expected: id equals `0`
   - Expected: get_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
task_table_init()
val id = task_create(2, 100, "t1")
expect(id).to_equal(0)
expect(get_count()).to_equal(1)
```

</details>

#### task_create sets state to READY

1. task table init
   - Expected: t.state equals `TASK_STATE_READY`
   - Expected: t.priority equals `1`
   - Expected: t.name equals `t2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
task_table_init()
val id = task_create(1, 200, "t2")
val t = task_get(id)
expect(t.state).to_equal(TASK_STATE_READY)
expect(t.priority).to_equal(1)
expect(t.name).to_equal("t2")
```

</details>

#### task_get retrieves correct TCB

1. task table init
   - Expected: t.name equals `getter`
   - Expected: t.priority equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
task_table_init()
val id = task_create(3, 300, "getter")
val t = task_get(id)
expect(t.name).to_equal("getter")
expect(t.priority).to_equal(3)
```

</details>

#### task_delete marks slot as idle

1. task table init
   - Expected: get_count() equals `1`
2. task delete
   - Expected: get_count() equals `0`
   - Expected: t.state equals `TASK_STATE_IDLE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
task_table_init()
val id = task_create(0, 400, "del")
expect(get_count()).to_equal(1)
task_delete(id)
expect(get_count()).to_equal(0)
val t = task_get(id)
expect(t.state).to_equal(TASK_STATE_IDLE)
```

</details>

#### task_set_state changes state

1. task table init
2. task set state
   - Expected: t1.state equals `TASK_STATE_RUNNING`
3. task set state
   - Expected: t2.state equals `TASK_STATE_BLOCKED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
task_table_init()
val id = task_create(1, 500, "st")
task_set_state(id, TASK_STATE_RUNNING)
val t1 = task_get(id)
expect(t1.state).to_equal(TASK_STATE_RUNNING)
task_set_state(id, TASK_STATE_BLOCKED)
val t2 = task_get(id)
expect(t2.state).to_equal(TASK_STATE_BLOCKED)
```

</details>

#### task_set_stack_ptr updates stack pointer

1. task table init
2. task set stack ptr
   - Expected: t.stack_ptr equals `8192`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
task_table_init()
val id = task_create(1, 600, "sp")
task_set_stack_ptr(id, 8192)
val t = task_get(id)
expect(t.stack_ptr).to_equal(8192)
```

</details>

#### MAX_TASKS limit returns INVALID_TASK

1. task table init
   - Expected: get_count() equals `16`
   - Expected: overflow equals `INVALID_TASK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
task_table_init()
val last = fill_table()
expect(get_count()).to_equal(16)
val overflow = task_create(0, 999, "overflow")
expect(overflow).to_equal(INVALID_TASK)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/realtime/task_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Task

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
