# Scheduler Specification

> 1. sched init

<!-- sdn-diagram:id=scheduler_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scheduler_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scheduler_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scheduler_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scheduler Specification

## Scenarios

### Scheduler

#### sched_init starts clean

1. sched init
   - Expected: current_task_id equals `NO_TASK`
   - Expected: priority_bitmap equals `0`
   - Expected: q_empty(0) is true
   - Expected: q_empty(7) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sched_init()
expect(current_task_id).to_equal(NO_TASK)
expect(priority_bitmap).to_equal(0)
expect(q_empty(0)).to_equal(true)
expect(q_empty(7)).to_equal(true)
```

</details>

#### sched_add puts task in correct queue

1. sched init
2. sched add
   - Expected: q_size(3) equals `1`
   - Expected: get_task_state(0) equals `TASK_STATE_READY`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sched_init()
sched_add(0, 3)
expect(q_size(3)).to_equal(1)
expect(get_task_state(0)).to_equal(TASK_STATE_READY)
```

</details>

#### sched_pick returns highest priority task

1. sched init
2. sched add
3. sched add
4. sched add
   - Expected: sched_pick() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sched_init()
sched_add(5, 4)
sched_add(2, 1)
sched_add(8, 6)
expect(sched_pick()).to_equal(2)
```

</details>

#### priority 0 runs before priority 7

1. sched init
2. sched add
3. sched add
   - Expected: sched_pick() equals `1`
   - Expected: sched_pick() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sched_init()
sched_add(3, 7)
sched_add(1, 0)
expect(sched_pick()).to_equal(1)
expect(sched_pick()).to_equal(3)
```

</details>

#### empty queue returns NO_TASK

1. sched init
   - Expected: sched_pick() equals `NO_TASK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sched_init()
expect(sched_pick()).to_equal(NO_TASK)
```

</details>

#### FIFO within same priority

1. sched init
2. sched add
3. sched add
4. sched add
   - Expected: sched_pick() equals `0`
   - Expected: sched_pick() equals `1`
   - Expected: sched_pick() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sched_init()
sched_add(0, 2)
sched_add(1, 2)
sched_add(4, 2)
expect(sched_pick()).to_equal(0)
expect(sched_pick()).to_equal(1)
expect(sched_pick()).to_equal(4)
```

</details>

#### sched_yield re-queues current task

1. sched init
2. sched add
3. current task id = sched pick
   - Expected: current_task_id equals `0`
4. sched yield
   - Expected: q_size(2) equals `1`
   - Expected: sched_pick() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sched_init()
sched_add(0, 2)
current_task_id = sched_pick()
expect(current_task_id).to_equal(0)
sched_yield()
expect(q_size(2)).to_equal(1)
expect(sched_pick()).to_equal(0)
```

</details>

#### sched_block sets state to BLOCKED

1. sched init
2. sched add
3. sched block
   - Expected: get_task_state(3) equals `TASK_STATE_BLOCKED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sched_init()
sched_add(3, 1)
sched_block(3)
expect(get_task_state(3)).to_equal(TASK_STATE_BLOCKED)
```

</details>

#### sched_unblock returns task to ready queue

1. sched init
2. sched add
3. sched block
   - Expected: get_task_state(5) equals `TASK_STATE_BLOCKED`
4. sched unblock
   - Expected: get_task_state(5) equals `TASK_STATE_READY`
   - Expected: sched_pick() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sched_init()
sched_add(5, 4)
sched_block(5)
expect(get_task_state(5)).to_equal(TASK_STATE_BLOCKED)
sched_unblock(5)
expect(get_task_state(5)).to_equal(TASK_STATE_READY)
expect(sched_pick()).to_equal(5)
```

</details>

#### sched_unblock ignores non-blocked task

1. sched init
2. sched add
3. sched unblock
   - Expected: q_size(3) equals `before_size`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sched_init()
sched_add(2, 3)
val before_size = q_size(3)
sched_unblock(2)
expect(q_size(3)).to_equal(before_size)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/realtime/scheduler_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Scheduler

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
