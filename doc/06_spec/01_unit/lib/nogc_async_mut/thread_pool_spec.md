# Thread Pool Specification

> <details>

<!-- sdn-diagram:id=thread_pool_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=thread_pool_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

thread_pool_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=thread_pool_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Thread Pool Specification

## Scenarios

### Thread Pool Task Registry

#### allocates non-zero task ids

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val first = next_task_id()
val second = next_task_id()
expect(first > 0).to_equal(true)
expect(second > first).to_equal(true)
```

</details>

#### registers value callbacks by task id

1. register value task callback
   - Expected: callback.? is true
   - Expected: callback?() equals `41`


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val task_id = next_task_id()
register_value_task_callback(task_id, value_41)
val callback = get_value_task_callback(task_id)
expect(callback.?).to_equal(true)
expect(callback?()).to_equal(41)
```

</details>

#### records task completion and result

1. mark task done
   - Expected: task_is_done(task_id) is true
   - Expected: task_result(task_id) equals `77`


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val task_id = next_task_id()
expect(task_is_done(task_id)).to_equal(false)
mark_task_done(task_id, 77)
expect(task_is_done(task_id)).to_equal(true)
expect(task_result(task_id)).to_equal(77)
```

</details>

#### joins an already completed pool task handle

1. mark task done
   - Expected: handle.is_done() is true
   - Expected: handle.id() equals `task_id`
   - Expected: handle.join() equals `123`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val task_id = next_task_id()
mark_task_done(task_id, 123)
val handle = TaskHandle(task_id: task_id)
expect(handle.is_done()).to_equal(true)
expect(handle.id()).to_equal(task_id)
expect(handle.join()).to_equal(123)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/thread_pool_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Thread Pool Task Registry

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
