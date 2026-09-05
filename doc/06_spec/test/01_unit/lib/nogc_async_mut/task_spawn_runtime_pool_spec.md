# Task Spawn Runtime Pool Specification

> <details>

<!-- sdn-diagram:id=task_spawn_runtime_pool_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=task_spawn_runtime_pool_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

task_spawn_runtime_pool_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=task_spawn_runtime_pool_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Task Spawn Runtime Pool Specification

## Scenarios

### Runtime pool task_spawn

#### joins multiple pool-backed tasks

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h0 = task_spawn(lcg_work_0)
val h1 = task_spawn(lcg_work_1)
val h2 = task_spawn(lcg_work_2)
val h3 = task_spawn(lcg_work_3)

val got = h0.join() + h1.join() + h2.join() + h3.join()
val expected = lcg_work(0) + lcg_work(1) + lcg_work(2) + lcg_work(3)
expect(got).to_equal(expected)
```

</details>

#### keeps join idempotent after completion

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handle = task_spawn(lcg_work_0)
val first = handle.join()
val second = handle.join()

expect(second).to_equal(first)
expect(handle.is_done()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/task_spawn_runtime_pool_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Runtime pool task_spawn

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
