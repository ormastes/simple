# Green Thread Specification

> <details>

<!-- sdn-diagram:id=green_thread_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=green_thread_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

green_thread_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=green_thread_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Green Thread Specification

## Scenarios

### OS Thread and Green Thread APIs

#### keeps OS thread runtime spawning available

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handle = rt_thread_spawn_isolated(\: 42)
expect(rt_thread_join(handle)).to_equal(42)
```

</details>

#### schedules green thread without completing immediately

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val before = green_ready_count()
val handle = green_spawn(green_value_7)
expect(handle.is_done()).to_equal(false)
expect(green_ready_count()).to_equal(before + 1)
expect(green_run_one()).to_equal(true)
expect(handle.is_done()).to_equal(true)
expect(handle.join()).to_equal(7)
```

</details>

#### runs multiple green threads cooperatively

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h1 = green_spawn(green_value_7)
val h2 = green_spawn(green_value_11)
val ran = green_run_all()
expect(ran >= 2).to_equal(true)
expect(h1.join()).to_equal(7)
expect(h2.join()).to_equal(11)
```

</details>

#### schedules precomputed values through the green queue

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handle = green_spawn_value(23)
expect(handle.is_done()).to_equal(false)
expect(green_run_one()).to_equal(true)
expect(handle.is_done()).to_equal(true)
expect(handle.join()).to_equal(23)
```

</details>

#### runs more than eight precomputed values without slot overwrite

- green run all
   - Expected: total equals `45`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h0 = green_spawn_value(0)
val h1 = green_spawn_value(1)
val h2 = green_spawn_value(2)
val h3 = green_spawn_value(3)
val h4 = green_spawn_value(4)
val h5 = green_spawn_value(5)
val h6 = green_spawn_value(6)
val h7 = green_spawn_value(7)
val h8 = green_spawn_value(8)
val h9 = green_spawn_value(9)
green_run_all()
val total = h0.join() + h1.join() + h2.join() + h3.join() + h4.join() + h5.join() + h6.join() + h7.join() + h8.join() + h9.join()
expect(total).to_equal(45)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/green_thread_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- OS Thread and Green Thread APIs

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
