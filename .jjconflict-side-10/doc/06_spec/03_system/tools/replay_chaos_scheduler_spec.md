# Replay Chaos Scheduler Specification

> <details>

<!-- sdn-diagram:id=replay_chaos_scheduler_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replay_chaos_scheduler_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replay_chaos_scheduler_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replay_chaos_scheduler_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Chaos Scheduler Specification

## Scenarios

### ChaosStrategy to_i32

#### Random to_i32 returns 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = ChaosStrategy::Random
expect(s.to_i32()).to_equal(0)
```

</details>

#### RoundRobin to_i32 returns 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = ChaosStrategy::RoundRobin
expect(s.to_i32()).to_equal(1)
```

</details>

#### StarveLast to_i32 returns 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = ChaosStrategy::StarveLast
expect(s.to_i32()).to_equal(2)
```

</details>

#### PrioritizeNew to_i32 returns 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = ChaosStrategy::PrioritizeNew
expect(s.to_i32()).to_equal(3)
```

</details>

### ChaosScheduler create and schedule_count

#### new scheduler has schedule_count 0

1. var sched = ChaosScheduler create
   - Expected: sched.schedule_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = ChaosScheduler.create(ChaosStrategy::RoundRobin, 42)
expect(sched.schedule_count()).to_equal(0)
```

</details>

#### pick_next on empty tids returns -1

1. var sched = ChaosScheduler create
   - Expected: chosen equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = ChaosScheduler.create(ChaosStrategy::Random, 1)
val chosen = sched.pick_next([])
expect(chosen).to_equal(-1)
```

</details>

#### pick_next with one tid always picks that tid

1. var sched = ChaosScheduler create
   - Expected: chosen equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = ChaosScheduler.create(ChaosStrategy::Random, 99)
val chosen = sched.pick_next([7])
expect(chosen).to_equal(7)
```

</details>

#### RoundRobin pick_next increments schedule_count

1. var sched = ChaosScheduler create
2. sched pick next
3. sched pick next
   - Expected: sched.schedule_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = ChaosScheduler.create(ChaosStrategy::RoundRobin, 0)
sched.pick_next([1, 2, 3])
sched.pick_next([1, 2, 3])
expect(sched.schedule_count()).to_equal(2)
```

</details>

#### PrioritizeNew picks highest tid

1. var sched = ChaosScheduler create
   - Expected: chosen equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = ChaosScheduler.create(ChaosStrategy::PrioritizeNew, 0)
val chosen = sched.pick_next([10, 30, 20])
expect(chosen).to_equal(30)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/replay_chaos_scheduler_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ChaosStrategy to_i32
- ChaosScheduler create and schedule_count

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
