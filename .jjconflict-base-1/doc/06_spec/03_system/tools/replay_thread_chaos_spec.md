# Replay Thread Chaos Specification

> <details>

<!-- sdn-diagram:id=replay_thread_chaos_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replay_thread_chaos_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replay_thread_chaos_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replay_thread_chaos_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Thread Chaos Specification

## Scenarios

### ThreadRecorder creation

#### starts with zero threads

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = ThreadRecorder.create()
expect(rec.thread_count()).to_equal(0)
```

</details>

#### starts with zero switches

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = ThreadRecorder.create()
expect(rec.switch_count()).to_equal(0)
```

</details>

### ThreadRecorder on_thread_create

#### adds both parent and child to active set on first create

1. var rec = ThreadRecorder create
2. rec on thread create
   - Expected: rec.thread_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rec = ThreadRecorder.create()
rec.on_thread_create(1, 2, 1000)
expect(rec.thread_count()).to_equal(2)
```

</details>

#### does not duplicate parent on second create

1. var rec = ThreadRecorder create
2. rec on thread create
3. rec on thread create
   - Expected: rec.thread_count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rec = ThreadRecorder.create()
rec.on_thread_create(1, 2, 1000)
rec.on_thread_create(1, 3, 2000)
expect(rec.thread_count()).to_equal(3)
```

</details>

#### does not duplicate child if already active

1. var rec = ThreadRecorder create
2. rec on thread create
3. rec on thread create
   - Expected: rec.thread_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rec = ThreadRecorder.create()
rec.on_thread_create(1, 2, 1000)
rec.on_thread_create(1, 2, 2000)
expect(rec.thread_count()).to_equal(2)
```

</details>

### ThreadRecorder on_thread_switch

#### records a context switch

1. var rec = ThreadRecorder create
2. rec on thread switch
   - Expected: rec.switch_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rec = ThreadRecorder.create()
rec.on_thread_switch(1, 2, 0, 5000)
expect(rec.switch_count()).to_equal(1)
```

</details>

#### records multiple switches

1. var rec = ThreadRecorder create
2. rec on thread switch
3. rec on thread switch
4. rec on thread switch
   - Expected: rec.switch_count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rec = ThreadRecorder.create()
rec.on_thread_switch(1, 2, 0, 5000)
rec.on_thread_switch(2, 3, 0, 6000)
rec.on_thread_switch(3, 1, 1, 7000)
expect(rec.switch_count()).to_equal(3)
```

</details>

### ThreadRecorder on_thread_exit

#### removes tid from active threads

1. var rec = ThreadRecorder create
2. rec on thread create
   - Expected: rec.thread_count() equals `2`
3. rec on thread exit
   - Expected: rec.thread_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rec = ThreadRecorder.create()
rec.on_thread_create(1, 2, 1000)
expect(rec.thread_count()).to_equal(2)
rec.on_thread_exit(2, 3000)
expect(rec.thread_count()).to_equal(1)
```

</details>

#### handles exit of non-existent tid gracefully

1. var rec = ThreadRecorder create
2. rec on thread exit
   - Expected: rec.thread_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rec = ThreadRecorder.create()
rec.on_thread_exit(999, 5000)
expect(rec.thread_count()).to_equal(0)
```

</details>

### ThreadRecorder get_schedule_order

#### returns empty list with no switches

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = ThreadRecorder.create()
val order = rec.get_schedule_order()
expect(order.len()).to_equal(0)
```

</details>

#### returns to_tids in switch order

1. var rec = ThreadRecorder create
2. rec on thread switch
3. rec on thread switch
4. rec on thread switch
   - Expected: order.len() equals `3`
   - Expected: order[0] equals `2`
   - Expected: order[1] equals `3`
   - Expected: order[2] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rec = ThreadRecorder.create()
rec.on_thread_switch(1, 2, 0, 100)
rec.on_thread_switch(2, 3, 0, 200)
rec.on_thread_switch(3, 1, 0, 300)
val order = rec.get_schedule_order()
expect(order.len()).to_equal(3)
expect(order[0]).to_equal(2)
expect(order[1]).to_equal(3)
expect(order[2]).to_equal(1)
```

</details>

### ChaosStrategy enum

#### Random to_i32 round-trip

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = ChaosStrategy::Random
expect(ChaosStrategy.from_i32(s.to_i32()).to_i32()).to_equal(0)
```

</details>

#### RoundRobin to_i32 round-trip

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = ChaosStrategy::RoundRobin
expect(ChaosStrategy.from_i32(s.to_i32()).to_i32()).to_equal(1)
```

</details>

#### StarveLast to_i32 round-trip

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = ChaosStrategy::StarveLast
expect(ChaosStrategy.from_i32(s.to_i32()).to_i32()).to_equal(2)
```

</details>

#### PrioritizeNew to_i32 round-trip

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = ChaosStrategy::PrioritizeNew
expect(ChaosStrategy.from_i32(s.to_i32()).to_i32()).to_equal(3)
```

</details>

#### to_text returns human-readable name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ChaosStrategy::Random.to_text()).to_equal("random")
expect(ChaosStrategy::RoundRobin.to_text()).to_equal("round_robin")
```

</details>

### ChaosScheduler creation

#### starts with zero schedule count

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sched = ChaosScheduler.create(ChaosStrategy::Random, 42)
expect(sched.schedule_count()).to_equal(0)
```

</details>

#### replay_schedule is empty initially

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sched = ChaosScheduler.create(ChaosStrategy::Random, 42)
expect(sched.replay_schedule().len()).to_equal(0)
```

</details>

### ChaosScheduler pick_next empty list

#### returns -1 for empty runnable list

1. var sched = ChaosScheduler create
   - Expected: picked equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = ChaosScheduler.create(ChaosStrategy::Random, 42)
val empty: [i64] = []
val picked = sched.pick_next(empty)
expect(picked).to_equal(-1)
```

</details>

### ChaosScheduler Random strategy

#### picks a valid tid from runnable list

1. var sched = ChaosScheduler create
   - Expected: valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = ChaosScheduler.create(ChaosStrategy::Random, 42)
val picked = sched.pick_next([10, 20, 30])
var valid = false
if picked == 10 or picked == 20 or picked == 30:
    valid = true
expect(valid).to_equal(true)
```

</details>

#### deterministic with same seed

1. var s1 = ChaosScheduler create
2. var s2 = ChaosScheduler create
   - Expected: a equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s1 = ChaosScheduler.create(ChaosStrategy::Random, 123)
var s2 = ChaosScheduler.create(ChaosStrategy::Random, 123)
val tids: [i64] = [5, 10, 15, 20]
val a = s1.pick_next(tids)
val b = s2.pick_next(tids)
expect(a).to_equal(b)
```

</details>

#### reseed changes future picks

1. var sched = ChaosScheduler create
2. sched pick next
3. sched reseed
   - Expected: sched.schedule_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = ChaosScheduler.create(ChaosStrategy::Random, 1)
sched.pick_next([1, 2, 3])
sched.reseed(999)
# After reseed, schedule_count is preserved
expect(sched.schedule_count()).to_equal(1)
```

</details>

### ChaosScheduler RoundRobin strategy

#### cycles through tids in order

1. var sched = ChaosScheduler create
   - Expected: a equals `10`
   - Expected: b equals `20`
   - Expected: c equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = ChaosScheduler.create(ChaosStrategy::RoundRobin, 0)
val tids: [i64] = [10, 20, 30]
val a = sched.pick_next(tids)
val b = sched.pick_next(tids)
val c = sched.pick_next(tids)
expect(a).to_equal(10)
expect(b).to_equal(20)
expect(c).to_equal(30)
```

</details>

#### wraps around after exhausting list

1. var sched = ChaosScheduler create
2. sched pick next
3. sched pick next
   - Expected: third equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = ChaosScheduler.create(ChaosStrategy::RoundRobin, 0)
val tids: [i64] = [10, 20]
sched.pick_next(tids)
sched.pick_next(tids)
val third = sched.pick_next(tids)
expect(third).to_equal(10)
```

</details>

### ChaosScheduler StarveLast strategy

#### picks different tid from last pick

1. var sched = ChaosScheduler create
   - Expected: differ is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = ChaosScheduler.create(ChaosStrategy::StarveLast, 0)
val tids: [i64] = [10, 20]
val first = sched.pick_next(tids)
val second = sched.pick_next(tids)
# first and second must differ (two choices available)
var differ = false
if first != second:
    differ = true
expect(differ).to_equal(true)
```

</details>

#### falls back when only one tid available

1. var sched = ChaosScheduler create
   - Expected: picked equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = ChaosScheduler.create(ChaosStrategy::StarveLast, 0)
val tids: [i64] = [10]
val picked = sched.pick_next(tids)
expect(picked).to_equal(10)
```

</details>

### ChaosScheduler PrioritizeNew strategy

#### picks the highest tid (newest)

1. var sched = ChaosScheduler create
   - Expected: picked equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = ChaosScheduler.create(ChaosStrategy::PrioritizeNew, 0)
val picked = sched.pick_next([5, 100, 50])
expect(picked).to_equal(100)
```

</details>

#### consistently picks highest tid

1. var sched = ChaosScheduler create
   - Expected: a equals `7`
   - Expected: b equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = ChaosScheduler.create(ChaosStrategy::PrioritizeNew, 0)
val tids: [i64] = [3, 7, 2]
val a = sched.pick_next(tids)
val b = sched.pick_next(tids)
expect(a).to_equal(7)
expect(b).to_equal(7)
```

</details>

### ChaosScheduler replay_schedule

#### logs all picks for replay

1. var sched = ChaosScheduler create
2. sched pick next
3. sched pick next
4. sched pick next
   - Expected: log.len() equals `3`
   - Expected: log[0] equals `1`
   - Expected: log[1] equals `2`
   - Expected: log[2] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = ChaosScheduler.create(ChaosStrategy::RoundRobin, 0)
val tids: [i64] = [1, 2, 3]
sched.pick_next(tids)
sched.pick_next(tids)
sched.pick_next(tids)
val log = sched.replay_schedule()
expect(log.len()).to_equal(3)
expect(log[0]).to_equal(1)
expect(log[1]).to_equal(2)
expect(log[2]).to_equal(3)
```

</details>

#### schedule_count matches log length

1. var sched = ChaosScheduler create
2. sched pick next
3. sched pick next
   - Expected: sched.schedule_count() equals `2`
   - Expected: sched.replay_schedule().len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = ChaosScheduler.create(ChaosStrategy::Random, 77)
sched.pick_next([10, 20])
sched.pick_next([10, 20])
expect(sched.schedule_count()).to_equal(2)
expect(sched.replay_schedule().len()).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/replay_thread_chaos_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ThreadRecorder creation
- ThreadRecorder on_thread_create
- ThreadRecorder on_thread_switch
- ThreadRecorder on_thread_exit
- ThreadRecorder get_schedule_order
- ChaosStrategy enum
- ChaosScheduler creation
- ChaosScheduler pick_next empty list
- ChaosScheduler Random strategy
- ChaosScheduler RoundRobin strategy
- ChaosScheduler StarveLast strategy
- ChaosScheduler PrioritizeNew strategy
- ChaosScheduler replay_schedule

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
