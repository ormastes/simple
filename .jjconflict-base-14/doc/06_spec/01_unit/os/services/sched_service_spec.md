# SchedService Specification (G1)

> User-space scheduler policy service. Validates task registration, unregistration, CPU-usage accumulation, runaway-driver demotion, nice clamping, and priority recommendation.

<!-- sdn-diagram:id=sched_service_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sched_service_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sched_service_spec -> std
sched_service_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sched_service_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SchedService Specification (G1)

User-space scheduler policy service. Validates task registration, unregistration, CPU-usage accumulation, runaway-driver demotion, nice clamping, and priority recommendation.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #G1 |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/os/services/sched_service_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

User-space scheduler policy service. Validates task registration,
unregistration, CPU-usage accumulation, runaway-driver demotion,
nice clamping, and priority recommendation.

## Scenarios

### SchedService register

#### register_task returns entity with non-zero id

1. var svc = SchedService new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = SchedService.new()
val e = svc.sched_register_task(1, SCHED_NORMAL, PRIO_NORMAL, 0)
expect(e.id).to_be_greater_than(0)
```

</details>

#### registered task has correct recommend_priority

1. var svc = SchedService new
   - Expected: svc.sched_recommend_priority(2) equals `PRIO_HIGH`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = SchedService.new()
val _e = svc.sched_register_task(2, SCHED_NORMAL, PRIO_HIGH, 0)
expect(svc.sched_recommend_priority(2)).to_equal(PRIO_HIGH)
```

</details>

### SchedService unregister

#### unregister_task returns true for registered task

1. var svc = SchedService new
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = SchedService.new()
val _e = svc.sched_register_task(3, SCHED_NORMAL, PRIO_NORMAL, 0)
val ok = svc.sched_unregister_task(3)
expect(ok).to_equal(true)
```

</details>

#### recommend_priority returns -1 after unregister

1. var svc = SchedService new
   - Expected: svc.sched_recommend_priority(4) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = SchedService.new()
val _e = svc.sched_register_task(4, SCHED_NORMAL, PRIO_NORMAL, 0)
val _ok = svc.sched_unregister_task(4)
expect(svc.sched_recommend_priority(4)).to_equal(-1)
```

</details>

### SchedService record_usage

#### record_usage returns true for registered task

1. var svc = SchedService new
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = SchedService.new()
val _e = svc.sched_register_task(5, SCHED_NORMAL, PRIO_NORMAL, 0)
val ok = svc.sched_record_usage(5, 10)
expect(ok).to_equal(true)
```

</details>

### SchedService runaway driver demotion

#### driver task above threshold is demoted after sched_tick

1. var svc = SchedService new
   - Expected: svc.sched_recommend_priority(6) equals `PRIO_NORMAL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = SchedService.new()
val _e = svc.sched_register_task(6, SCHED_DRIVER, PRIO_HIGH, 0)
val _ok = svc.sched_record_usage(6, 101)
val _tick = svc.sched_tick()
# priority should be demoted from PRIO_HIGH (1) to PRIO_NORMAL (2)
expect(svc.sched_recommend_priority(6)).to_equal(PRIO_NORMAL)
```

</details>

### SchedService nice clamping

#### nice value above 19 is clamped to 19

1. var svc = SchedService new
   - Expected: ok is true
   - Expected: svc.sched_recommend_priority(7) equals `PRIO_NORMAL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = SchedService.new()
val _e = svc.sched_register_task(7, SCHED_NORMAL, PRIO_NORMAL, 100)
# nice is clamped at register time; verify via sched_set_nice
val ok = svc.sched_set_nice(7, 50)
expect(ok).to_equal(true)
# recommend_priority stays the same (nice doesn't change priority directly)
expect(svc.sched_recommend_priority(7)).to_equal(PRIO_NORMAL)
```

</details>

#### nice min/max constants are correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(NICE_MIN).to_equal(-20)
expect(NICE_MAX).to_equal(19)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
