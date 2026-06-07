# Scheduler Green Carrier Parallelism Specification

> <details>

<!-- sdn-diagram:id=scheduler_green_parallelism_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scheduler_green_parallelism_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scheduler_green_parallelism_spec -> std
scheduler_green_parallelism_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scheduler_green_parallelism_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scheduler Green Carrier Parallelism Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Source | `test/01_unit/os/kernel/scheduler/scheduler_green_parallelism_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Requirements

**Requirements:** doc/02_requirements/feature/multicore_green.md

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Design

**Design:** doc/05_design/multicore_green.md

## Scenarios

### Scheduler green carrier parallelism

#### starts from scheduler topology

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sched = Scheduler.new_with_cpu_count(4u32)

expect(sched.green_carrier_parallelism_requested()).to_equal(4)
expect(sched.green_carrier_parallelism_limit()).to_equal(4)
expect(sched.green_carrier_parallelism_reason()).to_equal("default_topology_limit")
```

</details>

#### clamps requested carriers to scheduler topology

1. var sched = Scheduler new with cpu count
   - Expected: state.requested_limit equals `99`
   - Expected: state.active_limit equals `4`
   - Expected: state.reason equals `clamped_topology`
   - Expected: sched.green_carrier_parallelism_requested() equals `99`
   - Expected: sched.green_carrier_parallelism_limit() equals `4`
   - Expected: sched.green_carrier_parallelism_reason() equals `clamped_topology`


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new_with_cpu_count(4u32)
val state = sched.set_green_carrier_parallelism(99)

expect(state.requested_limit).to_equal(99)
expect(state.active_limit).to_equal(4)
expect(state.reason).to_equal("clamped_topology")
expect(sched.green_carrier_parallelism_requested()).to_equal(99)
expect(sched.green_carrier_parallelism_limit()).to_equal(4)
expect(sched.green_carrier_parallelism_reason()).to_equal("clamped_topology")
```

</details>

#### clamps zero or negative requested carriers through scheduler API

1. var sched = Scheduler new with cpu count
   - Expected: zero.requested_limit equals `0`
   - Expected: zero.active_limit equals `1`
   - Expected: zero.reason equals `clamped_min`
   - Expected: negative.requested_limit equals `-3`
   - Expected: negative.active_limit equals `1`
   - Expected: negative.reason equals `clamped_min`
   - Expected: sched.green_carrier_parallelism_requested() equals `-3`
   - Expected: sched.green_carrier_parallelism_limit() equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new_with_cpu_count(4u32)
val zero = sched.set_green_carrier_parallelism(0)
val negative = sched.set_green_carrier_parallelism(-3)

expect(zero.requested_limit).to_equal(0)
expect(zero.active_limit).to_equal(1)
expect(zero.reason).to_equal("clamped_min")
expect(negative.requested_limit).to_equal(-3)
expect(negative.active_limit).to_equal(1)
expect(negative.reason).to_equal("clamped_min")
expect(sched.green_carrier_parallelism_requested()).to_equal(-3)
expect(sched.green_carrier_parallelism_limit()).to_equal(1)
```

</details>

#### keeps requested carriers across topology changes

1. var sched = Scheduler new with cpu count

2. sched set green carrier parallelism

3. sched set topology
   - Expected: sched.green_carrier_parallelism_requested() equals `4`
   - Expected: sched.green_carrier_parallelism_limit() equals `4`
   - Expected: sched.green_carrier_parallelism_reason() equals `requested_limit`

4. sched set topology
   - Expected: sched.green_carrier_parallelism_requested() equals `4`
   - Expected: sched.green_carrier_parallelism_limit() equals `1`
   - Expected: sched.green_carrier_parallelism_reason() equals `clamped_topology`


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new_with_cpu_count(2u32)
sched.set_green_carrier_parallelism(4)
sched.set_topology(default_scheduler_topology(4u32))

expect(sched.green_carrier_parallelism_requested()).to_equal(4)
expect(sched.green_carrier_parallelism_limit()).to_equal(4)
expect(sched.green_carrier_parallelism_reason()).to_equal("requested_limit")

sched.set_topology(default_scheduler_topology(1u32))

expect(sched.green_carrier_parallelism_requested()).to_equal(4)
expect(sched.green_carrier_parallelism_limit()).to_equal(1)
expect(sched.green_carrier_parallelism_reason()).to_equal("clamped_topology")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/multicore_green.md](doc/02_requirements/feature/multicore_green.md)
- **Plan:** [doc/03_plan/sys_test/multicore_green.md](doc/03_plan/sys_test/multicore_green.md)
- **Design:** [doc/05_design/multicore_green.md](doc/05_design/multicore_green.md)


</details>
