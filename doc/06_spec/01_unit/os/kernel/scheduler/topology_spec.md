# Scheduler Topology Specification

> Tests for pure scheduler topology construction helpers.

<!-- sdn-diagram:id=topology_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=topology_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

topology_spec -> std
topology_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=topology_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scheduler Topology Specification

Tests for pure scheduler topology construction helpers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/scheduler/topology_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for pure scheduler topology construction helpers.

## Scenarios

### Scheduler topology helpers

### flat topology

#### keeps default scheduler topology compatible

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val legacy = default_scheduler_topology(4u32)
val flat = scheduler_flat_topology(4u32)

expect(legacy.cpu_count).to_equal(flat.cpu_count)
expect(legacy.domains.len()).to_equal(flat.domains.len())
expect(legacy.domains[0].kind).to_equal(SchedulerDomainKind.Flat)
expect(legacy.domains[0].first_cpu).to_equal(0u32)
expect(legacy.domains[0].cpu_count).to_equal(4u32)
expect(legacy.domains[0].rebalance_threshold).to_equal(2)
expect(legacy.domains[0].wake_affine_threshold).to_equal(1)
```

</details>

#### normalizes zero CPUs to one flat CPU

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val topology = scheduler_flat_topology(0u32)

expect(topology.cpu_count).to_equal(1u32)
expect(topology.domains.len()).to_equal(1)
expect(topology.domains[0].kind).to_equal(SchedulerDomainKind.Flat)
expect(topology.domains[0].cpu_count).to_equal(1u32)
```

</details>

#### falls back to flat topology for empty CPU info

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val topology = scheduler_topology_from_cpu_info([])

expect(topology.cpu_count).to_equal(1u32)
expect(topology.domains.len()).to_equal(1)
expect(topology.domains[0].kind).to_equal(SchedulerDomainKind.Flat)
```

</details>

### hardware topology

#### builds SMT cache and NUMA domains from synthetic CPU info

1.  cpu
2.  cpu
3.  cpu
4.  cpu
5.  cpu
6.  cpu
7.  cpu
8.  cpu
   - Expected: topology.cpu_count equals `8u32`
   - Expected: topology.domains.len() equals `9`
   - Expected: topology.domains[0].kind equals `SchedulerDomainKind.Flat`
   - Expected: topology.domains[0].first_cpu equals `0u32`
   - Expected: topology.domains[0].cpu_count equals `8u32`
   - Expected: topology.domains[1].kind equals `SchedulerDomainKind.Numa`
   - Expected: topology.domains[1].parent_id equals `0u32`
   - Expected: topology.domains[1].first_cpu equals `0u32`
   - Expected: topology.domains[1].cpu_count equals `4u32`
   - Expected: topology.domains[1].rebalance_threshold equals `8`
   - Expected: topology.domains[1].wake_affine_threshold equals `4`
   - Expected: topology.domains[2].kind equals `SchedulerDomainKind.Numa`
   - Expected: topology.domains[2].parent_id equals `0u32`
   - Expected: topology.domains[2].first_cpu equals `4u32`
   - Expected: topology.domains[2].cpu_count equals `4u32`
   - Expected: topology.domains[3].kind equals `SchedulerDomainKind.Cache`
   - Expected: topology.domains[3].parent_id equals `1u32`
   - Expected: topology.domains[3].first_cpu equals `0u32`
   - Expected: topology.domains[3].cpu_count equals `4u32`
   - Expected: topology.domains[3].rebalance_threshold equals `3`
   - Expected: topology.domains[3].wake_affine_threshold equals `2`
   - Expected: topology.domains[4].kind equals `SchedulerDomainKind.Cache`
   - Expected: topology.domains[4].parent_id equals `2u32`
   - Expected: topology.domains[4].first_cpu equals `4u32`
   - Expected: topology.domains[4].cpu_count equals `4u32`
   - Expected: topology.domains[5].kind equals `SchedulerDomainKind.Smt`
   - Expected: topology.domains[5].parent_id equals `3u32`
   - Expected: topology.domains[5].first_cpu equals `0u32`
   - Expected: topology.domains[5].cpu_count equals `2u32`
   - Expected: topology.domains[5].rebalance_threshold equals `1`
   - Expected: topology.domains[6].kind equals `SchedulerDomainKind.Smt`
   - Expected: topology.domains[6].parent_id equals `3u32`
   - Expected: topology.domains[6].first_cpu equals `2u32`
   - Expected: topology.domains[6].cpu_count equals `2u32`
   - Expected: topology.domains[7].kind equals `SchedulerDomainKind.Smt`
   - Expected: topology.domains[7].parent_id equals `4u32`
   - Expected: topology.domains[7].first_cpu equals `4u32`
   - Expected: topology.domains[7].cpu_count equals `2u32`
   - Expected: topology.domains[8].kind equals `SchedulerDomainKind.Smt`
   - Expected: topology.domains[8].parent_id equals `4u32`
   - Expected: topology.domains[8].first_cpu equals `6u32`
   - Expected: topology.domains[8].cpu_count equals `2u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 62 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val topology = scheduler_topology_from_cpu_info([
    _cpu(0u32, 0u32, 0u32, 0u32),
    _cpu(1u32, 0u32, 0u32, 0u32),
    _cpu(2u32, 1u32, 0u32, 0u32),
    _cpu(3u32, 1u32, 0u32, 0u32),
    _cpu(4u32, 2u32, 1u32, 1u32),
    _cpu(5u32, 2u32, 1u32, 1u32),
    _cpu(6u32, 3u32, 1u32, 1u32),
    _cpu(7u32, 3u32, 1u32, 1u32)
])

expect(topology.cpu_count).to_equal(8u32)
expect(topology.domains.len()).to_equal(9)

expect(topology.domains[0].kind).to_equal(SchedulerDomainKind.Flat)
expect(topology.domains[0].first_cpu).to_equal(0u32)
expect(topology.domains[0].cpu_count).to_equal(8u32)

expect(topology.domains[1].kind).to_equal(SchedulerDomainKind.Numa)
expect(topology.domains[1].parent_id).to_equal(0u32)
expect(topology.domains[1].first_cpu).to_equal(0u32)
expect(topology.domains[1].cpu_count).to_equal(4u32)
expect(topology.domains[1].rebalance_threshold).to_equal(8)
expect(topology.domains[1].wake_affine_threshold).to_equal(4)

expect(topology.domains[2].kind).to_equal(SchedulerDomainKind.Numa)
expect(topology.domains[2].parent_id).to_equal(0u32)
expect(topology.domains[2].first_cpu).to_equal(4u32)
expect(topology.domains[2].cpu_count).to_equal(4u32)

expect(topology.domains[3].kind).to_equal(SchedulerDomainKind.Cache)
expect(topology.domains[3].parent_id).to_equal(1u32)
expect(topology.domains[3].first_cpu).to_equal(0u32)
expect(topology.domains[3].cpu_count).to_equal(4u32)
expect(topology.domains[3].rebalance_threshold).to_equal(3)
expect(topology.domains[3].wake_affine_threshold).to_equal(2)

expect(topology.domains[4].kind).to_equal(SchedulerDomainKind.Cache)
expect(topology.domains[4].parent_id).to_equal(2u32)
expect(topology.domains[4].first_cpu).to_equal(4u32)
expect(topology.domains[4].cpu_count).to_equal(4u32)

expect(topology.domains[5].kind).to_equal(SchedulerDomainKind.Smt)
expect(topology.domains[5].parent_id).to_equal(3u32)
expect(topology.domains[5].first_cpu).to_equal(0u32)
expect(topology.domains[5].cpu_count).to_equal(2u32)
expect(topology.domains[5].rebalance_threshold).to_equal(1)

expect(topology.domains[6].kind).to_equal(SchedulerDomainKind.Smt)
expect(topology.domains[6].parent_id).to_equal(3u32)
expect(topology.domains[6].first_cpu).to_equal(2u32)
expect(topology.domains[6].cpu_count).to_equal(2u32)

expect(topology.domains[7].kind).to_equal(SchedulerDomainKind.Smt)
expect(topology.domains[7].parent_id).to_equal(4u32)
expect(topology.domains[7].first_cpu).to_equal(4u32)
expect(topology.domains[7].cpu_count).to_equal(2u32)

expect(topology.domains[8].kind).to_equal(SchedulerDomainKind.Smt)
expect(topology.domains[8].parent_id).to_equal(4u32)
expect(topology.domains[8].first_cpu).to_equal(6u32)
expect(topology.domains[8].cpu_count).to_equal(2u32)
```

</details>

#### uses flat fallback when CPU ids are not contiguous

1.  cpu
2.  cpu
   - Expected: topology.cpu_count equals `2u32`
   - Expected: topology.domains.len() equals `1`
   - Expected: topology.domains[0].kind equals `SchedulerDomainKind.Flat`
   - Expected: topology.domains[0].cpu_count equals `2u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val topology = scheduler_topology_from_cpu_info([
    _cpu(0u32, 0u32, 0u32, 0u32),
    _cpu(2u32, 1u32, 1u32, 1u32)
])

expect(topology.cpu_count).to_equal(2u32)
expect(topology.domains.len()).to_equal(1)
expect(topology.domains[0].kind).to_equal(SchedulerDomainKind.Flat)
expect(topology.domains[0].cpu_count).to_equal(2u32)
```

</details>

#### uses boot-registered platform topology when constructing the scheduler

1. scheduler clear platform cpu topology for test
2.  cpu
3.  cpu
4.  cpu
5.  cpu
   - Expected: scheduler.topology_cpu_count() equals `4u32`
   - Expected: scheduler.topology_domain_count() equals `5`
   - Expected: scheduler.topology_domain(0).unwrap().kind equals `SchedulerDomainKind.Flat`
   - Expected: scheduler.topology_domain(1).unwrap().kind equals `SchedulerDomainKind.Cache`
   - Expected: scheduler.topology_domain(3).unwrap().kind equals `SchedulerDomainKind.Smt`
6. scheduler clear platform cpu topology for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
scheduler_clear_platform_cpu_topology_for_test()
scheduler_register_platform_cpu_topology([
    _cpu(0u32, 0u32, 0u32, 0u32),
    _cpu(1u32, 0u32, 0u32, 0u32),
    _cpu(2u32, 1u32, 1u32, 0u32),
    _cpu(3u32, 1u32, 1u32, 0u32)
])

val scheduler = Scheduler.new()

expect(scheduler.topology_cpu_count()).to_equal(4u32)
expect(scheduler.topology_domain_count()).to_equal(5)
expect(scheduler.topology_domain(0).unwrap().kind).to_equal(SchedulerDomainKind.Flat)
expect(scheduler.topology_domain(1).unwrap().kind).to_equal(SchedulerDomainKind.Cache)
expect(scheduler.topology_domain(3).unwrap().kind).to_equal(SchedulerDomainKind.Smt)

scheduler_clear_platform_cpu_topology_for_test()
```

</details>

#### creates an operational single CPU bootstrap scheduler

1. scheduler clear platform cpu topology for test
2. var scheduler = Scheduler new bootstrap
   - Expected: scheduler.topology_cpu_count() equals `1u32`
   - Expected: scheduler.cpu_runnable_count(0u32) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
scheduler_clear_platform_cpu_topology_for_test()
var scheduler = Scheduler.new_bootstrap()

val task = scheduler.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())

expect(scheduler.topology_cpu_count()).to_equal(1u32)
expect(task.id).to_be_greater_than(0)
expect(scheduler.cpu_runnable_count(0u32)).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
