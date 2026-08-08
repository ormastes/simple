# x86_64 Scheduler Topology Probe Specification

> <details>

<!-- sdn-diagram:id=x86_64_topology_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=x86_64_topology_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

x86_64_topology_spec -> std
x86_64_topology_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=x86_64_topology_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# x86_64 Scheduler Topology Probe Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/arch/x86_64_topology_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### x86_64 scheduler topology probe

#### prefers CPUID topology v2 leaf over v1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(x86_select_topology_leaf(0x20u32)).to_equal(0x1Fu32)
expect(x86_select_topology_leaf(0x0Bu32)).to_equal(0x0Bu32)
expect(x86_select_topology_leaf(0x07u32)).to_equal(0u32)
```

</details>

#### builds SMT and cache groups from decoded APIC-id shifts

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = x86_scheduler_topology_from_shape(
    cpu_count: 4u32,
    smt_shift: 1u32,
    core_shift: 2u32,
    base_apic_id: 0u32
)

expect(info.len()).to_equal(4)
expect(info[0].cpu_id).to_equal(0u32)
expect(info[1].cpu_id).to_equal(1u32)
expect(info[0].smt_id).to_equal(0u32)
expect(info[1].smt_id).to_equal(0u32)
expect(info[2].smt_id).to_equal(1u32)
expect(info[3].smt_id).to_equal(1u32)
expect(info[0].cache_id).to_equal(0u32)
expect(info[3].cache_id).to_equal(0u32)
```

</details>

#### normalizes zero CPUs for early boot fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = x86_scheduler_topology_from_shape(
    cpu_count: 0u32,
    smt_shift: 0u32,
    core_shift: 0u32,
    base_apic_id: 0u32
)

expect(info.len()).to_equal(1)
expect(info[0].cpu_id).to_equal(0u32)
```

</details>

#### uses firmware APIC ids while keeping scheduler CPU ids contiguous

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = x86_scheduler_topology_from_apic_ids(
    apic_ids: [4u32, 5u32, 8u32, 9u32],
    smt_shift: 1u32,
    core_shift: 2u32
)

expect(info.len()).to_equal(4)
expect(info[0].cpu_id).to_equal(0u32)
expect(info[3].cpu_id).to_equal(3u32)
expect(info[0].smt_id).to_equal(2u32)
expect(info[1].smt_id).to_equal(2u32)
expect(info[2].smt_id).to_equal(4u32)
expect(info[3].smt_id).to_equal(4u32)
expect(info[0].cache_id).to_equal(1u32)
expect(info[3].cache_id).to_equal(2u32)
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


</details>
