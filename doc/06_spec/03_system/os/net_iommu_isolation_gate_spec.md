# Net Iommu Isolation Gate Specification

> <details>

<!-- sdn-diagram:id=net_iommu_isolation_gate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=net_iommu_isolation_gate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

net_iommu_isolation_gate_spec -> std
net_iommu_isolation_gate_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=net_iommu_isolation_gate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Net Iommu Isolation Gate Specification

## Scenarios

### FR-NET-0009 IOMMU isolation gate

#### device grants

#### distinguishes isolated grants from explicit no-isolation grants

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val isolated = grant_with_iommu(12u32, 44u64)
val no_iommu = grant_with_iommu(0u32, 0u64)
expect(device_grant_is_isolated(isolated)).to_equal(true)
expect(device_grant_is_no_isolation(isolated)).to_equal(false)
expect(device_grant_is_isolated(no_iommu)).to_equal(false)
expect(device_grant_is_no_isolation(no_iommu)).to_equal(true)
```

</details>

#### validates DMA descriptor owner task and BDF

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val desc = DmaDescriptor(
    cpu_virt_addr: 0x1000u64,
    host_phys_addr: 0x2000u64,
    device_addr: 0x2000u64,
    byte_len: 4096u64,
    cache_policy: 0,
    owner_task: 9u64,
    owner_bdf_bus: 0,
    owner_bdf_device: 5,
    owner_bdf_function: 0,
    allocation_id: 77u64
)
expect(dma_descriptor_matches_owner(desc, 9u64, 0, 5, 0)).to_equal(true)
expect(dma_descriptor_matches_owner(desc, 9u64, 0, 6, 0)).to_equal(false)
```

</details>

#### SR-IOV and net capability reporting

#### fails SR-IOV VF assignment without isolation

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val assignment = sriov_assign_vf(pf(0u32), 0u16, true)
val caps = sriov_net_backend_capabilities("sriov-vf", assignment)
expect(assignment.assigned).to_equal(false)
expect(caps.supports_sriov).to_equal(false)
expect(net_backend_sriov_isolation_state(true, caps)).to_equal("sriov-available")
```

</details>

#### reports sriov-isolated only after isolated VF assignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val assignment = sriov_assign_vf(pf(12u32), 0u16, true)
val caps = sriov_net_backend_capabilities("sriov-vf", assignment)
expect(assignment.assigned).to_equal(true)
expect(caps.supports_sriov).to_equal(true)
expect(net_backend_sriov_isolation_state(true, caps)).to_equal("sriov-isolated")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/net_iommu_isolation_gate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- FR-NET-0009 IOMMU isolation gate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
