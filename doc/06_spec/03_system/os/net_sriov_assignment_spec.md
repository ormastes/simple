# Net Sriov Assignment Specification

> 1. sriov record

<!-- sdn-diagram:id=net_sriov_assignment_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=net_sriov_assignment_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

net_sriov_assignment_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=net_sriov_assignment_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Net Sriov Assignment Specification

## Scenarios

### FR-NET-0005 SR-IOV discovery and assignment

#### PCI capability scan

#### identifies SR-IOV physical functions

1. sriov record
   - Expected: found.len() equals `1`
   - Expected: found[0].total_vfs equals `8u16`
   - Expected: found[0].iommu_domain_id equals `11u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val records = [
    sriov_record(8u16, 11u32),
    SriovCapabilityRecord(
        bdf_bus: 0,
        bdf_device: 6,
        bdf_function: 0,
        capability_id: 0x05u16,
        total_vfs: 0u16,
        first_vf_offset: 0u16,
        vf_stride: 0u16,
        iommu_domain_id: 0u32
    )
]
val found = sriov_scan_physical_functions(records)
expect(found.len()).to_equal(1)
expect(found[0].total_vfs).to_equal(8u16)
expect(found[0].iommu_domain_id).to_equal(11u32)
```

</details>

#### VF assignment

#### fails closed without explicit opt-in

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pf = sriov_scan_physical_functions([sriov_record(8u16, 11u32)])[0]
val assignment = sriov_assign_vf(pf, 0u16, false)
expect(assignment.assigned).to_equal(false)
expect(assignment.error).to_contain("opt-in")
```

</details>

#### fails closed without IOMMU isolation

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pf = sriov_scan_physical_functions([sriov_record(8u16, 0u32)])[0]
val assignment = sriov_assign_vf(pf, 0u16, true)
expect(assignment.assigned).to_equal(false)
expect(assignment.isolated).to_equal(false)
expect(assignment.error).to_contain("iommu")
```

</details>

#### reports supports_sriov only after VF assignment and isolation

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pf = sriov_scan_physical_functions([sriov_record(8u16, 11u32)])[0]
val assignment = sriov_assign_vf(pf, 1u16, true)
val caps = sriov_net_backend_capabilities("sriov-vf", assignment)
expect(assignment.assigned).to_equal(true)
expect(assignment.isolated).to_equal(true)
expect(caps.supports_sriov).to_equal(true)
expect(net_backend_summary(caps)).to_equal("sriov-vf:sriov-packet")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/net_sriov_assignment_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- FR-NET-0005 SR-IOV discovery and assignment

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
