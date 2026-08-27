# Net Iommu Isolation Gate Specification

> Tests covering FR-NET-0009 IOMMU isolation gate.

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

- distinguishes isolated grants from explicit no-isolation grants
   - Expected: device_grant_is_isolated(isolated) is true
   - Expected: device_grant_is_no_isolation(isolated) is false
   - Expected: device_grant_is_isolated(no_iommu) is false
   - Expected: device_grant_is_no_isolation(no_iommu) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("distinguishes isolated grants from explicit no-isolation grants")
val isolated = grant_with_iommu(12u32, 44u64)
val no_iommu = grant_with_iommu(0u32, 0u64)
expect(device_grant_is_isolated(isolated)).to_equal(true)
expect(device_grant_is_no_isolation(isolated)).to_equal(false)
expect(device_grant_is_isolated(no_iommu)).to_equal(false)
expect(device_grant_is_no_isolation(no_iommu)).to_equal(true)
```

</details>

#### validates DMA descriptor owner task and BDF

- validates DMA descriptor owner task and BDF
   - Expected: dma_descriptor_matches_owner(desc, 9u64, 0, 5, 0) is true
   - Expected: dma_descriptor_matches_owner(desc, 9u64, 0, 6, 0) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates DMA descriptor owner task and BDF")
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

- fails SR-IOV VF assignment without isolation
   - Expected: assignment.assigned is false
   - Expected: caps.supports_sriov is false
   - Expected: net_backend_sriov_isolation_state(true, caps) equals `sriov-available`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fails SR-IOV VF assignment without isolation")
val assignment = sriov_assign_vf(pf(0u32), 0u16, true)
val caps = sriov_net_backend_capabilities("sriov-vf", assignment)
expect(assignment.assigned).to_equal(false)
expect(caps.supports_sriov).to_equal(false)
expect(net_backend_sriov_isolation_state(true, caps)).to_equal("sriov-available")
```

</details>

#### reports sriov-isolated only after isolated VF assignment

- reports sriov-isolated only after isolated VF assignment
   - Expected: assignment.assigned is true
   - Expected: caps.supports_sriov is true
   - Expected: net_backend_sriov_isolation_state(true, caps) equals `sriov-isolated`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports sriov-isolated only after isolated VF assignment")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering FR-NET-0009 IOMMU isolation gate.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5dddd0d4e7e81e404084982ba4b6185993a457378f989de253ae163e08938e3e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5dddd0d4e7e81e404084982ba4b6185993a457378f989de253ae163e08938e3e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5dddd0d4e7e81e404084982ba4b6185993a457378f989de253ae163e08938e3e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/os/net_iommu_isolation_gate_spec.spl
mirror: doc/06_spec/03_system/os/net_iommu_isolation_gate_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/net_iommu_isolation_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/net_iommu_isolation_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/net_iommu_isolation_gate_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'distinguishes isolated grants from explicit no-isolation grants' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/net_iommu_isolation_gate_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates DMA descriptor owner task and BDF' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/net_iommu_isolation_gate_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails SR-IOV VF assignment without isolation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
