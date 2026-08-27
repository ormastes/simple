# Net Sriov Assignment Specification

> Tests covering FR-NET-0005 SR-IOV discovery and assignment.

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

- identifies SR-IOV physical functions
   - Expected: found.len() equals `1`
   - Expected: found[0].total_vfs equals `8u16`
   - Expected: found[0].iommu_domain_id equals `11u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("identifies SR-IOV physical functions")
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

- fails closed without explicit opt-in
   - Expected: assignment.assigned is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fails closed without explicit opt-in")
val pf = sriov_scan_physical_functions([sriov_record(8u16, 11u32)])[0]
val assignment = sriov_assign_vf(pf, 0u16, false)
expect(assignment.assigned).to_equal(false)
expect(assignment.error).to_contain("opt-in")
```

</details>

#### fails closed without IOMMU isolation

- fails closed without IOMMU isolation
   - Expected: assignment.assigned is false
   - Expected: assignment.isolated is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fails closed without IOMMU isolation")
val pf = sriov_scan_physical_functions([sriov_record(8u16, 0u32)])[0]
val assignment = sriov_assign_vf(pf, 0u16, true)
expect(assignment.assigned).to_equal(false)
expect(assignment.isolated).to_equal(false)
expect(assignment.error).to_contain("iommu")
```

</details>

#### reports supports_sriov only after VF assignment and isolation

- reports supports_sriov only after VF assignment and isolation
   - Expected: assignment.assigned is true
   - Expected: assignment.isolated is true
   - Expected: caps.supports_sriov is true
   - Expected: net_backend_summary(caps) equals `sriov-vf:sriov-packet`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports supports_sriov only after VF assignment and isolation")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering FR-NET-0005 SR-IOV discovery and assignment.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ec89a19a7ca097fb1d325c6697b39d2b569e98d9ce6dacced17b27819dddb2cb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ec89a19a7ca097fb1d325c6697b39d2b569e98d9ce6dacced17b27819dddb2cb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ec89a19a7ca097fb1d325c6697b39d2b569e98d9ce6dacced17b27819dddb2cb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/os/net_sriov_assignment_spec.spl
mirror: doc/06_spec/03_system/os/net_sriov_assignment_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/net_sriov_assignment_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/net_sriov_assignment_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/net_sriov_assignment_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/os/net_sriov_assignment_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'identifies SR-IOV physical functions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/net_sriov_assignment_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed without explicit opt-in' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/net_sriov_assignment_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed without IOMMU isolation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
