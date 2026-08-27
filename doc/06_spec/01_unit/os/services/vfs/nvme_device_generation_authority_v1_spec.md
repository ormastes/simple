# Nvme Device Generation Authority V1 Specification

> Tests covering NVMe device generation authority.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nvme Device Generation Authority V1 Specification

## Scenarios

### NVMe device generation authority

#### starts unavailable until a boot owner publishes identity

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- starts unavailable until a boot owner publishes identity
   - Expected: result.unwrap_err() equals `NvmeDeviceGenerationErrorV1.AuthorityUnavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts unavailable until a boot owner publishes identity")
val authority = NvmeDeviceGenerationAuthorityV1.new()
expect(authority.admitted()).to_be(false)
val result = authority.issue_for_driver(NvmeDriver.new(), _authority_test_lease(), 1u64)
expect(result.is_err()).to_be(true)
expect(result.unwrap_err()).to_equal(NvmeDeviceGenerationErrorV1.AuthorityUnavailable)
```

</details>

#### rejects zero or caller-incomplete bindings before state access

- rejects zero or caller-incomplete bindings before state access
   - Expected: result.unwrap_err() equals `NvmeDeviceGenerationErrorV1.InvalidBinding`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects zero or caller-incomplete bindings before state access")
val authority = NvmeDeviceGenerationAuthorityV1.new()
val result = authority.validate(
    NvmeDeviceGenerationTokenV1.invalid_probe(),
    0u64, 1u32, 1u32, 1u64, 1u64
)
expect(result.is_err()).to_be(true)
expect(result.unwrap_err()).to_equal(NvmeDeviceGenerationErrorV1.InvalidBinding)
```

</details>

#### rejects an invalid opaque probe token

- rejects an invalid opaque probe token
   - Expected: result.unwrap_err() equals `NvmeDeviceGenerationErrorV1.InvalidToken`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an invalid opaque probe token")
val authority = NvmeDeviceGenerationAuthorityV1.new()
val result = authority.validate(
    NvmeDeviceGenerationTokenV1.invalid_probe(),
    1u64, 1u32, 1u32, 1u64, 1u64
)
expect(result.is_err()).to_be(true)
expect(result.unwrap_err()).to_equal(NvmeDeviceGenerationErrorV1.InvalidToken)
```

</details>

#### does not consume or replay an invalid token

- does not consume or replay an invalid token
   - Expected: result.unwrap_err() equals `NvmeDeviceGenerationErrorV1.InvalidToken`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not consume or replay an invalid token")
val authority = NvmeDeviceGenerationAuthorityV1.new()
val result = authority.consume(
    NvmeDeviceGenerationTokenV1.invalid_probe(),
    1u64, 1u32, 1u32, 1u64, 1u64
)
expect(result.is_err()).to_be(true)
expect(result.unwrap_err()).to_equal(NvmeDeviceGenerationErrorV1.InvalidToken)
```

</details>

#### rejects incomplete trusted PCI identity

- rejects incomplete trusted PCI identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects incomplete trusted PCI identity")
val result = nvme_trusted_pci_identity(DeviceGrant(
    pci_vendor: 0u16, pci_device: 0u16,
    pci_bus: 0u8, pci_dev: 0u8, pci_func: 0u8,
    pci_class: 0u8, pci_subclass: 0u8,
    bar0_phys: 0u64, bar0_size: 0u64, bar0_cap: 0u64,
    irq_vector: 0u32, irq_notification_id: 0u64,
    irq_notification_bit: 0u64, irq_cap: 0u64,
    dma_device_addr: 0u64, dma_host_addr: 0u64, dma_size: 0u64,
    dma_cap: 0u64, iommu_domain_id: 0u32, iommu_cap: 0u64
))
expect(result.is_err()).to_be(true)
```

</details>

#### keeps distinct PCI BDFs distinct from namespace binding

- keeps distinct PCI BDFs distinct from namespace binding


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps distinct PCI BDFs distinct from namespace binding")
val first = nvme_trusted_pci_identity(_identity_grant(2u8, 0u8)).unwrap()
val second = nvme_trusted_pci_identity(_identity_grant(2u8, 1u8)).unwrap()
expect(first == second).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/services/vfs/nvme_device_generation_authority_v1_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering NVMe device generation authority.
- NVMe device generation authority

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cc0e496f4e47a75962f79eac0ce990aa86a3ac41f959bf7d02895e0ef96b46bf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cc0e496f4e47a75962f79eac0ce990aa86a3ac41f959bf7d02895e0ef96b46bf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cc0e496f4e47a75962f79eac0ce990aa86a3ac41f959bf7d02895e0ef96b46bf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/services/vfs/nvme_device_generation_authority_v1_spec.spl
mirror: doc/06_spec/01_unit/os/services/vfs/nvme_device_generation_authority_v1_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/services/vfs/nvme_device_generation_authority_v1_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/services/vfs/nvme_device_generation_authority_v1_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/services/vfs/nvme_device_generation_authority_v1_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts unavailable until a boot owner publishes identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/vfs/nvme_device_generation_authority_v1_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects zero or caller-incomplete bindings before state access' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/vfs/nvme_device_generation_authority_v1_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an invalid opaque probe token' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
