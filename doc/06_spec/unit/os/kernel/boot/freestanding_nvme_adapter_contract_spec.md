# Freestanding Nvme Adapter Contract Specification

> Tests covering freestanding pure NVMe adapter contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Freestanding Nvme Adapter Contract Specification

## Scenarios

### freestanding pure NVMe adapter contract

#### accepts only complete pure-Simple transfer evidence before boot probing

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts only complete pure-Simple transfer evidence before boot probing
   - Expected: contract.provider equals `simple-driver`
   - Expected: contract.pure_simple is true
   - Expected: contract.block_probe_entry equals `boot_fs_mount_from_device`
   - Expected: contract.transfer_ready is true
   - Expected: freestanding_nvme_adapter_ready(ready) is true
   - Expected: freestanding_nvme_adapter_refusal_reason(ready) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts only complete pure-Simple transfer evidence before boot probing")
val ready = _ready_transfer()
val contract = freestanding_nvme_adapter_contract(ready)
expect(contract.provider).to_equal("simple-driver")
expect(contract.pure_simple).to_equal(true)
expect(contract.block_probe_entry).to_equal("boot_fs_mount_from_device")
expect(contract.transfer_ready).to_equal(true)
expect(freestanding_nvme_adapter_ready(ready)).to_equal(true)
expect(freestanding_nvme_adapter_refusal_reason(ready)).to_equal("ready")
```

</details>

#### rejects C bridge and incomplete transfer evidence

- rejects C bridge and incomplete transfer evidence
   - Expected: freestanding_nvme_adapter_ready(bridge) is false
   - Expected: freestanding_nvme_adapter_refusal_reason(bridge) equals `nvme-transfer-provider-not-simple:c-boot-bridge`
   - Expected: freestanding_nvme_adapter_ready(missing_sector) is false
   - Expected: freestanding_nvme_adapter_refusal_reason(missing_sector) equals `missing-nvme-sector-read`


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects C bridge and incomplete transfer evidence")
val bridge = nvme_transfer_evidence(
    "c-boot-bridge",
    true,
    true,
    true,
    true,
    true,
    true,
    true,
    true,
    true,
    "user-space-driver",
    "raw-device-grant:tok=boot-nvme",
    "non-secure-resource-namespace",
    true,
    true
)
expect(freestanding_nvme_adapter_ready(bridge)).to_equal(false)
expect(freestanding_nvme_adapter_refusal_reason(bridge)).to_equal("nvme-transfer-provider-not-simple:c-boot-bridge")

val missing_sector = nvme_transfer_evidence(
    "simple-driver",
    true,
    true,
    true,
    true,
    true,
    false,
    true,
    true,
    true,
    "user-space-driver",
    "raw-device-grant:tok=boot-nvme",
    "non-secure-resource-namespace",
    true,
    true
)
expect(freestanding_nvme_adapter_ready(missing_sector)).to_equal(false)
expect(freestanding_nvme_adapter_refusal_reason(missing_sector)).to_equal("missing-nvme-sector-read")
```

</details>

#### publishes the provider and shared boot probe entry

- publishes the provider and shared boot probe entry
   - Expected: freestanding_nvme_adapter_provider() equals `simple-driver`
   - Expected: freestanding_nvme_adapter_block_probe_entry() equals `boot_fs_mount_from_device`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("publishes the provider and shared boot probe entry")
expect(freestanding_nvme_adapter_provider()).to_equal("simple-driver")
expect(freestanding_nvme_adapter_block_probe_entry()).to_equal("boot_fs_mount_from_device")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/kernel/boot/freestanding_nvme_adapter_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering freestanding pure NVMe adapter contract.
- freestanding pure NVMe adapter contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `d369d73ab61cca319efc35fa830cade3fcac967da3a8af3060517ed431a523c0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d369d73ab61cca319efc35fa830cade3fcac967da3a8af3060517ed431a523c0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d369d73ab61cca319efc35fa830cade3fcac967da3a8af3060517ed431a523c0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/unit/os/kernel/boot/freestanding_nvme_adapter_contract_spec.spl
mirror: doc/06_spec/unit/os/kernel/boot/freestanding_nvme_adapter_contract_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/kernel/boot/freestanding_nvme_adapter_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/boot/freestanding_nvme_adapter_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/boot/freestanding_nvme_adapter_contract_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts only complete pure-Simple transfer evidence before boot probing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/boot/freestanding_nvme_adapter_contract_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'publishes the provider and shared boot probe entry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
