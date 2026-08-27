# Nvme Driver Probe Contract Specification

> Tests covering NVMe driver probe and queue ownership contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nvme Driver Probe Contract Specification

## Scenarios

### NVMe driver probe and queue ownership contract

#### rejects probe and evidence collection before hardware initialization

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects probe and evidence collection before hardware initialization
   - Expected: driver.run_reversible_sector_probe(0u64).unwrap_err() equals `NVMe: driver not initialized`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects probe and evidence collection before hardware initialization")
var driver = NvmeDriver.new()
expect(driver.run_reversible_sector_probe(0u64).unwrap_err()).to_equal("NVMe: driver not initialized")
expect(driver.transfer_evidence_from_reversible_probe(
    0u64, "simple-driver", "device-grant", "system", true, true
).unwrap_err()).to_equal("NVMe: driver not initialized")
```

</details>

#### rejects sector and flush submission before hardware initialization

- rejects sector and flush submission before hardware initialization
   - Expected: driver.read_sectors(0u64, 1u32, 0x1000u64).unwrap_err() equals `NVMe: driver not initialized`
   - Expected: driver.write_sectors(0u64, 1u32, 0x1000u64).unwrap_err() equals `NVMe: driver not initialized`
   - Expected: driver.flush().unwrap_err() equals `NVMe: driver not initialized`
   - Expected: driver.read_sectors_notify(0u64, 1u32, 0x1000u64).unwrap_err() equals `NVMe: driver not initialized`
   - Expected: driver.write_sectors_notify(0u64, 1u32, 0x1000u64).unwrap_err() equals `NVMe: driver not initialized`
   - Expected: driver.flush_notify().unwrap_err() equals `NVMe: driver not initialized`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects sector and flush submission before hardware initialization")
var driver = NvmeDriver.new()
expect(driver.read_sectors(0u64, 1u32, 0x1000u64).unwrap_err()).to_equal("NVMe: driver not initialized")
expect(driver.write_sectors(0u64, 1u32, 0x1000u64).unwrap_err()).to_equal("NVMe: driver not initialized")
expect(driver.flush().unwrap_err()).to_equal("NVMe: driver not initialized")
expect(driver.read_sectors_notify(0u64, 1u32, 0x1000u64).unwrap_err()).to_equal("NVMe: driver not initialized")
expect(driver.write_sectors_notify(0u64, 1u32, 0x1000u64).unwrap_err()).to_equal("NVMe: driver not initialized")
expect(driver.flush_notify().unwrap_err()).to_equal("NVMe: driver not initialized")
```

</details>

#### tracks user data queue ownership by controller namespace and owner task

- tracks user data queue ownership by controller namespace and owner task
   - Expected: driver.user_data_queue_owner_reason(2u16, 64u16, 0u32, 5u32, 42u64) equals `ready`
   - Expected: driver.user_data_queue_owner_reason(2u16, 64u16, 0u32, 5u32, 42u64) equals `ready`
   - Expected: driver.user_data_queue_owner_reason(2u16, 64u16, 0u32, 6u32, 42u64) equals `NVMe: user data queue namespace conflict`
   - Expected: driver.user_data_queue_owner_reason(2u16, 64u16, 0u32, 5u32, 43u64) equals `NVMe: user data queue owner conflict`
   - Expected: driver.user_data_queue_owner_reason(2u16, 128u16, 0u32, 5u32, 42u64) equals `NVMe: user data queue depth too small`
   - Expected: observer.user_data_queue_owner_reason(2u16, 64u16, 0u32, 5u32, 43u64) equals `NVMe: user data queue owner conflict`
   - Expected: driver.user_data_queue_owner_reason(2u16, 64u16, 0u32, 5u32, 43u64) equals `NVMe: user data queue owner conflict`
   - Expected: driver.user_data_queue_owner_reason(2u16, 64u16, 0u32, 6u32, 43u64) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks user data queue ownership by controller namespace and owner task")
var driver = NvmeDriver.new()

expect(driver.user_data_queue_owner_reason(2u16, 64u16, 0u32, 5u32, 42u64)).to_equal("ready")
driver.remember_user_data_queue_owner(2u16, 64u16, 0u32, 5u32, 42u64)
expect(driver.user_data_queue_owner_reason(2u16, 64u16, 0u32, 5u32, 42u64)).to_equal("ready")
expect(driver.user_data_queue_owner_reason(2u16, 64u16, 0u32, 6u32, 42u64)).to_equal("NVMe: user data queue namespace conflict")
expect(driver.user_data_queue_owner_reason(2u16, 64u16, 0u32, 5u32, 43u64)).to_equal("NVMe: user data queue owner conflict")
expect(driver.user_data_queue_owner_reason(2u16, 128u16, 0u32, 5u32, 42u64)).to_equal("NVMe: user data queue depth too small")
var observer = NvmeDriver.new()
expect(observer.user_data_queue_owner_reason(2u16, 64u16, 0u32, 5u32, 43u64)).to_equal("NVMe: user data queue owner conflict")
expect(driver.release_user_data_queue_owner(2u16, 0u32, 5u32, 43u64)).to_be(false)
expect(driver.user_data_queue_owner_reason(2u16, 64u16, 0u32, 5u32, 43u64)).to_equal("NVMe: user data queue owner conflict")
expect(driver.release_user_data_queue_owner(2u16, 0u32, 5u32, 42u64)).to_be(true)
expect(driver.user_data_queue_owner_reason(2u16, 64u16, 0u32, 6u32, 43u64)).to_equal("ready")
```

</details>

#### rejects raw system and user queue access to the same namespace

- rejects raw system and user queue access to the same namespace
   - Expected: driver.raw_namespace_queue_access_reason(5u32, 1u16) equals `ready`
   - Expected: driver.raw_namespace_queue_access_reason(5u32, 2u16) equals `NVMe: namespace mode conflict system/user`
   - Expected: driver.user_data_queue_owner_reason(2u16, 64u16, 0u32, 5u32, 42u64) equals `NVMe: namespace mode conflict system/user`
   - Expected: user_driver.user_data_queue_owner_reason(2u16, 64u16, 0u32, 6u32, 42u64) equals `ready`
   - Expected: user_driver.raw_namespace_queue_access_reason(6u32, 1u16) equals `NVMe: namespace mode conflict system/user`
   - Expected: user_driver.raw_namespace_queue_access_reason(6u32, 2u16) equals `ready`
   - Expected: user_driver.raw_namespace_queue_access_reason(7u32, 2u16) equals `NVMe: user data queue namespace conflict`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects raw system and user queue access to the same namespace")
var driver = NvmeDriver.new()

expect(driver.raw_namespace_queue_access_reason(5u32, 1u16)).to_equal("ready")
driver.remember_system_namespace_raw_access(5u32)
expect(driver.raw_namespace_queue_access_reason(5u32, 2u16)).to_equal("NVMe: namespace mode conflict system/user")
expect(driver.user_data_queue_owner_reason(2u16, 64u16, 0u32, 5u32, 42u64)).to_equal("NVMe: namespace mode conflict system/user")

var user_driver = NvmeDriver.new()
expect(user_driver.user_data_queue_owner_reason(2u16, 64u16, 0u32, 6u32, 42u64)).to_equal("ready")
user_driver.remember_user_data_queue_owner(2u16, 64u16, 0u32, 6u32, 42u64)
expect(user_driver.raw_namespace_queue_access_reason(6u32, 1u16)).to_equal("NVMe: namespace mode conflict system/user")
expect(user_driver.raw_namespace_queue_access_reason(6u32, 2u16)).to_equal("ready")
expect(user_driver.raw_namespace_queue_access_reason(7u32, 2u16)).to_equal("NVMe: user data queue namespace conflict")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/drivers/nvme/nvme_driver_probe_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering NVMe driver probe and queue ownership contract.
- NVMe driver probe and queue ownership contract

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bf65d7a8837eec07fe68be494c8c89905686dee85907d5048487017d2d697059`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bf65d7a8837eec07fe68be494c8c89905686dee85907d5048487017d2d697059`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bf65d7a8837eec07fe68be494c8c89905686dee85907d5048487017d2d697059`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/drivers/nvme/nvme_driver_probe_contract_spec.spl
mirror: doc/06_spec/01_unit/os/drivers/nvme/nvme_driver_probe_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/drivers/nvme/nvme_driver_probe_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/drivers/nvme/nvme_driver_probe_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/drivers/nvme/nvme_driver_probe_contract_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects probe and evidence collection before hardware initialization' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/drivers/nvme/nvme_driver_probe_contract_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects sector and flush submission before hardware initialization' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/drivers/nvme/nvme_driver_probe_contract_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tracks user data queue ownership by controller namespace and owner task' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
