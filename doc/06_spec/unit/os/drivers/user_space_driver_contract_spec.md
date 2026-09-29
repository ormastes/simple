# User Space Driver Contract Specification

> Tests covering SimpleOS user-space direct driver contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# User Space Driver Contract Specification

## Scenarios

### SimpleOS user-space direct driver contract

#### requires NVMe direct access to run as a user-space driver with grants

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- requires NVMe direct access to run as a user-space driver with grants
   - Expected: denied equals `direct-access-not-user-space-driver:kernel-driver`
   - Expected: ready is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires NVMe direct access to run as a user-space driver with grants")
val denied = user_space_driver_direct_access_reason(
    "nvme",
    "kernel-driver",
    "mmio",
    "raw-device-grant:tok=11",
    "non-secure-resource-namespace",
    true,
    true,
    "simple-driver"
)
expect(denied).to_equal("direct-access-not-user-space-driver:kernel-driver")

val ready = user_space_driver_direct_access_ready(
    "nvme",
    "user-space-driver",
    "mmio",
    "raw-device-grant:tok=11",
    "non-secure-resource-namespace",
    true,
    true,
    "simple-driver"
)
expect(ready).to_equal(true)
```

</details>

#### keeps common drivers as shared logic without ambient MMIO or DMA

- keeps common drivers as shared logic without ambient MMIO or DMA
   - Expected: parser equals `ready`
   - Expected: bridge_parser equals `common-logic-provider-not-simple-driver:c-boot-bridge`
   - Expected: unshared_parser equals `missing-common-driver-logic`
   - Expected: ambient_grant equals `common-logic-has-ambient-grant:resource-grant-set:tok=55`
   - Expected: ambient_namespace equals `common-logic-has-resource-namespace:non-secure-resource-namespace`
   - Expected: mmio equals `direct-access-not-user-space-driver:common-driver`


<details>
<summary>Executable SSpec</summary>

Runnable source: 73 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps common drivers as shared logic without ambient MMIO or DMA")
val parser = user_space_driver_direct_access_reason(
    "virtio-net",
    "common-driver",
    "descriptor-builder",
    "none",
    "none",
    true,
    false,
    "simple-driver"
)
expect(parser).to_equal("ready")

val bridge_parser = user_space_driver_direct_access_reason(
    "virtio-net",
    "common-driver",
    "descriptor-builder",
    "none",
    "none",
    true,
    false,
    "c-boot-bridge"
)
expect(bridge_parser).to_equal("common-logic-provider-not-simple-driver:c-boot-bridge")

val unshared_parser = user_space_driver_direct_access_reason(
    "virtio-net",
    "common-driver",
    "queue-layout",
    "none",
    "none",
    false,
    false,
    "simple-driver"
)
expect(unshared_parser).to_equal("missing-common-driver-logic")

val ambient_grant = user_space_driver_direct_access_reason(
    "virtio-net",
    "common-driver",
    "state-machine",
    "resource-grant-set:tok=55",
    "none",
    true,
    true,
    "simple-driver"
)
expect(ambient_grant).to_equal("common-logic-has-ambient-grant:resource-grant-set:tok=55")

val ambient_namespace = user_space_driver_direct_access_reason(
    "virtio-net",
    "common-driver",
    "parser",
    "none",
    "non-secure-resource-namespace",
    true,
    false,
    "simple-driver"
)
expect(ambient_namespace).to_equal("common-logic-has-resource-namespace:non-secure-resource-namespace")

val mmio = user_space_driver_direct_access_reason(
    "virtio-net",
    "common-driver",
    "mmio",
    "resource-grant-set:tok=22",
    "non-secure-resource-namespace",
    true,
    true,
    "simple-driver"
)
expect(mmio).to_equal("direct-access-not-user-space-driver:common-driver")
```

</details>

#### rejects C bridge and unbrokered RDMA as pure direct access

- rejects C bridge and unbrokered RDMA as pure direct access
   - Expected: bridge equals `provider-not-simple-driver:c-boot-bridge`
   - Expected: rdma equals `missing-iommu-or-grant-broker`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects C bridge and unbrokered RDMA as pure direct access")
val bridge = user_space_driver_direct_access_reason(
    "nvme",
    "user-space-driver",
    "dma",
    "raw-device-grant:tok=11",
    "non-secure-resource-namespace",
    true,
    true,
    "c-boot-bridge"
)
expect(bridge).to_equal("provider-not-simple-driver:c-boot-bridge")

val rdma = user_space_driver_direct_access_reason(
    "rdma",
    "user-space-driver",
    "dma",
    "resource-grant-set:tok=33",
    "non-secure-resource-namespace",
    true,
    false,
    "simple-driver"
)
expect(rdma).to_equal("missing-iommu-or-grant-broker")
```

</details>

#### accepts every direct access lane only with complete user-space evidence

- accepts every direct access lane only with complete user-space evidence
   - Expected: ready is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts every direct access lane only with complete user-space evidence")
val ready = user_space_driver_all_direct_access_ready(
    "e1000",
    "user-space-driver",
    "resource-grant-set:tok=44",
    "non-secure-resource-namespace",
    true,
    true,
    "simple-driver"
)
expect(ready).to_equal(true)
```

</details>

#### rejects kernel placement for the full direct access set

- rejects kernel placement for the full direct access set


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects kernel placement for the full direct access set")
val placement_reason = user_space_driver_all_direct_access_reason(
    "virtio-net",
    "kernel-driver",
    "resource-grant-set:tok=22",
    "non-secure-resource-namespace",
    true,
    true,
    "simple-driver"
)
expect(placement_reason).to_contain("missing-required-access:mmio:")
expect(placement_reason).to_contain("direct-access-not-user-space-driver:kernel-driver")
```

</details>

#### rejects unbrokered RDMA for the full direct access set

- rejects unbrokered RDMA for the full direct access set


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unbrokered RDMA for the full direct access set")
val no_broker = user_space_driver_all_direct_access_reason(
    "rdma",
    "user-space-driver",
    "resource-grant-set:tok=33",
    "non-secure-resource-namespace",
    true,
    false,
    "simple-driver"
)
expect(no_broker).to_contain("missing-required-access:mmio:")
expect(no_broker).to_contain("missing-iommu-or-grant-broker")
```

</details>

#### rejects grant labels that do not prove an issued broker token

- rejects grant labels that do not prove an issued broker token
   - Expected: raw_label equals `missing-issued-device-grant-token:raw-device-grant`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects grant labels that do not prove an issued broker token")
val raw_label = user_space_driver_direct_access_reason(
    "nvme",
    "user-space-driver",
    "mmio",
    "raw-device-grant",
    "non-secure-resource-namespace",
    true,
    true,
    "simple-driver"
)
expect(raw_label).to_equal("missing-issued-device-grant-token:raw-device-grant")

val set_label = user_space_driver_all_direct_access_reason(
    "virtio-net",
    "user-space-driver",
    "resource-grant-set",
    "non-secure-resource-namespace",
    true,
    true,
    "simple-driver"
)
expect(set_label).to_contain("missing-required-access:mmio:")
expect(set_label).to_contain("missing-issued-device-grant-token:resource-grant-set")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/drivers/user_space_driver_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS user-space direct driver contract.
- SimpleOS user-space direct driver contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `d0aaec5d59e478f3e7c3c1e2c645227219c366b8d1912b125ee5a07957f9985b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d0aaec5d59e478f3e7c3c1e2c645227219c366b8d1912b125ee5a07957f9985b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d0aaec5d59e478f3e7c3c1e2c645227219c366b8d1912b125ee5a07957f9985b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/drivers/user_space_driver_contract_spec.spl
mirror: doc/06_spec/unit/os/drivers/user_space_driver_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/drivers/user_space_driver_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/drivers/user_space_driver_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/drivers/user_space_driver_contract_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires NVMe direct access to run as a user-space driver with grants' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/drivers/user_space_driver_contract_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps common drivers as shared logic without ambient MMIO or DMA' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/drivers/user_space_driver_contract_spec.spl:119:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects C bridge and unbrokered RDMA as pure direct access' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
