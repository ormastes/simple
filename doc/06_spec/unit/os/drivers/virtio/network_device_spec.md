# Network Device Specification

> Tests covering SimpleOS network transfer evidence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Network Device Specification

## Scenarios

### SimpleOS network transfer evidence

#### rejects C bridge network transfer claims

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects C bridge network transfer claims
   - Expected: network_transfer_ready(bridge) is false
   - Expected: network_transfer_readiness_reason(bridge) equals `network-transfer-provider-not-simple:c-boot-bridge`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects C bridge network transfer claims")
val bridge = network_transfer_evidence(
    "c-boot-bridge",
    "virtio-net",
    true,
    true,
    true,
    true,
    true,
    true,
    true,
    true,
    "user-space-driver",
    "resource-grant-set:tok=22",
    "non-secure-resource-namespace",
    true,
    true
)
expect(network_transfer_ready(bridge)).to_equal(false)
expect(network_transfer_readiness_reason(bridge)).to_equal("network-transfer-provider-not-simple:c-boot-bridge")
```

</details>

#### requires queue setup TX completion RX frame and DMA isolation

- requires queue setup TX completion RX frame and DMA isolation
   - Expected: network_transfer_readiness_reason(missing_rx_queue) equals `missing-network-rx-queue`
   - Expected: network_transfer_readiness_reason(missing_completion) equals `missing-network-tx-completion`
   - Expected: network_transfer_ready(ready) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 57 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires queue setup TX completion RX frame and DMA isolation")
val missing_rx_queue = network_transfer_evidence(
    "simple-driver",
    "virtio-net",
    true,
    true,
    true,
    true,
    false,
    true,
    true,
    true,
    "user-space-driver",
    "resource-grant-set:tok=22",
    "non-secure-resource-namespace",
    true,
    true
)
val missing_completion = network_transfer_evidence(
    "simple-driver",
    "e1000",
    true,
    true,
    true,
    true,
    true,
    false,
    true,
    true,
    "user-space-driver",
    "resource-grant-set:tok=23",
    "non-secure-resource-namespace",
    true,
    true
)
val ready = network_transfer_evidence(
    "simple-driver",
    "virtio-net",
    true,
    true,
    true,
    true,
    true,
    true,
    true,
    true,
    "user-space-driver",
    "resource-grant-set:tok=24",
    "non-secure-resource-namespace",
    true,
    true
)

expect(network_transfer_readiness_reason(missing_rx_queue)).to_equal("missing-network-rx-queue")
expect(network_transfer_readiness_reason(missing_completion)).to_equal("missing-network-tx-completion")
expect(network_transfer_ready(ready)).to_equal(true)
```

</details>

#### rejects unsupported or kernel-only network transfer evidence

- rejects unsupported or kernel-only network transfer evidence
   - Expected: network_transfer_readiness_reason(unsupported) equals `network-transfer-unsupported-kind:rdma`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unsupported or kernel-only network transfer evidence")
val unsupported = network_transfer_evidence(
    "simple-driver",
    "rdma",
    true,
    true,
    true,
    true,
    true,
    true,
    true,
    true,
    "user-space-driver",
    "resource-grant-set:tok=25",
    "non-secure-resource-namespace",
    true,
    true
)
val kernel_side = network_transfer_evidence(
    "simple-driver",
    "e1000",
    true,
    true,
    true,
    true,
    true,
    true,
    true,
    true,
    "kernel-driver",
    "resource-grant-set:tok=26",
    "non-secure-resource-namespace",
    true,
    true
)

expect(network_transfer_readiness_reason(unsupported)).to_equal("network-transfer-unsupported-kind:rdma")
expect(network_transfer_readiness_reason(kernel_side)).to_contain("network-transfer-direct-access-not-ready:")
expect(network_transfer_readiness_reason(kernel_side)).to_contain("direct-access-not-user-space-driver:kernel-driver")
```

</details>

#### requires issued grants non-secure namespace and shared common driver logic

- requires issued grants non-secure namespace and shared common driver logic


<details>
<summary>Executable SSpec</summary>

Runnable source: 57 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires issued grants non-secure namespace and shared common driver logic")
val no_token = network_transfer_evidence(
    "simple-driver",
    "virtio-net",
    true,
    true,
    true,
    true,
    true,
    true,
    true,
    true,
    "user-space-driver",
    "resource-grant-set",
    "non-secure-resource-namespace",
    true,
    true
)
val bad_namespace = network_transfer_evidence(
    "simple-driver",
    "e1000",
    true,
    true,
    true,
    true,
    true,
    true,
    true,
    true,
    "user-space-driver",
    "resource-grant-set:tok=27",
    "secure-kernel-namespace",
    true,
    true
)
val missing_common = network_transfer_evidence(
    "simple-driver",
    "virtio-net",
    true,
    true,
    true,
    true,
    true,
    true,
    true,
    true,
    "user-space-driver",
    "resource-grant-set:tok=28",
    "non-secure-resource-namespace",
    false,
    true
)

expect(network_transfer_readiness_reason(no_token)).to_contain("missing-issued-device-grant-token:resource-grant-set")
expect(network_transfer_readiness_reason(bad_namespace)).to_contain("missing-non-secure-resource-namespace:secure-kernel-namespace")
expect(network_transfer_readiness_reason(missing_common)).to_contain("missing-common-driver-logic")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/drivers/virtio/network_device_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS network transfer evidence.
- SimpleOS network transfer evidence

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

- Canonical SPipe generation for source `7344248b641e043ba65cb26f08ae142bef44d796d17234aab555654dc15456a0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7344248b641e043ba65cb26f08ae142bef44d796d17234aab555654dc15456a0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7344248b641e043ba65cb26f08ae142bef44d796d17234aab555654dc15456a0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/unit/os/drivers/virtio/network_device_spec.spl
mirror: doc/06_spec/unit/os/drivers/virtio/network_device_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/drivers/virtio/network_device_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/drivers/virtio/network_device_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
