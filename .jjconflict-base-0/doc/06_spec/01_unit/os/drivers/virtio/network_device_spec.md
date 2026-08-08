# Network Device Specification

> <details>

<!-- sdn-diagram:id=network_device_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=network_device_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

network_device_spec -> std
network_device_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=network_device_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Network Device Specification

## Scenarios

### SimpleOS network transfer evidence

#### rejects C bridge network transfer claims

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 55 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 55 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/os/drivers/virtio/network_device_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
