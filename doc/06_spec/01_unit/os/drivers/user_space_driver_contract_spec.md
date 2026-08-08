# User Space Driver Contract Specification

> <details>

<!-- sdn-diagram:id=user_space_driver_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=user_space_driver_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

user_space_driver_contract_spec -> std
user_space_driver_contract_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=user_space_driver_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# User Space Driver Contract Specification

## Scenarios

### SimpleOS user-space direct driver contract

#### requires NVMe direct access to run as a user-space driver with grants

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 71 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/os/drivers/user_space_driver_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
