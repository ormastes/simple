# Device Mem Types Specification

> <details>

<!-- sdn-diagram:id=device_mem_types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=device_mem_types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

device_mem_types_spec -> std
device_mem_types_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=device_mem_types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Device Mem Types Specification

## Scenarios

### DeviceGrant resource token metadata

#### derives nonzero BAR IRQ DMA and IOMMU tokens from owner and BDF

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = device_grant_token_base(0u8, 4u8, 0u8, 42u64)
expect(device_grant_bar_token(base) != 0u64).to_equal(true)
expect(device_grant_irq_token(base) != 0u64).to_equal(true)
expect(device_grant_dma_token(base) != 0u64).to_equal(true)
expect(device_grant_iommu_token(base) != 0u64).to_equal(true)
expect(device_grant_iommu_domain_id(0u8, 4u8, 0u8)).to_equal(1025u32)
```

</details>

#### reports a resource-grant-set label only when all grant tokens exist

1. bar0 cap: device grant bar token
2. irq cap: device grant irq token
3. dma cap: device grant dma token
4. iommu domain id: device grant iommu domain id
5. iommu cap: device grant iommu token
   - Expected: device_grant_has_resource_tokens(grant) is true
   - Expected: device_grant_matches_owner_task(grant, 42u64) is true
   - Expected: device_grant_matches_owner_task(grant, 43u64) is false
   - Expected: device_grant_is_isolated(grant) is true
6. bar0 cap: device grant bar token
7. irq cap: device grant irq token
   - Expected: device_grant_has_resource_tokens(incomplete) is false
   - Expected: device_grant_resource_set_label(incomplete) equals `resource-grant-set:missing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 53 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = device_grant_token_base(0u8, 4u8, 0u8, 42u64)
val grant = DeviceGrant(
    pci_vendor: 0x1B36u16,
    pci_device: 0x5845u16,
    pci_bus: 0u8,
    pci_dev: 4u8,
    pci_func: 0u8,
    pci_class: 1u8,
    pci_subclass: 8u8,
    bar0_phys: 0xFEB90000u64,
    bar0_size: 0x1000u64,
    bar0_cap: device_grant_bar_token(base),
    irq_vector: 43u32,
    irq_notification_id: 1u64,
    irq_notification_bit: 1u64,
    irq_cap: device_grant_irq_token(base),
    dma_device_addr: 0u64,
    dma_host_addr: 0u64,
    dma_size: 0u64,
    dma_cap: device_grant_dma_token(base),
    iommu_domain_id: device_grant_iommu_domain_id(0u8, 4u8, 0u8),
    iommu_cap: device_grant_iommu_token(base)
)
expect(device_grant_has_resource_tokens(grant)).to_equal(true)
expect(device_grant_matches_owner_task(grant, 42u64)).to_equal(true)
expect(device_grant_matches_owner_task(grant, 43u64)).to_equal(false)
expect(device_grant_is_isolated(grant)).to_equal(true)
expect(device_grant_resource_set_label(grant)).to_contain("resource-grant-set:tok=")

val incomplete = DeviceGrant(
    pci_vendor: 0x1B36u16,
    pci_device: 0x5845u16,
    pci_bus: 0u8,
    pci_dev: 4u8,
    pci_func: 0u8,
    pci_class: 1u8,
    pci_subclass: 8u8,
    bar0_phys: 0xFEB90000u64,
    bar0_size: 0x1000u64,
    bar0_cap: device_grant_bar_token(base),
    irq_vector: 43u32,
    irq_notification_id: 1u64,
    irq_notification_bit: 1u64,
    irq_cap: device_grant_irq_token(base),
    dma_device_addr: 0u64,
    dma_host_addr: 0u64,
    dma_size: 0u64,
    dma_cap: 0u64,
    iommu_domain_id: 0u32,
    iommu_cap: 0u64
)
expect(device_grant_has_resource_tokens(incomplete)).to_equal(false)
expect(device_grant_resource_set_label(incomplete)).to_equal("resource-grant-set:missing")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/types/device_mem_types_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DeviceGrant resource token metadata

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
