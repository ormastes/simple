# Pci Provider Specification

> <details>

<!-- sdn-diagram:id=pci_provider_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pci_provider_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pci_provider_spec -> std
pci_provider_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pci_provider_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pci Provider Specification

## Scenarios

### PCI provider contracts

#### selects a provider by board without fallback success

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(pci_provider_kind_name(pci_provider_from_board("x86_64-q35"))).to_equal("q35-config-io")
expect(pci_provider_kind_name(pci_provider_from_board("riscv64-virt"))).to_equal("pci-ecam")
expect(pci_provider_kind_name(pci_provider_from_board("mps2-an505"))).to_equal("no-pci")
expect(pci_provider_can_enumerate(pci_provider_from_board("mps2-an505"))).to_equal(false)
expect(pci_provider_refusal_reason(PciProviderKind.NoPci, "mps2-an505")).to_equal("pci-unavailable:mps2-an505")
```

</details>

#### builds config I/O and ECAM addresses deterministically

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = PciConfigTarget(bus: 1, device: 2, func: 3, offset: 0x10)
val config_io = pci_config_io_addr(target)
val expected_io = (1u32 << 31) | (1u32 << 16) | (2u32 << 11) | (3u32 << 8) | 0x10u32
expect(config_io).to_equal(expected_io)

val ecam = pci_ecam_addr(0x30000000u64, target)
val expected_ecam = 0x30000000u64 + (1u64 << 20) + (2u64 << 15) + (3u64 << 12) + 0x10u64
expect(ecam).to_equal(expected_ecam)
expect(pci_provider_config_addr(PciProviderKind.NoPci, 0x30000000u64, target)).to_equal(0u64)
expect(pci_provider_config_addr(PciProviderKind.Ecam, 0x30000000u64, target)).to_equal(expected_ecam)
```

</details>

#### decodes I/O, 32-bit MMIO, and 64-bit prefetchable BARs

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val io_bar = pci_bar_decode(0x0000C041u32, 0xFFFFFF01u32)
expect(io_bar.implemented).to_equal(true)
expect(io_bar.is_io).to_equal(true)
expect(io_bar.base_low).to_equal(0x0000C040u64)
expect(io_bar.size).to_equal(0x100u64)

val mmio_bar = pci_bar_decode(0xFEB90000u32, 0xFFFFF000u32)
expect(mmio_bar.is_io).to_equal(false)
expect(mmio_bar.is_mem64).to_equal(false)
expect(mmio_bar.base_low).to_equal(0xFEB90000u64)
expect(mmio_bar.size).to_equal(0x1000u64)

val mmio64_bar = pci_bar_decode(0x8000000Cu32, 0xFFFFC00Cu32)
expect(mmio64_bar.is_io).to_equal(false)
expect(mmio64_bar.is_mem64).to_equal(true)
expect(mmio64_bar.is_prefetchable).to_equal(true)
expect(mmio64_bar.base_low).to_equal(0x80000000u64)
expect(mmio64_bar.size).to_equal(0x4000u64)
```

</details>

#### does not invent BAR size for unimplemented BARs

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing = pci_bar_decode(0u32, 0xFFFFFFFFu32)
expect(missing.implemented).to_equal(false)
expect(missing.size).to_equal(0u64)
expect(pci_bar_size_from_probe(0xFFFFFFFFu32, false)).to_equal(0u64)
```

</details>

#### parses config snapshots and rejects absent vendor sentinels

1. target: PciConfigTarget
2. id dword:
3. class dword:
4. target: PciConfigTarget
   - Expected: parsed.? is true
   - Expected: dev.vendor_id equals `0x1B36`
   - Expected: dev.device_id equals `0x5845`
   - Expected: dev.class_code equals `0x01`
   - Expected: dev.subclass equals `0x08`
   - Expected: dev.prog_if equals `0x02`
   - Expected: dev.bar0.size equals `0x1000u64`
   - Expected: dev.irq_line equals `11`
   - Expected: pci_function_is_nvme(dev) is true
   - Expected: pci_function_from_snapshot(absent).? is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nvme = PciConfigSnapshot(
    target: PciConfigTarget(bus: 0, device: 4, func: 0, offset: 0),
    id_dword: (0x5845u32 << 16) | 0x1B36u32,
    class_dword: (0x01u32 << 24) | (0x08u32 << 16) | (0x02u32 << 8),
    header_dword: 0u32,
    bar0_raw: 0xFEB90000u32,
    bar0_probe_mask: 0xFFFFF000u32,
    bar1_raw: 0u32,
    bar1_probe_mask: 0xFFFFFFFFu32,
    irq_dword: 11u32
)
val absent = PciConfigSnapshot(
    target: PciConfigTarget(bus: 0, device: 5, func: 0, offset: 0),
    id_dword: 0xFFFFFFFFu32,
    class_dword: 0u32,
    header_dword: 0u32,
    bar0_raw: 0u32,
    bar0_probe_mask: 0xFFFFFFFFu32,
    bar1_raw: 0u32,
    bar1_probe_mask: 0xFFFFFFFFu32,
    irq_dword: 0u32
)
val parsed = pci_function_from_snapshot(nvme)
expect(parsed.?).to_equal(true)
val dev = parsed
expect(dev.vendor_id).to_equal(0x1B36)
expect(dev.device_id).to_equal(0x5845)
expect(dev.class_code).to_equal(0x01)
expect(dev.subclass).to_equal(0x08)
expect(dev.prog_if).to_equal(0x02)
expect(dev.bar0.size).to_equal(0x1000u64)
expect(dev.irq_line).to_equal(11)
expect(pci_function_is_nvme(dev)).to_equal(true)
expect(pci_function_from_snapshot(absent).?).to_equal(false)
```

</details>

#### enumerates snapshots and classifies q35 network and RDMA candidates

1. target: PciConfigTarget
2. id dword:
3. class dword:
4. target: PciConfigTarget
5. id dword:
6. class dword:
7. target: PciConfigTarget
8. id dword:
9. class dword:
   - Expected: functions.len() equals `3`
   - Expected: pci_function_is_virtio_net(functions[0]) is true
   - Expected: functions[0].multifunction is true
   - Expected: pci_function_is_e1000(functions[1]) is true
   - Expected: pci_function_is_infiniband(functions[2]) is true
   - Expected: pci_count_class(functions, 0x02, 0x00) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val virtio_net = PciConfigSnapshot(
    target: PciConfigTarget(bus: 0, device: 3, func: 0, offset: 0),
    id_dword: (0x1000u32 << 16) | 0x1AF4u32,
    class_dword: (0x02u32 << 24),
    header_dword: 0x00800000u32,
    bar0_raw: 0x0000C041u32,
    bar0_probe_mask: 0xFFFFFF01u32,
    bar1_raw: 0u32,
    bar1_probe_mask: 0xFFFFFFFFu32,
    irq_dword: 10u32
)
val e1000 = PciConfigSnapshot(
    target: PciConfigTarget(bus: 0, device: 6, func: 0, offset: 0),
    id_dword: (0x100Eu32 << 16) | 0x8086u32,
    class_dword: (0x02u32 << 24),
    header_dword: 0u32,
    bar0_raw: 0xFEB80000u32,
    bar0_probe_mask: 0xFFFF0000u32,
    bar1_raw: 0u32,
    bar1_probe_mask: 0xFFFFFFFFu32,
    irq_dword: 9u32
)
val ib = PciConfigSnapshot(
    target: PciConfigTarget(bus: 0, device: 7, func: 0, offset: 0),
    id_dword: (0x1017u32 << 16) | 0x15B3u32,
    class_dword: (0x0Cu32 << 24) | (0x06u32 << 16),
    header_dword: 0u32,
    bar0_raw: 0x8000000Cu32,
    bar0_probe_mask: 0xFFFFC00Cu32,
    bar1_raw: 0u32,
    bar1_probe_mask: 0xFFFFFFFFu32,
    irq_dword: 12u32
)
val functions = pci_enumerate_snapshots([virtio_net, e1000, ib])
expect(functions.len()).to_equal(3)
expect(pci_function_is_virtio_net(functions[0])).to_equal(true)
expect(functions[0].multifunction).to_equal(true)
expect(pci_function_is_e1000(functions[1])).to_equal(true)
expect(pci_function_is_infiniband(functions[2])).to_equal(true)
expect(pci_count_class(functions, 0x02, 0x00)).to_equal(2)
```

</details>

#### requires real BAR IRQ DMA and namespace evidence before PCI grants are ready

1. target: PciConfigTarget
2. id dword:
3. class dword:
   - Expected: parsed.? is true
   - Expected: pci_resource_grant_ready(ready) is true
   - Expected: pci_resource_grant_readiness_reason(no_bar) equals `missing-pci-bar0:nvme`
   - Expected: pci_resource_grant_readiness_reason(no_irq) equals `missing-pci-irq:virtio-net`
   - Expected: pci_resource_grant_readiness_reason(bad_namespace) equals `missing-pci-non-secure-namespace:secure-kernel-namespace`
   - Expected: pci_resource_grant_readiness_reason(no_token) equals `missing-pci-issued-grant-token:nvme`


<details>
<summary>Executable SSpec</summary>

Runnable source: 80 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nvme = PciConfigSnapshot(
    target: PciConfigTarget(bus: 0, device: 4, func: 0, offset: 0),
    id_dword: (0x5845u32 << 16) | 0x1B36u32,
    class_dword: (0x01u32 << 24) | (0x08u32 << 16) | (0x02u32 << 8),
    header_dword: 0u32,
    bar0_raw: 0xFEB90000u32,
    bar0_probe_mask: 0xFFFFF000u32,
    bar1_raw: 0u32,
    bar1_probe_mask: 0xFFFFFFFFu32,
    irq_dword: 11u32
)
val parsed = pci_function_from_snapshot(nvme)
expect(parsed.?).to_equal(true)

val ready = pci_resource_grant_evidence_from_function(
    "q35-config-io",
    "nvme",
    parsed,
    true,
    true,
    "non-secure-resource-namespace",
    101
)
expect(pci_resource_grant_ready(ready)).to_equal(true)

val no_bar = pci_resource_grant_evidence(
    "q35-config-io",
    "nvme",
    true,
    false,
    0u64,
    11,
    true,
    true,
    "non-secure-resource-namespace",
    101
)
expect(pci_resource_grant_readiness_reason(no_bar)).to_equal("missing-pci-bar0:nvme")

val no_irq = pci_resource_grant_evidence(
    "q35-config-io",
    "virtio-net",
    true,
    true,
    0x100u64,
    0xFF,
    true,
    true,
    "non-secure-resource-namespace",
    101
)
expect(pci_resource_grant_readiness_reason(no_irq)).to_equal("missing-pci-irq:virtio-net")

val bad_namespace = pci_resource_grant_evidence(
    "pci-ecam",
    "rdma",
    true,
    true,
    0x1000u64,
    12,
    true,
    true,
    "secure-kernel-namespace",
    101
)
expect(pci_resource_grant_readiness_reason(bad_namespace)).to_equal("missing-pci-non-secure-namespace:secure-kernel-namespace")

val no_token = pci_resource_grant_evidence(
    "q35-config-io",
    "nvme",
    true,
    true,
    0x1000u64,
    11,
    true,
    true,
    "non-secure-resource-namespace",
    0
)
expect(pci_resource_grant_readiness_reason(no_token)).to_equal("missing-pci-issued-grant-token:nvme")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/drivers/pci/pci_provider_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- PCI provider contracts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
