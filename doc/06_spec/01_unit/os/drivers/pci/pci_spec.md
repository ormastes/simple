# PCI Bus Specification

> Tests PCI configuration address construction, device classification methods, and bus scanning/lookup functionality.

<!-- sdn-diagram:id=pci_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pci_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pci_spec -> std
pci_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pci_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# PCI Bus Specification

Tests PCI configuration address construction, device classification methods, and bus scanning/lookup functionality.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OS-PCI |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | In Progress |
| Source | `test/01_unit/os/drivers/pci/pci_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests PCI configuration address construction, device classification
methods, and bus scanning/lookup functionality.

## Scenarios

### PCI

### pci_config_addr

#### sets enable bit (bit 31)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val addr = pci_config_addr(0, 0, 0, 0)
expect((addr >> 31) & 1).to_equal(1)
```

</details>

#### encodes bus in bits 23-16

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val addr = pci_config_addr(5, 0, 0, 0)
val bus_field = (addr >> 16) & 0xFF
expect(bus_field).to_equal(5)
```

</details>

#### encodes device in bits 15-11

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val addr = pci_config_addr(0, 3, 0, 0)
val dev_field = (addr >> 11) & 0x1F
expect(dev_field).to_equal(3)
```

</details>

#### encodes function in bits 10-8

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val addr = pci_config_addr(0, 0, 7, 0)
val func_field = (addr >> 8) & 0x07
expect(func_field).to_equal(7)
```

</details>

#### encodes offset aligned to dword (bits 7-2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val addr = pci_config_addr(0, 0, 0, 0x3C)
val offset_field = addr & 0xFF
expect(offset_field).to_equal(0x3C)
```

</details>

#### masks offset low 2 bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val addr = pci_config_addr(0, 0, 0, 0x3F)
val offset_field = addr & 0x03
expect(offset_field).to_equal(0)
```

</details>

#### combines all fields correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bus=1, device=2, function=3, offset=0x10
val addr = pci_config_addr(1, 2, 3, 0x10)
# Expected: (1<<31) | (1<<16) | (2<<11) | (3<<8) | 0x10
val expected = (1 << 31) | (1 << 16) | (2 << 11) | (3 << 8) | 0x10
expect(addr).to_equal(expected)
```

</details>

### PciDevice.is_valid

#### returns true for valid vendor

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = make_device(0x8086, 0x1234, 0x02)
expect(dev.is_valid()).to_equal(true)
```

</details>

#### returns false for 0xFFFF vendor (no device)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = make_device(0xFFFF, 0x0000, 0x00)
expect(dev.is_valid()).to_equal(false)
```

</details>

### PciDevice.is_bridge

#### returns true for bridge class 0x06

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = make_device(0x8086, 0x1234, 0x06)
expect(dev.is_bridge()).to_equal(true)
```

</details>

#### returns false for non-bridge class

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = make_device(0x8086, 0x1234, 0x02)
expect(dev.is_bridge()).to_equal(false)
```

</details>

### PciDevice.is_virtio

#### returns true for VirtIO vendor 0x1AF4

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = make_device(0x1AF4, 0x1000, 0x02)
expect(dev.is_virtio()).to_equal(true)
```

</details>

#### returns false for Intel vendor

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = make_device(0x8086, 0x1000, 0x02)
expect(dev.is_virtio()).to_equal(false)
```

</details>

### PciBus

### new

#### starts with no devices

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bus = PciBus.new()
expect(bus.device_count()).to_equal(0)
```

</details>

### find_by_vendor_device

#### finds matching device

1. var bus = PciBus new
2. bus devices push
3. bus devices push
   - Expected: found.? is true
   - Expected: result.vendor_id equals `0x1AF4`
   - Expected: result.device_id equals `0x1001`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bus = PciBus.new()
val dev1 = PciDevice(
    bus: 0, device: 0, function: 0,
    vendor_id: 0x8086, device_id: 0x100E,
    class_code: 0x02, subclass: 0x00, prog_if: 0x00,
    header_type: 0x00, bar0: 0xFEBC0000, bar1: 0,
    irq_line: 11
)
val dev2 = PciDevice(
    bus: 0, device: 1, function: 0,
    vendor_id: 0x1AF4, device_id: 0x1001,
    class_code: 0x01, subclass: 0x00, prog_if: 0x00,
    header_type: 0x00, bar0: 0xFEBD0000, bar1: 0,
    irq_line: 10
)
bus.devices.push(dev1)
bus.devices.push(dev2)

val found = bus.find_by_vendor_device(0x1AF4, 0x1001)
expect(found.?).to_equal(true)
val result = found.unwrap()
expect(result.vendor_id).to_equal(0x1AF4)
expect(result.device_id).to_equal(0x1001)
```

</details>

#### returns nil when not found

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bus = PciBus.new()
val found = bus.find_by_vendor_device(0x9999, 0x1111)
expect(found.?).to_equal(false)
```

</details>

### find_virtio_devices

#### finds all VirtIO devices

1. var bus = PciBus new
2. bus devices push
3. bus devices push
4. bus devices push
   - Expected: virtio.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bus = PciBus.new()
bus.devices.push(make_device(0x1AF4, 0x1000, 0x02))
bus.devices.push(make_device(0x8086, 0x100E, 0x02))
bus.devices.push(make_device(0x1AF4, 0x1001, 0x01))
val virtio = bus.find_virtio_devices()
expect(virtio.len()).to_equal(2)
```

</details>

### find_by_class

#### finds devices by class and subclass

1. var bus = PciBus new
2. bus devices push
3. bus devices push
   - Expected: nets.len() equals `1`
   - Expected: nets[0].vendor_id equals `0x8086`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bus = PciBus.new()
val net_dev = PciDevice(
    bus: 0, device: 0, function: 0,
    vendor_id: 0x8086, device_id: 0x100E,
    class_code: 0x02, subclass: 0x00, prog_if: 0x00,
    header_type: 0x00, bar0: 0, bar1: 0, irq_line: 0
)
val storage_dev = PciDevice(
    bus: 0, device: 1, function: 0,
    vendor_id: 0x8086, device_id: 0x2922,
    class_code: 0x01, subclass: 0x06, prog_if: 0x01,
    header_type: 0x00, bar0: 0, bar1: 0, irq_line: 0
)
bus.devices.push(net_dev)
bus.devices.push(storage_dev)
val nets = bus.find_by_class(0x02, 0x00)
expect(nets.len()).to_equal(1)
expect(nets[0].vendor_id).to_equal(0x8086)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
