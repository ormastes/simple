# Capability Types Specification

> Tests for CapabilityToken, CapabilityKind, and CapabilitySet kernel types. Validates construction, the `has()` method, `pledge()` monotonic restriction, and the `full()` static constructor.

<!-- sdn-diagram:id=capability_types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=capability_types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

capability_types_spec -> std
capability_types_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=capability_types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 45 | 45 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Capability Types Specification

Tests for CapabilityToken, CapabilityKind, and CapabilitySet kernel types. Validates construction, the `has()` method, `pledge()` monotonic restriction, and the `full()` static constructor.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OS-003 |
| Category | Runtime |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/os/kernel/types/capability_types_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for CapabilityToken, CapabilityKind, and CapabilitySet kernel types.
Validates construction, the `has()` method, `pledge()` monotonic restriction,
and the `full()` static constructor.

## Scenarios

### CapabilityToken

#### stores kind, generation, and owner

1. kind: CapabilityKind FileRead
   - Expected: token.generation equals `1`
   - Expected: token.owner equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val token = CapabilityToken(
    kind: CapabilityKind.FileRead(path_prefix: "/tmp"),
    generation: 1,
    owner: 42
)
expect(token.generation).to_equal(1)
expect(token.owner).to_equal(42)
```

</details>

#### can hold FileWrite capability

1. kind: CapabilityKind FileWrite
   - Expected: token.generation equals `5`
   - Expected: token.owner equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val token = CapabilityToken(
    kind: CapabilityKind.FileWrite(path_prefix: "/var/log"),
    generation: 5,
    owner: 10
)
expect(token.generation).to_equal(5)
expect(token.owner).to_equal(10)
```

</details>

#### can hold NetConnect capability

1. kind: CapabilityKind NetConnect
   - Expected: token.generation equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val token = CapabilityToken(
    kind: CapabilityKind.NetConnect(port: 443),
    generation: 2,
    owner: 7
)
expect(token.generation).to_equal(2)
```

</details>

### CapabilityKind

### File capabilities

#### FileRead carries path prefix

1. CapabilityKind FileRead
   - Expected: is_file_read is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CapabilityKind.FileRead(path_prefix: "/home")
val is_file_read = match kind:
    CapabilityKind.FileRead(path_prefix): true
    _: false
expect(is_file_read).to_equal(true)
```

</details>

#### FileWrite carries path prefix

1. CapabilityKind FileWrite
   - Expected: is_file_write is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CapabilityKind.FileWrite(path_prefix: "/tmp")
val is_file_write = match kind:
    CapabilityKind.FileWrite(path_prefix): true
    _: false
expect(is_file_write).to_equal(true)
```

</details>

#### FileCreate carries path prefix

1. CapabilityKind FileCreate
   - Expected: is_file_create is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CapabilityKind.FileCreate(path_prefix: "/data")
val is_file_create = match kind:
    CapabilityKind.FileCreate(path_prefix): true
    _: false
expect(is_file_create).to_equal(true)
```

</details>

#### FileExec carries path prefix

1. CapabilityKind FileExec
   - Expected: is_file_exec is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CapabilityKind.FileExec(path_prefix: "/usr/bin")
val is_file_exec = match kind:
    CapabilityKind.FileExec(path_prefix): true
    _: false
expect(is_file_exec).to_equal(true)
```

</details>

### Network capabilities

#### NetConnect carries port

1. CapabilityKind NetConnect
   - Expected: is_net is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CapabilityKind.NetConnect(port: 80)
val is_net = match kind:
    CapabilityKind.NetConnect(port): true
    _: false
expect(is_net).to_equal(true)
```

</details>

#### NetListen carries port

1. CapabilityKind NetListen
   - Expected: is_listen is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CapabilityKind.NetListen(port: 8080)
val is_listen = match kind:
    CapabilityKind.NetListen(port): true
    _: false
expect(is_listen).to_equal(true)
```

</details>

#### NetRaw has no payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CapabilityKind.NetRaw
val is_raw = match kind:
    CapabilityKind.NetRaw: true
    _: false
expect(is_raw).to_equal(true)
```

</details>

### Process capabilities

#### ProcessSpawn has no payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CapabilityKind.ProcessSpawn
val is_spawn = match kind:
    CapabilityKind.ProcessSpawn: true
    _: false
expect(is_spawn).to_equal(true)
```

</details>

#### ProcessSignal carries target task

1. CapabilityKind ProcessSignal
   - Expected: is_signal is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CapabilityKind.ProcessSignal(target: 99)
val is_signal = match kind:
    CapabilityKind.ProcessSignal(target): true
    _: false
expect(is_signal).to_equal(true)
```

</details>

### Hardware capabilities

#### PortIO carries base and count

1. CapabilityKind PortIO
   - Expected: is_port is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CapabilityKind.PortIO(base: 0x3F8, count: 8)
val is_port = match kind:
    CapabilityKind.PortIO(base, count): true
    _: false
expect(is_port).to_equal(true)
```

</details>

#### Mmio carries base and size

1. CapabilityKind Mmio
   - Expected: is_mmio is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CapabilityKind.Mmio(base: 0xFEE00000, size: 4096)
val is_mmio = match kind:
    CapabilityKind.Mmio(base, size): true
    _: false
expect(is_mmio).to_equal(true)
```

</details>

#### Irq carries interrupt number

1. CapabilityKind Irq
   - Expected: is_irq is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CapabilityKind.Irq(irq_num: 14)
val is_irq = match kind:
    CapabilityKind.Irq(irq_num): true
    _: false
expect(is_irq).to_equal(true)
```

</details>

#### DeviceEnumerate carries PCI class tuple

1. CapabilityKind DeviceEnumerate
   - Expected: is_device_enum is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CapabilityKind.DeviceEnumerate(class_code: 1, subclass: 8)
val is_device_enum = match kind:
    CapabilityKind.DeviceEnumerate(class_code, subclass): true
    _: false
expect(is_device_enum).to_equal(true)
```

</details>

#### DeviceGrant carries BDF tuple

1. CapabilityKind DeviceGrant
   - Expected: is_device_grant is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CapabilityKind.DeviceGrant(bdf_bus: 0, bdf_device: 4, bdf_func: 0)
val is_device_grant = match kind:
    CapabilityKind.DeviceGrant(bdf_bus, bdf_device, bdf_func): true
    _: false
expect(is_device_grant).to_equal(true)
```

</details>

#### DeviceBarMap carries BDF and BAR index

1. CapabilityKind DeviceBarMap
   - Expected: is_bar is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CapabilityKind.DeviceBarMap(bdf_bus: 0, bdf_device: 4, bdf_func: 0, bar_index: 0)
val is_bar = match kind:
    CapabilityKind.DeviceBarMap(bdf_bus, bdf_device, bdf_func, bar_index): true
    _: false
expect(is_bar).to_equal(true)
```

</details>

#### DeviceDma carries BDF and maximum byte authority

1. CapabilityKind DeviceDma
   - Expected: is_dma is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CapabilityKind.DeviceDma(bdf_bus: 0, bdf_device: 4, bdf_func: 0, max_bytes: 65536)
val is_dma = match kind:
    CapabilityKind.DeviceDma(bdf_bus, bdf_device, bdf_func, max_bytes): true
    _: false
expect(is_dma).to_equal(true)
```

</details>

#### IommuDomain carries domain id

1. CapabilityKind IommuDomain
   - Expected: is_iommu is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CapabilityKind.IommuDomain(domain_id: 7)
val is_iommu = match kind:
    CapabilityKind.IommuDomain(domain_id): true
    _: false
expect(is_iommu).to_equal(true)
```

</details>

### Storage capabilities

#### BlockDevice carries path and rights

1. CapabilityKind BlockDevice
   - Expected: is_block is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CapabilityKind.BlockDevice(path: "/dev/nvme0n1", rights: CAP_RIGHT_READ)
val is_block = match kind:
    CapabilityKind.BlockDevice(path, rights): true
    _: false
expect(is_block).to_equal(true)
```

</details>

#### StorageNamespace carries controller, nsid, and rights

1. CapabilityKind StorageNamespace
   - Expected: is_namespace is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CapabilityKind.StorageNamespace(controller_id: 0, nsid: 2, rights: CAP_RIGHT_READ)
val is_namespace = match kind:
    CapabilityKind.StorageNamespace(controller_id, nsid, rights): true
    _: false
expect(is_namespace).to_equal(true)
```

</details>

#### StoragePartition carries device path and write rights

1. CapabilityKind StoragePartition
   - Expected: is_partition is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CapabilityKind.StoragePartition(path: "/dev/nvme0n1p3", rights: CAP_RIGHT_READ + CAP_RIGHT_WRITE)
val is_partition = match kind:
    CapabilityKind.StoragePartition(path, rights): true
    _: false
expect(is_partition).to_equal(true)
```

</details>

#### StorageExtent carries bounded LBA authority and generation

1. CapabilityKind StorageExtent
   - Expected: is_extent is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CapabilityKind.StorageExtent(object_id: 44, offset_lba: 128, lba_count: 64, rights: CAP_RIGHT_READ, generation: 9)
val is_extent = match kind:
    CapabilityKind.StorageExtent(object_id, offset_lba, lba_count, rights, generation): true
    _: false
expect(is_extent).to_equal(true)
```

</details>

#### Mount carries path prefix and mount rights

1. CapabilityKind Mount
   - Expected: is_mount is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CapabilityKind.Mount(path_prefix: "/data/app", rights: CAP_RIGHT_READ + CAP_RIGHT_WRITE + CAP_RIGHT_MOUNT)
val is_mount = match kind:
    CapabilityKind.Mount(path_prefix, rights): true
    _: false
expect(is_mount).to_equal(true)
```

</details>

#### IoQueue carries queue id and submit rights

1. CapabilityKind IoQueue
   - Expected: is_queue is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CapabilityKind.IoQueue(queue_id: SIMPLEOS_NVME_FIRST_DATA_QUEUE_ID, rights: CAP_RIGHT_QUEUE_SUBMIT)
val is_queue = match kind:
    CapabilityKind.IoQueue(queue_id, rights): true
    _: false
expect(is_queue).to_equal(true)
```

</details>

#### defines reserved NVMe queue ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SIMPLEOS_NVME_ADMIN_QUEUE_ID).to_equal(0)
expect(SIMPLEOS_NVME_SYSTEM_QUEUE_ID).to_equal(1)
expect(SIMPLEOS_NVME_FIRST_DATA_QUEUE_ID).to_equal(2)
```

</details>

### IPC capabilities

#### IpcConnect carries port name

1. CapabilityKind IpcConnect
   - Expected: is_ipc is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CapabilityKind.IpcConnect(port_name: "vfs")
val is_ipc = match kind:
    CapabilityKind.IpcConnect(port_name): true
    _: false
expect(is_ipc).to_equal(true)
```

</details>

#### IpcListen carries port name

1. CapabilityKind IpcListen
   - Expected: is_listen is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CapabilityKind.IpcListen(port_name: "compositor")
val is_listen = match kind:
    CapabilityKind.IpcListen(port_name): true
    _: false
expect(is_listen).to_equal(true)
```

</details>

### System capabilities

#### SystemReboot has no payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CapabilityKind.SystemReboot
val is_reboot = match kind:
    CapabilityKind.SystemReboot: true
    _: false
expect(is_reboot).to_equal(true)
```

</details>

#### SystemMount has no payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CapabilityKind.SystemMount
val is_mount = match kind:
    CapabilityKind.SystemMount: true
    _: false
expect(is_mount).to_equal(true)
```

</details>

#### SystemTime has no payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = CapabilityKind.SystemTime
val is_time = match kind:
    CapabilityKind.SystemTime: true
    _: false
expect(is_time).to_equal(true)
```

</details>

### CapabilitySet

### full

#### starts with empty caps list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cs = CapabilitySet.full()
expect(cs.caps.len()).to_equal(0)
```

</details>

#### starts not pledged

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cs = CapabilitySet.full()
expect(cs.is_pledged).to_equal(false)
```

</details>

### has

#### returns false for empty set

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cs = CapabilitySet.full()
val result = cs.has(CapabilityKind.ProcessSpawn)
expect(result).to_equal(false)
```

</details>

#### returns true when capability is present

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val token = CapabilityToken(
    kind: CapabilityKind.ProcessSpawn,
    generation: 1,
    owner: 1
)
val cs = CapabilitySet(caps: [token], is_pledged: false)
val result = cs.has(CapabilityKind.ProcessSpawn)
expect(result).to_equal(true)
```

</details>

#### returns false for non-matching capability kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val token = CapabilityToken(
    kind: CapabilityKind.ProcessSpawn,
    generation: 1,
    owner: 1
)
val cs = CapabilitySet(caps: [token], is_pledged: false)
val result = cs.has(CapabilityKind.SystemReboot)
expect(result).to_equal(false)
```

</details>

#### allows file prefixes through containment

1. kind: CapabilityKind FileRead
   - Expected: cs.has(CapabilityKind.FileRead(path_prefix: "/data/app/db")) is true
   - Expected: cs.has(CapabilityKind.FileRead(path_prefix: "/etc/passwd")) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val token = CapabilityToken(
    kind: CapabilityKind.FileRead(path_prefix: "/data/app"),
    generation: 1,
    owner: 1
)
val cs = CapabilitySet(caps: [token], is_pledged: false)
expect(cs.has(CapabilityKind.FileRead(path_prefix: "/data/app/db"))).to_equal(true)
expect(cs.has(CapabilityKind.FileRead(path_prefix: "/etc/passwd"))).to_equal(false)
```

</details>

#### allows DMA requests up to the granted byte limit

1. kind: CapabilityKind DeviceDma
   - Expected: cs.has(CapabilityKind.DeviceDma(bdf_bus: 0, bdf_device: 4, bdf_func: 0, max_bytes: 4096)) is true
   - Expected: cs.has(CapabilityKind.DeviceDma(bdf_bus: 0, bdf_device: 4, bdf_func: 0, max_bytes: 131072)) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val token = CapabilityToken(
    kind: CapabilityKind.DeviceDma(bdf_bus: 0, bdf_device: 4, bdf_func: 0, max_bytes: 65536),
    generation: 1,
    owner: 1
)
val cs = CapabilitySet(caps: [token], is_pledged: false)
expect(cs.has(CapabilityKind.DeviceDma(bdf_bus: 0, bdf_device: 4, bdf_func: 0, max_bytes: 4096))).to_equal(true)
expect(cs.has(CapabilityKind.DeviceDma(bdf_bus: 0, bdf_device: 4, bdf_func: 0, max_bytes: 131072))).to_equal(false)
```

</details>

#### allows storage partition subrights only when granted

1. kind: CapabilityKind StoragePartition
   - Expected: cs.has(CapabilityKind.StoragePartition(path: "/dev/nvme0n1p3", rights: CAP_RIGHT_READ)) is true
   - Expected: cs.has(CapabilityKind.StoragePartition(path: "/dev/nvme0n1p3", rights: CAP_RIGHT_MOUNT)) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val token = CapabilityToken(
    kind: CapabilityKind.StoragePartition(path: "/dev/nvme0n1p3", rights: CAP_RIGHT_READ + CAP_RIGHT_WRITE),
    generation: 1,
    owner: 1
)
val cs = CapabilitySet(caps: [token], is_pledged: false)
expect(cs.has(CapabilityKind.StoragePartition(path: "/dev/nvme0n1p3", rights: CAP_RIGHT_READ))).to_equal(true)
expect(cs.has(CapabilityKind.StoragePartition(path: "/dev/nvme0n1p3", rights: CAP_RIGHT_MOUNT))).to_equal(false)
```

</details>

#### allows bounded storage extents with matching generation

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val held = CapabilityKind.StorageExtent(object_id: 44, offset_lba: 100, lba_count: 50, rights: CAP_RIGHT_READ, generation: 7)
val inside = CapabilityKind.StorageExtent(object_id: 44, offset_lba: 120, lba_count: 8, rights: CAP_RIGHT_READ, generation: 7)
val stale = CapabilityKind.StorageExtent(object_id: 44, offset_lba: 120, lba_count: 8, rights: CAP_RIGHT_READ, generation: 8)
expect(capability_kind_allows(held, inside)).to_equal(true)
expect(capability_kind_allows(held, stale)).to_equal(false)
```

</details>

### pledge

#### sets is_pledged to true

1. var cs = CapabilitySet
2. cs pledge
   - Expected: cs.is_pledged is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cs = CapabilitySet(caps: [], is_pledged: false)
cs.pledge([])
expect(cs.is_pledged).to_equal(true)
```

</details>

#### filters caps to only allowed kinds

1. cs pledge
   - Expected: has_spawn is true
   - Expected: has_reboot is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spawn_token = CapabilityToken(
    kind: CapabilityKind.ProcessSpawn,
    generation: 1,
    owner: 1
)
val reboot_token = CapabilityToken(
    kind: CapabilityKind.SystemReboot,
    generation: 2,
    owner: 1
)
var cs = CapabilitySet(
    caps: [spawn_token, reboot_token],
    is_pledged: false
)
cs.pledge([CapabilityKind.ProcessSpawn])
# Only ProcessSpawn should remain
val has_spawn = cs.has(CapabilityKind.ProcessSpawn)
expect(has_spawn).to_equal(true)
val has_reboot = cs.has(CapabilityKind.SystemReboot)
expect(has_reboot).to_equal(false)
```

</details>

#### double pledge is no-op (already pledged)

1. cs pledge
   - Expected: cs.is_pledged is true
   - Expected: cs.caps.len() equals `0`
2. cs pledge
   - Expected: cs.is_pledged is true
   - Expected: cs.caps.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val token = CapabilityToken(
    kind: CapabilityKind.ProcessSpawn,
    generation: 1,
    owner: 1
)
var cs = CapabilitySet(
    caps: [token],
    is_pledged: false
)
# First pledge: remove all
cs.pledge([])
expect(cs.is_pledged).to_equal(true)
expect(cs.caps.len()).to_equal(0)

# Second pledge: should be no-op, cannot add back
cs.pledge([CapabilityKind.ProcessSpawn])
expect(cs.is_pledged).to_equal(true)
# Still empty because second pledge was ignored
expect(cs.caps.len()).to_equal(0)
```

</details>

#### pledge with empty allowed list removes all caps

1. cs pledge
   - Expected: cs.caps.len() equals `0`
   - Expected: cs.is_pledged is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val token = CapabilityToken(
    kind: CapabilityKind.NetRaw,
    generation: 1,
    owner: 1
)
var cs = CapabilitySet(
    caps: [token],
    is_pledged: false
)
cs.pledge([])
expect(cs.caps.len()).to_equal(0)
expect(cs.is_pledged).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 45 |
| Active scenarios | 45 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
