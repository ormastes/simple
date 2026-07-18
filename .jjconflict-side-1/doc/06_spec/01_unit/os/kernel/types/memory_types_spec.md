# Memory Types Specification

> Tests for PhysAddr, VirtAddr, PageFrame, and VmFlags kernel types. Validates construction, address arithmetic, and flag static constructors.

<!-- sdn-diagram:id=memory_types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=memory_types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

memory_types_spec -> std
memory_types_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=memory_types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 42 | 42 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Memory Types Specification

Tests for PhysAddr, VirtAddr, PageFrame, and VmFlags kernel types. Validates construction, address arithmetic, and flag static constructors.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OS-001 |
| Category | Runtime |
| Difficulty | 2/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/os/kernel/types/memory_types_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for PhysAddr, VirtAddr, PageFrame, and VmFlags kernel types.
Validates construction, address arithmetic, and flag static constructors.

## Scenarios

### MemoryTypes

### PhysAddr

#### stores the physical address value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pa = PhysAddr(addr: 0x1000)
expect(pa.addr).to_equal(0x1000)
```

</details>

#### supports zero address

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pa = PhysAddr(addr: 0)
expect(pa.addr).to_equal(0)
```

</details>

#### supports large address

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pa = PhysAddr(addr: 0xFFFFFFFF)
expect(pa.addr).to_equal(0xFFFFFFFF)
```

</details>

### VirtAddr

#### stores the virtual address value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val va = VirtAddr(addr: 0xDEAD0000)
expect(va.addr).to_equal(0xDEAD0000)
```

</details>

#### supports zero address

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val va = VirtAddr(addr: 0)
expect(va.addr).to_equal(0)
```

</details>

### PageFrame

### construction

#### stores the page frame number

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = PageFrame(pfn: 42)
expect(frame.pfn).to_equal(42)
```

</details>

#### supports zero pfn

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = PageFrame(pfn: 0)
expect(frame.pfn).to_equal(0)
```

</details>

### to_phys_addr

#### converts pfn to physical address by multiplying by 4096

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = PageFrame(pfn: 1)
val pa = frame.to_phys_addr()
expect(pa.addr).to_equal(4096)
```

</details>

#### converts pfn 42 to address 172032

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = PageFrame(pfn: 42)
val pa = frame.to_phys_addr()
expect(pa.addr).to_equal(42 * 4096)
```

</details>

#### converts pfn 0 to address 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = PageFrame(pfn: 0)
val pa = frame.to_phys_addr()
expect(pa.addr).to_equal(0)
```

</details>

#### converts pfn 256 to address 1048576 (1MB)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = PageFrame(pfn: 256)
val pa = frame.to_phys_addr()
expect(pa.addr).to_equal(1048576)
```

</details>

### from_phys_addr

#### converts physical address to pfn by dividing by 4096

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pa = PhysAddr(addr: 4096)
val frame = PageFrame.from_phys_addr(pa)
expect(frame.pfn).to_equal(1)
```

</details>

#### converts address 172032 to pfn 42

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pa = PhysAddr(addr: 172032)
val frame = PageFrame.from_phys_addr(pa)
expect(frame.pfn).to_equal(42)
```

</details>

#### converts address 0 to pfn 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pa = PhysAddr(addr: 0)
val frame = PageFrame.from_phys_addr(pa)
expect(frame.pfn).to_equal(0)
```

</details>

#### truncates non-aligned addresses

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pa = PhysAddr(addr: 5000)
val frame = PageFrame.from_phys_addr(pa)
expect(frame.pfn).to_equal(1)
```

</details>

### round-trip

#### pfn -> phys_addr -> pfn preserves the value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = PageFrame(pfn: 100)
val pa = original.to_phys_addr()
val restored = PageFrame.from_phys_addr(pa)
expect(restored.pfn).to_equal(100)
```

</details>

### VmFlags

### kernel_rw

#### is present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = VmFlags.kernel_rw()
expect(flags.present).to_equal(true)
```

</details>

#### is writable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = VmFlags.kernel_rw()
expect(flags.writable).to_equal(true)
```

</details>

#### is not user-accessible

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = VmFlags.kernel_rw()
expect(flags.user).to_equal(false)
```

</details>

#### has write_through disabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = VmFlags.kernel_rw()
expect(flags.write_through).to_equal(false)
```

</details>

#### has cache_disable disabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = VmFlags.kernel_rw()
expect(flags.cache_disable).to_equal(false)
```

</details>

#### has no_execute enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = VmFlags.kernel_rw()
expect(flags.no_execute).to_equal(true)
```

</details>

### kernel_ro

#### is present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = VmFlags.kernel_ro()
expect(flags.present).to_equal(true)
```

</details>

#### is not writable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = VmFlags.kernel_ro()
expect(flags.writable).to_equal(false)
```

</details>

#### is not user-accessible

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = VmFlags.kernel_ro()
expect(flags.user).to_equal(false)
```

</details>

#### has write_through disabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = VmFlags.kernel_ro()
expect(flags.write_through).to_equal(false)
```

</details>

#### has cache_disable disabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = VmFlags.kernel_ro()
expect(flags.cache_disable).to_equal(false)
```

</details>

### user_rw

#### is present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = VmFlags.user_rw()
expect(flags.present).to_equal(true)
```

</details>

#### is writable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = VmFlags.user_rw()
expect(flags.writable).to_equal(true)
```

</details>

#### is user-accessible

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = VmFlags.user_rw()
expect(flags.user).to_equal(true)
```

</details>

#### has no_execute enabled for data pages

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = VmFlags.user_rw()
expect(flags.no_execute).to_equal(true)
```

</details>

### user_rx

#### is present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = VmFlags.user_rx()
expect(flags.present).to_equal(true)
```

</details>

#### is not writable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = VmFlags.user_rx()
expect(flags.writable).to_equal(false)
```

</details>

#### is user-accessible

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = VmFlags.user_rx()
expect(flags.user).to_equal(true)
```

</details>

#### has no_execute disabled for executable pages

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = VmFlags.user_rx()
expect(flags.no_execute).to_equal(false)
```

</details>

### mmio

#### is present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = VmFlags.mmio()
expect(flags.present).to_equal(true)
```

</details>

#### is writable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = VmFlags.mmio()
expect(flags.writable).to_equal(true)
```

</details>

#### is not user-accessible

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = VmFlags.mmio()
expect(flags.user).to_equal(false)
```

</details>

#### has write_through enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = VmFlags.mmio()
expect(flags.write_through).to_equal(true)
```

</details>

#### has cache_disable enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = VmFlags.mmio()
expect(flags.cache_disable).to_equal(true)
```

</details>

#### has no_execute enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = VmFlags.mmio()
expect(flags.no_execute).to_equal(true)
```

</details>

### VmMap

#### stores all mapping fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val virt = VirtAddr(addr: 0x1000)
val phys = PhysAddr(addr: 0x2000)
val flags = VmFlags.kernel_rw()
val mapping = VmMap(virt: virt, phys: phys, size: 4096, flags: flags)
expect(mapping.virt.addr).to_equal(0x1000)
expect(mapping.phys.addr).to_equal(0x2000)
expect(mapping.size).to_equal(4096)
expect(mapping.flags.present).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 42 |
| Active scenarios | 42 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
