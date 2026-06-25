# Physical Memory Manager Specification

> Tests for the bitmap-based physical page frame allocator (PhysMemManager). Tests allocate/free logic using the PhysMemManager struct directly.

<!-- sdn-diagram:id=pmm_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pmm_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pmm_spec -> std
pmm_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pmm_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Physical Memory Manager Specification

Tests for the bitmap-based physical page frame allocator (PhysMemManager). Tests allocate/free logic using the PhysMemManager struct directly.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OS-004 |
| Category | Runtime |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/os/kernel/memory/pmm_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the bitmap-based physical page frame allocator (PhysMemManager).
Tests allocate/free logic using the PhysMemManager struct directly.

Note: The actual PMM uses mmio_read/write for bitmap access, which requires
real memory-mapped hardware. These tests validate the data structure logic
and type-level operations (PageFrame, PhysAddr conversions) rather than
the bitmap I/O operations that require bare-metal execution.

## Scenarios

### PhysMemManager

### construction

#### initializes with zero pages

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pmm = _make_pmm(0, 0, 0)
expect(pmm.total_pages).to_equal(0)
expect(pmm.free_pages).to_equal(0)
```

</details>

#### tracks total pages

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pmm = _make_pmm(0x100000, 1024, 1024)
expect(pmm.total_pages).to_equal(1024)
```

</details>

#### tracks free pages

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pmm = _make_pmm(0x100000, 1024, 512)
expect(pmm.free_pages).to_equal(512)
```

</details>

#### stores bitmap address

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pmm = _make_pmm(0xDEAD0000, 256, 256)
expect(pmm.bitmap_addr).to_equal(0xDEAD0000)
```

</details>

#### initializes last_alloc_index to zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pmm = _make_pmm(0x100000, 1024, 1024)
expect(pmm.last_alloc_index).to_equal(0)
```

</details>

### memory queries

#### total_memory returns total_pages * 4096

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pmm = _make_pmm(0x100000, 256, 256)
expect(pmm.total_memory()).to_equal(256 * 4096)
```

</details>

#### free_memory returns free_pages * 4096

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pmm = _make_pmm(0x100000, 256, 128)
expect(pmm.free_memory()).to_equal(128 * 4096)
```

</details>

#### used_pages returns total - free

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pmm = _make_pmm(0x100000, 1000, 600)
expect(pmm.used_pages()).to_equal(400)
```

</details>

#### total_memory for zero pages is zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pmm = _make_pmm(0, 0, 0)
expect(pmm.total_memory()).to_equal(0)
```

</details>

### PageFrame allocation types

### PageFrame construction

#### creates a frame with valid pfn

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = PageFrame(pfn: 0)
expect(frame.pfn).to_equal(0)
```

</details>

#### pfn maps to correct physical address

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = PageFrame(pfn: 10)
val addr = frame.to_phys_addr()
expect(addr.addr).to_equal(10 * 4096)
```

</details>

### PageFrame round-trip

#### alloc index 0 maps to pfn 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = PageFrame(pfn: 0)
val addr = frame.to_phys_addr()
expect(addr.addr).to_equal(0)
val back = PageFrame.from_phys_addr(addr)
expect(back.pfn).to_equal(0)
```

</details>

#### alloc index 1023 maps to address 4190208

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = PageFrame(pfn: 1023)
val addr = frame.to_phys_addr()
expect(addr.addr).to_equal(1023 * 4096)
```

</details>

### simulated alloc/free state tracking

#### decrementing free_pages simulates allocation

1. var pmm =  make pmm
   - Expected: pmm.free_pages equals `99`
   - Expected: pmm.used_pages() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pmm = _make_pmm(0x100000, 100, 100)
# Simulate allocating a page
pmm.free_pages = pmm.free_pages - 1
expect(pmm.free_pages).to_equal(99)
expect(pmm.used_pages()).to_equal(1)
```

</details>

#### incrementing free_pages simulates freeing

1. var pmm =  make pmm
   - Expected: pmm.free_pages equals `51`
   - Expected: pmm.used_pages() equals `49`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pmm = _make_pmm(0x100000, 100, 50)
# Simulate freeing a page
pmm.free_pages = pmm.free_pages + 1
expect(pmm.free_pages).to_equal(51)
expect(pmm.used_pages()).to_equal(49)
```

</details>

#### cannot allocate when free_pages is zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pmm = _make_pmm(0x100000, 100, 0)
val can_alloc = pmm.free_pages > 0
expect(can_alloc).to_equal(false)
```

</details>

#### free then re-alloc restores count

1. var pmm =  make pmm
   - Expected: pmm.free_pages equals `100`
   - Expected: pmm.free_pages equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pmm = _make_pmm(0x100000, 100, 99)
# Free one page
pmm.free_pages = pmm.free_pages + 1
expect(pmm.free_pages).to_equal(100)
# Allocate again
pmm.free_pages = pmm.free_pages - 1
expect(pmm.free_pages).to_equal(99)
```

</details>

#### next-fit hint advances on allocation

1. var pmm =  make pmm
   - Expected: pmm.last_alloc_index equals `1`
   - Expected: pmm.last_alloc_index equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pmm = _make_pmm(0x100000, 100, 100)
# Simulate allocation at index 0, hint moves to 1
pmm.last_alloc_index = 1
expect(pmm.last_alloc_index).to_equal(1)
# Simulate allocation at index 1, hint moves to 2
pmm.last_alloc_index = 2
expect(pmm.last_alloc_index).to_equal(2)
```

</details>

#### next-fit hint wraps around

1. var pmm =  make pmm
2. pmm last alloc index =
   - Expected: pmm.last_alloc_index equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pmm = _make_pmm(0x100000, 100, 100)
pmm.last_alloc_index = 99
# Next alloc wraps to 0
pmm.last_alloc_index = (pmm.last_alloc_index + 1) % pmm.total_pages
expect(pmm.last_alloc_index).to_equal(0)
```

</details>

### PMM constants

#### PAGE_SIZE is 4096

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(4096).to_equal(4096)
```

</details>

#### MAX_PHYS_PAGES covers 4GB

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 4GB / 4KB = 1,048,576 pages
expect(1048576).to_equal(1048576)
```

</details>

#### BITMAP_SIZE_BYTES is MAX_PHYS_PAGES / 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(131072).to_equal(1048576 / 8)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
