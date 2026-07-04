# Segment Mapper Specification

> _PT_LOAD → user address space mapper.""_

<!-- sdn-diagram:id=segment_mapper_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=segment_mapper_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

segment_mapper_spec -> std
segment_mapper_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=segment_mapper_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Segment Mapper Specification

## Scenarios

### segment_mapper
_PT_LOAD → user address space mapper.""_

### highest_loaded_address

#### returns 0 for an empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val segs: [UserLoadSegment] = []
expect(highest_loaded_address(segs)).to_equal(0)
```

</details>

#### returns page-aligned upper bound for a single segment

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# va=0x1000, memsz=0x2000 ⇒ end = 0x3000 (already page-aligned).
val seg = UserLoadSegment(
    virt_addr: 0x1000,
    mem_size: 0x2000,
    file_size: 0x2000,
    flags: 4,           # PF_R
    align: 0x1000,
    data: []
)
val segs = [seg]
expect(highest_loaded_address(segs)).to_equal(0x3000)
```

</details>

#### rounds an unaligned upper bound up to the next page

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seg = UserLoadSegment(
    virt_addr: 0x1000,
    mem_size: 0x1234,
    file_size: 0x1000,
    flags: 4,
    align: 0x1000,
    data: []
)
val segs = [seg]
# 0x1000 + 0x1234 = 0x2234 → rounds up to 0x3000
expect(highest_loaded_address(segs)).to_equal(0x3000)
```

</details>

#### takes the max across multiple segments

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = UserLoadSegment(
    virt_addr: 0x1000, mem_size: 0x1000, file_size: 0x1000,
    flags: 4, align: 0x1000, data: []
)
val b = UserLoadSegment(
    virt_addr: 0x4000, mem_size: 0x500, file_size: 0x500,
    flags: 6, align: 0x1000, data: []
)
val segs = [a, b]
# b ends at 0x4500 → rounds to 0x5000
expect(highest_loaded_address(segs)).to_equal(0x5000)
```

</details>

### map_segment validation

#### rejects a segment with file_size > mem_size

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad = UserLoadSegment(
    virt_addr: 0x1000,
    mem_size: 0x100,
    file_size: 0x200,   # larger than mem_size
    flags: 4,
    align: 0x1000,
    data: []
)
val as_handle = AddressSpace(phys_root: 0, id: 0)
val bytes: [u8] = []
val r = map_segment(as_handle, bad, bytes)
match r:
    case Err(msg):
        expect(msg.contains("file_size")).to_equal(true)
    case Ok(_):
        expect("expected Err, got Ok").to_equal("")
```

</details>

### map_all no-op

#### returns Ok(0) on an empty segment list

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val as_handle = AddressSpace(phys_root: 0, id: 0)
val segs: [UserLoadSegment] = []
val bytes: [u8] = []
val r = map_all(as_handle, segs, bytes)
match r:
    case Ok(n):
        expect(n).to_equal(0)
    case Err(_):
        expect("expected Ok(0), got Err").to_equal("")
```

</details>

### map_stack validation

#### rejects a zero-sized stack

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val as_handle = AddressSpace(phys_root: 0, id: 0)
val r = map_stack(as_handle, 0x8000, 0, [])
match r:
    case Err(msg):
        expect(msg.contains("stack_size")).to_equal(true)
    case Ok(_):
        expect("expected Err, got Ok").to_equal("")
```

</details>

#### rejects an initial frame larger than the stack

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val as_handle = AddressSpace(phys_root: 0, id: 0)
val r = map_stack(as_handle, 0x8000, 2, [1u8, 2u8, 3u8])
match r:
    case Err(msg):
        expect(msg.contains("initial stack")).to_equal(true)
    case Ok(_):
        expect("expected Err, got Ok").to_equal("")
```

</details>

#### rejects stack ranges that underflow

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val as_handle = AddressSpace(phys_root: 0, id: 0)
val r = map_stack(as_handle, 0x1000, 0x2000, [])
match r:
    case Err(msg):
        expect(msg.contains("underflows")).to_equal(true)
    case Ok(_):
        expect("expected Err, got Ok").to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/loader/segment_mapper_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- segment_mapper
- highest_loaded_address
- map_segment validation
- map_all no-op
- map_stack validation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
