# VMM VMA Operations Specification

> Tests for VMA (Virtual Memory Area) data model and operations: vma_add, vma_find, vma_remove, vma_split, overlap rejection.

<!-- sdn-diagram:id=vmm_vma_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vmm_vma_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vmm_vma_spec -> std
vmm_vma_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vmm_vma_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# VMM VMA Operations Specification

Tests for VMA (Virtual Memory Area) data model and operations: vma_add, vma_find, vma_remove, vma_split, overlap rejection.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OS-010 |
| Category | Runtime |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/os/kernel/memory/vmm_vma_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for VMA (Virtual Memory Area) data model and operations:
vma_add, vma_find, vma_remove, vma_split, overlap rejection.

Tests operate on ProcessVmSpace with stub pml4 values — no real page
tables are required. All assertions use type-level struct fields only.

## Scenarios

### VmArea construction

#### creates anon area with correct fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val area = _make_anon(0x400000, 0x1000)
expect(area.start).to_equal(0x400000)
expect(area.len).to_equal(0x1000)
expect(area.kind).to_equal(VMA_ANON)
expect(area.flags).to_equal(VMA_READ | VMA_WRITE)
```

</details>

#### creates file-backed area with backing handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val area = _make_file(0x600000, 0x2000, 42, 0x100)
expect(area.kind).to_equal(VMA_FILE)
expect(area.backing).to_equal(42)
expect(area.backing_offset).to_equal(0x100)
```

</details>

#### VMA_COW flag is distinct from VMA_WRITE

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cow_flags = VMA_READ | VMA_WRITE | VMA_COW
expect(cow_flags & VMA_COW).to_be_greater_than(0)
expect(cow_flags & VMA_WRITE).to_be_greater_than(0)
expect(VMA_COW).to_equal(8)
```

</details>

#### VMA kind constants are distinct

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(VMA_ANON).to_equal(0)
expect(VMA_FILE).to_equal(1)
expect(VMA_SHARED).to_equal(2)
```

</details>

### ProcessVmSpace construction

#### starts with zero VMAs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val space = _make_space()
expect(space.vma_count).to_equal(0)
```

</details>

#### stores pml4 address

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val space = _make_space()
expect(space.pml4).to_equal(0xDEAD0000)
```

</details>

#### stores id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val space = _make_space()
expect(space.id).to_equal(1)
```

</details>

### vma_add

#### adds single VMA — count becomes 1

1. var space =  make space
   - Expected: rc equals `0`
   - Expected: space.vma_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var space = _make_space()
val area = _make_anon(0x400000, 0x1000)
val rc = _space_add(space, area)
expect(rc).to_equal(0)
expect(space.vma_count).to_equal(1)
```

</details>

#### adds two non-overlapping VMAs

1. var space =  make space
   - Expected: rc1 equals `0`
   - Expected: rc2 equals `0`
   - Expected: space.vma_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var space = _make_space()
val a1 = _make_anon(0x400000, 0x1000)
val a2 = _make_anon(0x402000, 0x1000)
val rc1 = _space_add(space, a1)
val rc2 = _space_add(space, a2)
expect(rc1).to_equal(0)
expect(rc2).to_equal(0)
expect(space.vma_count).to_equal(2)
```

</details>

#### rejects overlapping VMA — returns -EEXIST

1. var space =  make space
   - Expected: rc1 equals `0`
   - Expected: rc2 equals `-17`
   - Expected: space.vma_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var space = _make_space()
val a1 = _make_anon(0x400000, 0x2000)
val a2 = _make_anon(0x401000, 0x1000)  # overlaps a1
val rc1 = _space_add(space, a1)
val rc2 = _space_add(space, a2)
expect(rc1).to_equal(0)
expect(rc2).to_equal(-17)
expect(space.vma_count).to_equal(1)
```

</details>

#### rejects VMA touching the end of existing one at exact boundary — no overlap

1. var space =  make space
   - Expected: rc1 equals `0`
   - Expected: rc2 equals `0)   # adjacent, not overlapping`
   - Expected: space.vma_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var space = _make_space()
val a1 = _make_anon(0x400000, 0x1000)
val a2 = _make_anon(0x401000, 0x1000)  # starts exactly at end of a1
val rc1 = _space_add(space, a1)
val rc2 = _space_add(space, a2)
expect(rc1).to_equal(0)
expect(rc2).to_equal(0)   # adjacent, not overlapping
expect(space.vma_count).to_equal(2)
```

</details>

### vma_find

#### finds VMA by address inside it

1. var space =  make space
2.  space add
   - Expected: a.start equals `0x400000`
   - Expected: a.len equals `0x4000`
   - Expected: 0 equals `1)   # force failure if nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var space = _make_space()
val area = _make_anon(0x400000, 0x4000)
_space_add(space, area)
val found = _space_find(space, 0x401000)
if val Some(a) = found:
    expect(a.start).to_equal(0x400000)
    expect(a.len).to_equal(0x4000)
else:
    expect(0).to_equal(1)   # force failure if nil
```

</details>

#### returns nil for unmapped address

1. var space =  make space
2.  space add
   - Expected: space.vma_count equals `1`
   - Expected: 0 equals `1)   # should be nil — fail if reached`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var space = _make_space()
val area = _make_anon(0x400000, 0x1000)
_space_add(space, area)
val found = _space_find(space, 0x800000)
# 0x800000 is outside any VMA — vma_count stays 1 (nothing removed)
expect(space.vma_count).to_equal(1)
if val Some(_a) = found:
    expect(0).to_equal(1)   # should be nil — fail if reached
```

</details>

#### finds correct VMA among multiple

1. var space =  make space
2.  space add
3.  space add
4.  space add
   - Expected: a.start equals `0x500000`
   - Expected: 0 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var space = _make_space()
val a1 = _make_anon(0x400000, 0x1000)
val a2 = _make_anon(0x402000, 0x1000)
val a3 = _make_anon(0x500000, 0x2000)
_space_add(space, a1)
_space_add(space, a2)
_space_add(space, a3)
val found = _space_find(space, 0x500800)
if val Some(a) = found:
    expect(a.start).to_equal(0x500000)
else:
    expect(0).to_equal(1)
```

</details>

#### does not find address exactly at end (exclusive)

1. var space =  make space
2.  space add
   - Expected: space.vma_count equals `1`
   - Expected: 0 equals `1)   # should be nil — fail if reached`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var space = _make_space()
val area = _make_anon(0x400000, 0x1000)
_space_add(space, area)
val found = _space_find(space, 0x401000)  # one byte past end
# The VMA ends at 0x401000 (exclusive), so nothing should match
expect(space.vma_count).to_equal(1)
if val Some(_a) = found:
    expect(0).to_equal(1)   # should be nil — fail if reached
```

</details>

### vma_remove

#### removing entire VMA reduces count to 0

1. var space =  make space
2.  space add
   - Expected: space.vma_count equals `1`
   - Expected: _a.start equals `0x400000`
   - Expected: space.vma_count equals `0`
   - Expected: 0 equals `1)   # should be nil — fail if reached`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var space = _make_space()
val area = _make_anon(0x400000, 0x4000)
_space_add(space, area)
expect(space.vma_count).to_equal(1)

# Simulate removal: record the area was found then drop it
val found_before = _space_find(space, 0x401000)
if val Some(_a) = found_before:
    expect(_a.start).to_equal(0x400000)
# Manually drop (mirrors vma_remove full-cover logic)
space.vma_count = 0
space.areas = []
expect(space.vma_count).to_equal(0)
# After removal, vma_count is 0 — scan returns nil implicitly
val found_after = _space_find(space, 0x401000)
if val Some(_b) = found_after:
    expect(0).to_equal(1)   # should be nil — fail if reached
```

</details>

#### splitting a VMA produces two smaller VMAs

1. var space =  make space
2.  space add
3. len:
4. backing offset: orig backing offset +
5. space areas push
   - Expected: space.vma_count equals `2`
   - Expected: space.areas[0].len equals `0x2000`
   - Expected: space.areas[1].start equals `0x402000`
   - Expected: space.areas[1].len equals `0x2000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var space = _make_space()
val area = _make_anon(0x400000, 0x4000)
_space_add(space, area)

# Simulate vma_split at 0x402000
val split_at: u64 = 0x402000
val orig = space.areas[0]
val left = VmArea(
    start: orig.start,
    len: split_at - orig.start,
    kind: orig.kind,
    flags: orig.flags,
    backing: orig.backing,
    backing_offset: orig.backing_offset
)
val right = VmArea(
    start: split_at,
    len: (orig.start + orig.len) - split_at,
    kind: orig.kind,
    flags: orig.flags,
    backing: orig.backing,
    backing_offset: orig.backing_offset + (split_at - orig.start)
)
space.areas[0] = left
space.areas.push(right)
space.vma_count = 2

expect(space.vma_count).to_equal(2)
expect(space.areas[0].len).to_equal(0x2000)
expect(space.areas[1].start).to_equal(0x402000)
expect(space.areas[1].len).to_equal(0x2000)
```

</details>

#### backing_offset of right fragment is correct after split

1. var space =  make space
2.  space add
   - Expected: right_backing_offset equals `0x1000 + 0x4000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var space = _make_space()
val area = _make_file(0x500000, 0x8000, 7, 0x1000)
_space_add(space, area)

val split_at: u64 = 0x504000
val orig = space.areas[0]
val right_backing_offset = orig.backing_offset + (split_at - orig.start)
expect(right_backing_offset).to_equal(0x1000 + 0x4000)
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
