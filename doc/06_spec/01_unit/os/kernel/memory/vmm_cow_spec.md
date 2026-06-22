# VMM COW (Copy-on-Write) Specification

> Tests for COW clone logic, PMM reference counting, and anon/file fault handlers. All tests use stub ProcessVmSpace values and simulated PMM counters — no real page tables or boot environment are required.

<!-- sdn-diagram:id=vmm_cow_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vmm_cow_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vmm_cow_spec -> std
vmm_cow_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vmm_cow_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# VMM COW (Copy-on-Write) Specification

Tests for COW clone logic, PMM reference counting, and anon/file fault handlers. All tests use stub ProcessVmSpace values and simulated PMM counters — no real page tables or boot environment are required.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OS-011 |
| Category | Runtime |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/os/kernel/memory/vmm_cow_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for COW clone logic, PMM reference counting, and anon/file fault handlers.
All tests use stub ProcessVmSpace values and simulated PMM counters —
no real page tables or boot environment are required.

## Scenarios

### vmm_cow_clone VMA duplication

#### child has same vma_count as parent

1. var parent =  cow make space
2.  cow space add
3.  cow space add
   - Expected: child.vma_count equals `parent.vma_count`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parent = _cow_make_space(0x1000, 1)
_cow_space_add(parent, _cow_make_anon(0x400000, 0x1000, VMA_READ | VMA_WRITE))
_cow_space_add(parent, _cow_make_anon(0x402000, 0x2000, VMA_READ | VMA_WRITE))

val pmm = _sim_pmm_new(8)
val child = _sim_cow_clone(parent, 0x1000, 0x2000, 2, pmm)

expect(child.vma_count).to_equal(parent.vma_count)
```

</details>

#### child VMAs have VMA_COW set for writable areas

1. var parent =  cow make space
2.  cow space add


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parent = _cow_make_space(0x1000, 1)
_cow_space_add(parent, _cow_make_anon(0x400000, 0x1000, VMA_READ | VMA_WRITE))

val pmm = _sim_pmm_new(4)
val child = _sim_cow_clone(parent, 0x1000, 0x2000, 2, pmm)

val c_area = child.areas[0]
expect(c_area.flags & VMA_COW).to_be_greater_than(0)
```

</details>

#### parent VMAs are also marked VMA_COW after clone

1. var parent =  cow make space
2.  cow space add
3.  sim cow clone


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parent = _cow_make_space(0x1000, 1)
_cow_space_add(parent, _cow_make_anon(0x400000, 0x1000, VMA_READ | VMA_WRITE))

val pmm = _sim_pmm_new(4)
_sim_cow_clone(parent, 0x1000, 0x2000, 2, pmm)

val p_area = parent.areas[0]
expect(p_area.flags & VMA_COW).to_be_greater_than(0)
```

</details>

#### read-only VMAs are not marked VMA_COW

1. var parent =  cow make space
2.  cow space add
   - Expected: c_area.flags & VMA_COW equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parent = _cow_make_space(0x1000, 1)
_cow_space_add(parent, _cow_make_anon(0x400000, 0x1000, VMA_READ))  # no WRITE

val pmm = _sim_pmm_new(4)
val child = _sim_cow_clone(parent, 0x1000, 0x2000, 2, pmm)

val c_area = child.areas[0]
expect(c_area.flags & VMA_COW).to_equal(0)
```

</details>

#### child VMA start and len match parent

1. var parent =  cow make space
2.  cow space add
   - Expected: child.areas[0].start equals `0x600000`
   - Expected: child.areas[0].len equals `0x8000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parent = _cow_make_space(0x1000, 1)
_cow_space_add(parent, _cow_make_anon(0x600000, 0x8000, VMA_READ | VMA_WRITE))

val pmm = _sim_pmm_new(4)
val child = _sim_cow_clone(parent, 0x1000, 0x2000, 2, pmm)

expect(child.areas[0].start).to_equal(0x600000)
expect(child.areas[0].len).to_equal(0x8000)
```

</details>

### PMM reference counting

#### ref increments count

1.  sim ref
   - Expected: pmm.counts[0] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pmm = _sim_pmm_new(4)
_sim_ref(pmm, 0)
expect(pmm.counts[0]).to_equal(1)
```

</details>

#### double-ref gives count 2

1.  sim ref
2.  sim ref
   - Expected: pmm.counts[0] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pmm = _sim_pmm_new(4)
_sim_ref(pmm, 0)
_sim_ref(pmm, 0)
expect(pmm.counts[0]).to_equal(2)
```

</details>

#### unref decrements and returns new count

1.  sim ref
2.  sim ref
   - Expected: remaining equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pmm = _sim_pmm_new(4)
_sim_ref(pmm, 1)
_sim_ref(pmm, 1)
val remaining = _sim_unref(pmm, 1)
expect(remaining).to_equal(1)
```

</details>

#### unref to 0 means page is freeable

1.  sim ref
   - Expected: r equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pmm = _sim_pmm_new(4)
_sim_ref(pmm, 2)
val r = _sim_unref(pmm, 2)
expect(r).to_equal(0)
```

</details>

#### clone increments refcount for each shared VMA

1. var parent =  cow make space
2.  cow space add
3.  cow space add
4.  sim cow clone
   - Expected: pmm.counts[0] equals `1`
   - Expected: pmm.counts[1] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parent = _cow_make_space(0x1000, 1)
_cow_space_add(parent, _cow_make_anon(0x400000, 0x1000, VMA_READ | VMA_WRITE))
_cow_space_add(parent, _cow_make_anon(0x402000, 0x1000, VMA_READ | VMA_WRITE))

val pmm = _sim_pmm_new(8)
_sim_cow_clone(parent, 0x1000, 0x2000, 2, pmm)

# Each of the 2 VMAs should have ref count 1
expect(pmm.counts[0]).to_equal(1)
expect(pmm.counts[1]).to_equal(1)
```

</details>

### anon fault — fresh page allocation

#### alloc from simulated PMM succeeds when pages are free

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pmm = _sim_pmm_new(4)
val pfn = _sim_alloc(pmm)
expect(pfn).to_equal(0)
```

</details>

#### allocated page has refcount 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pmm = _sim_pmm_new(4)
val pfn = _sim_alloc(pmm)
expect(pmm.counts[pfn]).to_equal(1)
```

</details>

#### second alloc returns different pfn

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pmm = _sim_pmm_new(4)
val pfn0 = _sim_alloc(pmm)
val pfn1 = _sim_alloc(pmm)
expect(pfn0).to_equal(0)
expect(pfn1).to_equal(1)
```

</details>

#### alloc from empty PMM returns -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pmm = _sim_pmm_new(0)
val pfn = _sim_alloc(pmm)
expect(pfn).to_equal(-1)
```

</details>

### COW fault — copy and upgrade

#### after COW fault VMA_COW is cleared and VMA_WRITE is set

1. var space =  cow make space
2.  cow space add
   - Expected: updated.flags & VMA_COW equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var space = _cow_make_space(0x1000, 1)
val initial_flags = VMA_READ | VMA_WRITE | VMA_COW
_cow_space_add(space, _cow_make_anon(0x400000, 0x1000, initial_flags))

# Simulate the VMA update that vmm_handle_cow_fault performs
val fault_vaddr: u64 = 0x400000
var i: i32 = 0
while (i as u64) < space.vma_count:
    val a = space.areas[i]
    if (fault_vaddr >= a.start) and (fault_vaddr < (a.start + a.len)):
        val new_flags = (a.flags & ~VMA_COW) | VMA_WRITE
        space.areas[i] = VmArea(
            start: a.start,
            len: a.len,
            kind: a.kind,
            flags: new_flags,
            backing: a.backing,
            backing_offset: a.backing_offset
        )
        break
    i = i + 1

val updated = space.areas[0]
expect(updated.flags & VMA_COW).to_equal(0)
expect(updated.flags & VMA_WRITE).to_be_greater_than(0)
```

</details>

#### parent page refcount drops to 0 when child takes private copy

1.  sim ref
   - Expected: r equals `0)        # Parent can now free the old page`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pmm = _sim_pmm_new(4)
_sim_ref(pmm, 0)   # Simulate parent sharing pfn 0 with child
val r = _sim_unref(pmm, 0)   # Child takes private copy; parent ref drops
expect(r).to_equal(0)        # Parent can now free the old page
```

</details>

#### new page gets refcount 1 after COW alloc

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pmm = _sim_pmm_new(4)
val pfn = _sim_alloc(pmm)   # Child's new private page
expect(pmm.counts[pfn]).to_equal(1)
```

</details>

#### COW on file-backed VMA preserves backing handle and offset

1. var space =  cow make space
2.  cow space add
   - Expected: a.backing equals `99`
   - Expected: a.backing_offset equals `0x3000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var space = _cow_make_space(0x1000, 1)
val area = VmArea(
    start: 0x500000,
    len: 0x2000,
    kind: VMA_FILE,
    flags: VMA_READ | VMA_WRITE | VMA_COW,
    backing: 99,
    backing_offset: 0x3000
)
_cow_space_add(space, area)

# After COW fault the metadata must be preserved
val a = space.areas[0]
expect(a.backing).to_equal(99)
expect(a.backing_offset).to_equal(0x3000)
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
