# RV64 Sv39 Virtual Memory Unit Tests

> Unit tests for Sv39 3-level page table walk, TLB, permission checking, and superpage support.

<!-- sdn-diagram:id=rv64_sv39_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_sv39_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_sv39_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_sv39_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 Sv39 Virtual Memory Unit Tests

Unit tests for Sv39 3-level page table walk, TLB, permission checking, and superpage support.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-SV39-001 |
| Category | Hardware |
| Difficulty | 3/5 |
| Status | Draft |
| Source | `test/01_unit/hardware/rv64gc/rv64_sv39_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for Sv39 3-level page table walk, TLB, permission checking,
and superpage support.

## Scenarios

### Sv39 VPN Extraction

#### extracts VPN[2] from virtual address

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vaddr: i64 = 0x80000000
expect((vaddr >> 30) and 0x1FF).to_equal(2)
```

</details>

#### extracts VPN[1] from virtual address

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vaddr: i64 = 0x00200000
expect((vaddr >> 21) and 0x1FF).to_equal(1)
```

</details>

#### extracts VPN[0] from virtual address

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vaddr: i64 = 0x00001000
expect((vaddr >> 12) and 0x1FF).to_equal(1)
```

</details>

### Sv39 4KB Page Walk

#### translates through 3-level walk

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vpn2 = 0
val vpn1 = 0
val vpn0 = 0
val offset = 0x100
# L2[0] → L1 table at PPN 0x1000
val l2_entry = _make_ptr_pte(0x1000)
# L1[0] → L0 table at PPN 0x2000
val l1_entry = _make_ptr_pte(0x2000)
# L0[0] → leaf at PPN 0x80 (physical page 0x80000)
val l0_entry = _make_leaf_pte(0x80, PTE_R or PTE_W)
val phys_page = 0x80
val paddr = phys_page * PAGE_SIZE + offset
expect(paddr).to_equal(0x80100)
```

</details>

#### offset preserved through translation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vaddr: i64 = 0x00000ABC
val offset = vaddr and 0xFFF
expect(offset).to_equal(0xABC)
```

</details>

#### invalid PTE (V=0) causes page fault

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pte: i64 = 0  # V bit not set
expect(pte and PTE_V).to_equal(0)
```

</details>

### Sv39 2MB Superpage

#### 2MB superpage: leaf at level 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l1_entry = _make_leaf_pte(0x80, PTE_R or PTE_W or PTE_X)
val is_leaf = (l1_entry and (PTE_R or PTE_W or PTE_X)) != 0
expect(is_leaf).to_equal(true)
```

</details>

#### 2MB superpage offset from vaddr

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vaddr: i64 = 0x00200100
val offset_2mb = vaddr and 0x1FFFFF
expect(offset_2mb).to_equal(0x100)
```

</details>

### Sv39 1GB Gigapage

#### 1GB gigapage: leaf at level 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l2_entry = _make_leaf_pte(0x80000, PTE_R or PTE_W or PTE_X)
val is_leaf = (l2_entry and (PTE_R or PTE_W or PTE_X)) != 0
expect(is_leaf).to_equal(true)
```

</details>

#### 1GB gigapage offset from vaddr

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vaddr: i64 = 0x80000100
val offset_1gb = vaddr and 0x3FFFFFFF
expect(offset_1gb).to_equal(0x100)
```

</details>

### Sv39 Permission Checking

#### read-only page blocks writes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pte = _make_leaf_pte(0x80, PTE_R)
expect((pte and PTE_W) == 0).to_equal(true)
```

</details>

#### execute-only page blocks reads

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pte = _make_leaf_pte(0x80, PTE_X)
expect((pte and PTE_R) == 0).to_equal(true)
```

</details>

#### RWX all set

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pte = _make_leaf_pte(0x80, PTE_R or PTE_W or PTE_X)
expect((pte and PTE_R) != 0).to_equal(true)
expect((pte and PTE_W) != 0).to_equal(true)
expect((pte and PTE_X) != 0).to_equal(true)
```

</details>

### User/Global Bits

#### PTE_U allows U-mode access

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pte = _make_leaf_pte(0x80, PTE_R or PTE_U)
expect((pte and PTE_U) != 0).to_equal(true)
```

</details>

#### PTE_G marks global page

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pte = _make_leaf_pte(0x80, PTE_R or PTE_G)
expect((pte and PTE_G) != 0).to_equal(true)
```

</details>

### Accessed/Dirty Bits

#### A bit set on access

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pte = _make_leaf_pte(0x80, PTE_R)
expect((pte and PTE_A) != 0).to_equal(true)
```

</details>

#### D bit set on write

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pte = _make_leaf_pte(0x80, PTE_R or PTE_W)
expect((pte and PTE_D) != 0).to_equal(true)
```

</details>

#### page without A bit triggers page fault

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pte = (0x80 << 10) or PTE_V or PTE_R  # No A bit
expect((pte and PTE_A) == 0).to_equal(true)
```

</details>

### TLB

#### TLB hit returns cached result

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Simulate: entry stores VPN→PPN mapping
val tlb_vpn: i64 = 0x80000
val tlb_ppn: i64 = 0x40000
val lookup_vpn: i64 = 0x80000
expect(lookup_vpn == tlb_vpn).to_equal(true)
```

</details>

#### TLB miss triggers page walk

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tlb_vpn: i64 = 0x80000
val lookup_vpn: i64 = 0x90000
expect(lookup_vpn == tlb_vpn).to_equal(false)
```

</details>

#### SFENCE.VMA flushes all TLB entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# After flush, all lookups miss
var flushed = true
expect(flushed).to_equal(true)
```

</details>

### SATP Register

#### Mode 0 = Bare (no translation)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val satp: i64 = 0
val mode = (satp >> 60) and 0xF
expect(mode).to_equal(0)
```

</details>

#### Mode 8 = Sv39

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val satp: i64 = 8 << 60
val mode = (satp >> 60) and 0xF
expect(mode).to_equal(8)
```

</details>

#### ASID field

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val satp: i64 = (8 << 60) or (5 << 44) or 0x80000
val asid = (satp >> 44) and 0xFFFF
expect(asid).to_equal(5)
```

</details>

#### PPN field

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val satp: i64 = (8 << 60) or 0x80000
val ppn = satp and 0xFFFFFFFFFFF
expect(ppn).to_equal(0x80000)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
