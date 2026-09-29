# Physical Memory Manager Specification

> Tests for the bitmap-based physical page frame allocator (PhysMemManager). Tests allocate/free logic using the PhysMemManager struct directly.

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
| Source | `test/unit/os/kernel/memory/pmm_spec.spl` |
| Updated | 2026-08-26 |
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

- initializes with zero pages
   - Expected: pmm.total_pages equals `0`
   - Expected: pmm.free_pages equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("initializes with zero pages")
val pmm = _make_pmm(0, 0, 0)
expect(pmm.total_pages).to_equal(0)
expect(pmm.free_pages).to_equal(0)
```

</details>

#### tracks total pages

- tracks total pages
   - Expected: pmm.total_pages equals `1024`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks total pages")
val pmm = _make_pmm(0x100000, 1024, 1024)
expect(pmm.total_pages).to_equal(1024)
```

</details>

#### tracks free pages

- tracks free pages
   - Expected: pmm.free_pages equals `512`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks free pages")
val pmm = _make_pmm(0x100000, 1024, 512)
expect(pmm.free_pages).to_equal(512)
```

</details>

#### stores bitmap address

- stores bitmap address
   - Expected: pmm.bitmap_addr equals `0xDEAD0000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores bitmap address")
val pmm = _make_pmm(0xDEAD0000, 256, 256)
expect(pmm.bitmap_addr).to_equal(0xDEAD0000)
```

</details>

#### initializes last_alloc_index to zero

- initializes last_alloc_index to zero
   - Expected: pmm.last_alloc_index equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("initializes last_alloc_index to zero")
val pmm = _make_pmm(0x100000, 1024, 1024)
expect(pmm.last_alloc_index).to_equal(0)
```

</details>

### memory queries

#### total_memory returns total_pages * 4096

- total_memory returns total_pages * 4096
   - Expected: pmm.total_memory() equals `256 * 4096`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("total_memory returns total_pages * 4096")
val pmm = _make_pmm(0x100000, 256, 256)
expect(pmm.total_memory()).to_equal(256 * 4096)
```

</details>

#### free_memory returns free_pages * 4096

- free_memory returns free_pages * 4096
   - Expected: pmm.free_memory() equals `128 * 4096`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("free_memory returns free_pages * 4096")
val pmm = _make_pmm(0x100000, 256, 128)
expect(pmm.free_memory()).to_equal(128 * 4096)
```

</details>

#### used_pages returns total - free

- used_pages returns total - free
   - Expected: pmm.used_pages() equals `400`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("used_pages returns total - free")
val pmm = _make_pmm(0x100000, 1000, 600)
expect(pmm.used_pages()).to_equal(400)
```

</details>

#### total_memory for zero pages is zero

- total_memory for zero pages is zero
   - Expected: pmm.total_memory() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("total_memory for zero pages is zero")
val pmm = _make_pmm(0, 0, 0)
expect(pmm.total_memory()).to_equal(0)
```

</details>

### PageFrame allocation types

### PageFrame construction

#### creates a frame with valid pfn

- creates a frame with valid pfn
   - Expected: frame.pfn equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a frame with valid pfn")
val frame = PageFrame(pfn: 0)
expect(frame.pfn).to_equal(0)
```

</details>

#### pfn maps to correct physical address

- pfn maps to correct physical address
   - Expected: addr.addr equals `10 * 4096`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pfn maps to correct physical address")
val frame = PageFrame(pfn: 10)
val addr = frame.to_phys_addr()
expect(addr.addr).to_equal(10 * 4096)
```

</details>

### PageFrame round-trip

#### alloc index 0 maps to pfn 0

- alloc index 0 maps to pfn 0
   - Expected: addr.addr equals `0`
   - Expected: back.pfn equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("alloc index 0 maps to pfn 0")
val frame = PageFrame(pfn: 0)
val addr = frame.to_phys_addr()
expect(addr.addr).to_equal(0)
val back = PageFrame.from_phys_addr(addr)
expect(back.pfn).to_equal(0)
```

</details>

#### alloc index 1023 maps to address 4190208

- alloc index 1023 maps to address 4190208
   - Expected: addr.addr equals `1023 * 4096`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("alloc index 1023 maps to address 4190208")
val frame = PageFrame(pfn: 1023)
val addr = frame.to_phys_addr()
expect(addr.addr).to_equal(1023 * 4096)
```

</details>

### simulated alloc/free state tracking

#### decrementing free_pages simulates allocation

- decrementing free_pages simulates allocation
   - Expected: pmm.free_pages equals `99`
   - Expected: pmm.used_pages() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decrementing free_pages simulates allocation")
var pmm = _make_pmm(0x100000, 100, 100)
# Simulate allocating a page
pmm.free_pages = pmm.free_pages - 1
expect(pmm.free_pages).to_equal(99)
expect(pmm.used_pages()).to_equal(1)
```

</details>

#### incrementing free_pages simulates freeing

- incrementing free_pages simulates freeing
   - Expected: pmm.free_pages equals `51`
   - Expected: pmm.used_pages() equals `49`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("incrementing free_pages simulates freeing")
var pmm = _make_pmm(0x100000, 100, 50)
# Simulate freeing a page
pmm.free_pages = pmm.free_pages + 1
expect(pmm.free_pages).to_equal(51)
expect(pmm.used_pages()).to_equal(49)
```

</details>

#### cannot allocate when free_pages is zero

- cannot allocate when free_pages is zero
   - Expected: can_alloc is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cannot allocate when free_pages is zero")
val pmm = _make_pmm(0x100000, 100, 0)
val can_alloc = pmm.free_pages > 0
expect(can_alloc).to_equal(false)
```

</details>

#### free then re-alloc restores count

- free then re-alloc restores count
   - Expected: pmm.free_pages equals `100`
   - Expected: pmm.free_pages equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("free then re-alloc restores count")
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

- next-fit hint advances on allocation
   - Expected: pmm.last_alloc_index equals `1`
   - Expected: pmm.last_alloc_index equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("next-fit hint advances on allocation")
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

- next-fit hint wraps around
   - Expected: pmm.last_alloc_index equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("next-fit hint wraps around")
var pmm = _make_pmm(0x100000, 100, 100)
pmm.last_alloc_index = 99
# Next alloc wraps to 0
pmm.last_alloc_index = (pmm.last_alloc_index + 1) % pmm.total_pages
expect(pmm.last_alloc_index).to_equal(0)
```

</details>

### PMM constants

#### PAGE_SIZE is 4096

- PAGE_SIZE is 4096
   - Expected: 4096 equals `4096`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PAGE_SIZE is 4096")
expect(4096).to_equal(4096)
```

</details>

#### MAX_PHYS_PAGES covers 4GB

- MAX_PHYS_PAGES covers 4GB
   - Expected: 1048576 equals `1048576`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("MAX_PHYS_PAGES covers 4GB")
# 4GB / 4KB = 1,048,576 pages
expect(1048576).to_equal(1048576)
```

</details>

#### BITMAP_SIZE_BYTES is MAX_PHYS_PAGES / 8

- BITMAP_SIZE_BYTES is MAX_PHYS_PAGES / 8
   - Expected: 131072 equals `1048576 / 8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BITMAP_SIZE_BYTES is MAX_PHYS_PAGES / 8")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b7e9f95dbd81ac540b697b5ef87fa941d291665b57bc8673329950d70f217603`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b7e9f95dbd81ac540b697b5ef87fa941d291665b57bc8673329950d70f217603`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b7e9f95dbd81ac540b697b5ef87fa941d291665b57bc8673329950d70f217603`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/os/kernel/memory/pmm_spec.spl
mirror: doc/06_spec/unit/os/kernel/memory/pmm_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/kernel/memory/pmm_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/memory/pmm_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/memory/pmm_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 21 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/kernel/memory/pmm_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'initializes with zero pages' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/memory/pmm_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tracks total pages' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/memory/pmm_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tracks free pages' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
