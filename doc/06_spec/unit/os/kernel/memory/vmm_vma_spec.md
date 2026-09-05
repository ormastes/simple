# VMM VMA Operations Specification

> Tests for VMA (Virtual Memory Area) data model and operations: vma_add, vma_find, vma_remove, vma_split, overlap rejection.

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
| Source | `test/unit/os/kernel/memory/vmm_vma_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for VMA (Virtual Memory Area) data model and operations:
vma_add, vma_find, vma_remove, vma_split, overlap rejection.

Tests operate on ProcessVmSpace with stub pml4 values — no real page
tables are required. All assertions use type-level struct fields only.

## Scenarios

### VmArea construction

#### creates anon area with correct fields

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates anon area with correct fields
   - Expected: area.start equals `0x400000`
   - Expected: area.len equals `0x1000`
   - Expected: area.kind equals `VMA_ANON`
   - Expected: area.flags equals `VMA_READ | VMA_WRITE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates anon area with correct fields")
val area = _make_anon(0x400000, 0x1000)
expect(area.start).to_equal(0x400000)
expect(area.len).to_equal(0x1000)
expect(area.kind).to_equal(VMA_ANON)
expect(area.flags).to_equal(VMA_READ | VMA_WRITE)
```

</details>

#### creates file-backed area with backing handle

- creates file-backed area with backing handle
   - Expected: area.kind equals `VMA_FILE`
   - Expected: area.backing equals `42`
   - Expected: area.backing_offset equals `0x100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates file-backed area with backing handle")
val area = _make_file(0x600000, 0x2000, 42, 0x100)
expect(area.kind).to_equal(VMA_FILE)
expect(area.backing).to_equal(42)
expect(area.backing_offset).to_equal(0x100)
```

</details>

#### VMA_COW flag is distinct from VMA_WRITE

- VMA_COW flag is distinct from VMA_WRITE
   - Expected: VMA_COW equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VMA_COW flag is distinct from VMA_WRITE")
val cow_flags = VMA_READ | VMA_WRITE | VMA_COW
expect(cow_flags & VMA_COW).to_be_greater_than(0)
expect(cow_flags & VMA_WRITE).to_be_greater_than(0)
expect(VMA_COW).to_equal(8)
```

</details>

#### VMA kind constants are distinct

- VMA kind constants are distinct
   - Expected: VMA_ANON equals `0`
   - Expected: VMA_FILE equals `1`
   - Expected: VMA_SHARED equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VMA kind constants are distinct")
expect(VMA_ANON).to_equal(0)
expect(VMA_FILE).to_equal(1)
expect(VMA_SHARED).to_equal(2)
```

</details>

### ProcessVmSpace construction

#### starts with zero VMAs

- starts with zero VMAs
   - Expected: space.vma_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with zero VMAs")
val space = _make_space()
expect(space.vma_count).to_equal(0)
```

</details>

#### stores pml4 address

- stores pml4 address
   - Expected: space.pml4 equals `0xDEAD0000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores pml4 address")
val space = _make_space()
expect(space.pml4).to_equal(0xDEAD0000)
```

</details>

#### stores id

- stores id
   - Expected: space.id equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores id")
val space = _make_space()
expect(space.id).to_equal(1)
```

</details>

### vma_add

#### adds single VMA — count becomes 1

- adds single VMA — count becomes 1
   - Expected: result.code equals `0`
   - Expected: space.vma_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds single VMA — count becomes 1")
var space = _make_space()
val area = _make_anon(0x400000, 0x1000)
val result = vma_add(space, area)
space = result.space
expect(result.code).to_equal(0)
expect(space.vma_count).to_equal(1)
```

</details>

#### adds two non-overlapping VMAs

- adds two non-overlapping VMAs
   - Expected: r1.code equals `0`
   - Expected: r2.code equals `0`
   - Expected: space.vma_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds two non-overlapping VMAs")
var space = _make_space()
val a1 = _make_anon(0x400000, 0x1000)
val a2 = _make_anon(0x402000, 0x1000)
val r1 = vma_add(space, a1)
space = r1.space
val r2 = vma_add(space, a2)
space = r2.space
expect(r1.code).to_equal(0)
expect(r2.code).to_equal(0)
expect(space.vma_count).to_equal(2)
```

</details>

#### rejects overlapping VMA — returns -EEXIST

- rejects overlapping VMA — returns -EEXIST
   - Expected: r1.code equals `0`
   - Expected: r2.code equals `-17`
   - Expected: space.vma_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects overlapping VMA — returns -EEXIST")
var space = _make_space()
val a1 = _make_anon(0x400000, 0x2000)
val a2 = _make_anon(0x401000, 0x1000)  # overlaps a1
val r1 = vma_add(space, a1)
space = r1.space
val r2 = vma_add(space, a2)
space = r2.space
expect(r1.code).to_equal(0)
expect(r2.code).to_equal(-17)
expect(space.vma_count).to_equal(1)
```

</details>

#### rejects VMA touching the end of existing one at exact boundary — no overlap

- rejects VMA touching the end of existing one at exact boundary — no overlap
   - Expected: r1.code equals `0`
   - Expected: r2.code equals `0)   # adjacent, not overlapping`
   - Expected: space.vma_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects VMA touching the end of existing one at exact boundary — no overlap")
var space = _make_space()
val a1 = _make_anon(0x400000, 0x1000)
val a2 = _make_anon(0x401000, 0x1000)  # starts exactly at end of a1
val r1 = vma_add(space, a1)
space = r1.space
val r2 = vma_add(space, a2)
space = r2.space
expect(r1.code).to_equal(0)
expect(r2.code).to_equal(0)   # adjacent, not overlapping
expect(space.vma_count).to_equal(2)
```

</details>

### vma_find

#### finds VMA by address inside it

- finds VMA by address inside it
   - Expected: a.start equals `0x400000`
   - Expected: a.len equals `0x4000`
   - Expected: 0 equals `1)   # force failure if nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds VMA by address inside it")
var space = _make_space()
val area = _make_anon(0x400000, 0x4000)
space = vma_add(space, area).space
val found = vma_find(space, 0x401000)
if val Some(a) = found:
    expect(a.start).to_equal(0x400000)
    expect(a.len).to_equal(0x4000)
else:
    expect(0).to_equal(1)   # force failure if nil
```

</details>

#### returns nil for unmapped address

- returns nil for unmapped address
   - Expected: space.vma_count equals `1`
   - Expected: 0 equals `1)   # should be nil — fail if reached`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for unmapped address")
var space = _make_space()
val area = _make_anon(0x400000, 0x1000)
space = vma_add(space, area).space
val found = vma_find(space, 0x800000)
# 0x800000 is outside any VMA — vma_count stays 1 (nothing removed)
expect(space.vma_count).to_equal(1)
if val Some(_a) = found:
    expect(0).to_equal(1)   # should be nil — fail if reached
```

</details>

#### finds correct VMA among multiple

- finds correct VMA among multiple
   - Expected: a.start equals `0x500000`
   - Expected: 0 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds correct VMA among multiple")
var space = _make_space()
val a1 = _make_anon(0x400000, 0x1000)
val a2 = _make_anon(0x402000, 0x1000)
val a3 = _make_anon(0x500000, 0x2000)
space = vma_add(space, a1).space
space = vma_add(space, a2).space
space = vma_add(space, a3).space
val found = vma_find(space, 0x500800)
if val Some(a) = found:
    expect(a.start).to_equal(0x500000)
else:
    expect(0).to_equal(1)
```

</details>

#### does not find address exactly at end (exclusive)

- does not find address exactly at end (exclusive)
   - Expected: space.vma_count equals `1`
   - Expected: 0 equals `1)   # should be nil — fail if reached`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not find address exactly at end (exclusive)")
var space = _make_space()
val area = _make_anon(0x400000, 0x1000)
space = vma_add(space, area).space
val found = vma_find(space, 0x401000)  # one byte past end
# The VMA ends at 0x401000 (exclusive), so nothing should match
expect(space.vma_count).to_equal(1)
if val Some(_a) = found:
    expect(0).to_equal(1)   # should be nil — fail if reached
```

</details>

### vma_remove

#### removing entire VMA reduces count to 0

- removing entire VMA reduces count to 0
   - Expected: space.vma_count equals `1`
   - Expected: _a.start equals `0x400000`
   - Expected: space.vma_count equals `0`
   - Expected: 0 equals `1)   # should be nil — fail if reached`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removing entire VMA reduces count to 0")
var space = _make_space()
val area = _make_anon(0x400000, 0x4000)
space = vma_add(space, area).space
expect(space.vma_count).to_equal(1)

val found_before = vma_find(space, 0x401000)
if val Some(_a) = found_before:
    expect(_a.start).to_equal(0x400000)

space = vma_remove(space, 0x400000, 0x4000)
expect(space.vma_count).to_equal(0)
# After removal, vma_count is 0 — scan returns nil implicitly
val found_after = vma_find(space, 0x401000)
if val Some(_b) = found_after:
    expect(0).to_equal(1)   # should be nil — fail if reached
```

</details>

#### splitting a VMA produces two smaller VMAs

- splitting a VMA produces two smaller VMAs
   - Expected: split_result.code equals `0`
   - Expected: space.vma_count equals `2`
   - Expected: space.areas[0].len equals `0x2000`
   - Expected: space.areas[1].start equals `0x402000`
   - Expected: space.areas[1].len equals `0x2000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("splitting a VMA produces two smaller VMAs")
var space = _make_space()
val area = _make_anon(0x400000, 0x4000)
space = vma_add(space, area).space

val split_result = vma_split(space, 0x402000)
space = split_result.space

expect(split_result.code).to_equal(0)
expect(space.vma_count).to_equal(2)
expect(space.areas[0].len).to_equal(0x2000)
expect(space.areas[1].start).to_equal(0x402000)
expect(space.areas[1].len).to_equal(0x2000)
```

</details>

#### backing_offset of right fragment is correct after split

- backing_offset of right fragment is correct after split
   - Expected: split_result.code equals `0`
   - Expected: space.areas[1].backing_offset equals `0x1000 + 0x4000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("backing_offset of right fragment is correct after split")
var space = _make_space()
val area = _make_file(0x500000, 0x8000, 7, 0x1000)
space = vma_add(space, area).space

val split_result = vma_split(space, 0x504000)
space = split_result.space

expect(split_result.code).to_equal(0)
expect(space.areas[1].backing_offset).to_equal(0x1000 + 0x4000)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fffa29ad7737140975cff51d6551779ded9fe7f30ee22702f19cd0dccff8609d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fffa29ad7737140975cff51d6551779ded9fe7f30ee22702f19cd0dccff8609d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fffa29ad7737140975cff51d6551779ded9fe7f30ee22702f19cd0dccff8609d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/os/kernel/memory/vmm_vma_spec.spl
mirror: doc/06_spec/unit/os/kernel/memory/vmm_vma_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/kernel/memory/vmm_vma_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/memory/vmm_vma_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/memory/vmm_vma_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 25 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/kernel/memory/vmm_vma_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates anon area with correct fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/memory/vmm_vma_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates file-backed area with backing handle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/memory/vmm_vma_spec.spl:100:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'VMA_COW flag is distinct from VMA_WRITE' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
