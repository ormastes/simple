# Segment Mapper Specification

> Tests covering segment_mapper, highest_loaded_address, map_segment validation, map_all no-op, map_stack validation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Segment Mapper Specification

## Scenarios

### segment_mapper

### highest_loaded_address

#### returns 0 for an empty list

- returns 0 for an empty list
   - Expected: highest_loaded_address(segs) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for an empty list")
val segs: [UserLoadSegment] = []
expect(highest_loaded_address(segs)).to_equal(0)
```

</details>

#### returns page-aligned upper bound for a single segment

- returns page-aligned upper bound for a single segment
   - Expected: highest_loaded_address(segs) equals `0x3000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns page-aligned upper bound for a single segment")
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

- rounds an unaligned upper bound up to the next page
   - Expected: highest_loaded_address(segs) equals `0x3000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rounds an unaligned upper bound up to the next page")
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

- takes the max across multiple segments
   - Expected: highest_loaded_address(segs) equals `0x5000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("takes the max across multiple segments")
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

- rejects a segment with file_size > mem_size
   - Expected: msg contains `file_size`
   - Expected: "expected Err, got Ok" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a segment with file_size > mem_size")
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

- returns Ok(0) on an empty segment list
   - Expected: n equals `0`
   - Expected: "expected Ok(0), got Err" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns Ok(0) on an empty segment list")
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

- rejects a zero-sized stack
   - Expected: msg contains `stack_size`
   - Expected: "expected Err, got Ok" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a zero-sized stack")
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

- rejects an initial frame larger than the stack
   - Expected: msg contains `initial stack`
   - Expected: "expected Err, got Ok" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an initial frame larger than the stack")
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

- rejects stack ranges that underflow
   - Expected: msg contains `underflows`
   - Expected: "expected Err, got Ok" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects stack ranges that underflow")
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
| Source | `test/unit/os/kernel/loader/segment_mapper_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering segment_mapper, highest_loaded_address, map_segment validation, map_all no-op, map_stack validation.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a5f12789d6c086a347a152de15bb0fbc51e9e50c836794f3b422e40884bd7ab2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a5f12789d6c086a347a152de15bb0fbc51e9e50c836794f3b422e40884bd7ab2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a5f12789d6c086a347a152de15bb0fbc51e9e50c836794f3b422e40884bd7ab2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/os/kernel/loader/segment_mapper_spec.spl
mirror: doc/06_spec/unit/os/kernel/loader/segment_mapper_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/kernel/loader/segment_mapper_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/loader/segment_mapper_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/loader/segment_mapper_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/kernel/loader/segment_mapper_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns 0 for an empty list' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/loader/segment_mapper_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns page-aligned upper bound for a single segment' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/loader/segment_mapper_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rounds an unaligned upper bound up to the next page' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
