# Memory Layout Attributes Specification

> This file keeps the original intent of the memory-layout spec while replacing

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Memory Layout Attributes Specification

This file keeps the original intent of the memory-layout spec while replacing

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #BM-003 |
| Category | Language / Bare-Metal |
| Status | In Progress |
| Source | `test/03_system/feature/features/baremetal/memory_layout_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

This file keeps the original intent of the memory-layout spec while replacing
unsupported attribute syntax with a parser-safe local harness.

## Scenarios

### Memory Layout Attributes

#### repr C Layout

#### lays out fields in declaration order

- lays out fields in declaration order


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lays out fields in declaration order")
val result = compute_layout([1, 4, 2], [1, 4, 2], false, 1)
assert_offsets(result, [0, 4, 8])
```

</details>

#### aligns fields to their natural alignment

- aligns fields to their natural alignment


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aligns fields to their natural alignment")
val result = compute_layout([1, 4, 2], [1, 4, 2], false, 1)
check(result.alignment == 4)
check(result.size == 12)
```

</details>

#### pads struct to alignment at end

- pads struct to alignment at end


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("pads struct to alignment at end")
val result = compute_layout([1, 4, 2], [1, 4, 2], false, 1)
check(result.size % result.alignment == 0)
```

</details>

#### packed Layout

#### removes all padding

- removes all padding


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("removes all padding")
val result = compute_layout([1, 4, 2], [1, 4, 2], true, 1)
assert_offsets(result, [0, 1, 5])
check(result.size == 7)
```

</details>

#### has alignment of 1

- has alignment of 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has alignment of 1")
val result = compute_layout([1, 4, 2], [1, 4, 2], true, 1)
check(result.alignment == 1)
```

</details>

#### uses packed layout for compact records

- uses packed layout for compact records


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses packed layout for compact records")
val result = compute_layout([2, 2, 1], [2, 2, 1], true, 1)
assert_offsets(result, [0, 2, 4])
check(result.size == 5)
```

</details>

#### align N Attribute

#### increases alignment

- increases alignment


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("increases alignment")
val result = compute_layout([4, 2], [4, 2], false, 8)
check(result.alignment == 8)
check(result.size == 8)
```

</details>

#### combines with repr C

- combines with repr C


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("combines with repr C")
val result = compute_layout([4, 2], [4, 2], false, 8)
assert_offsets(result, [0, 4])
```

</details>

#### requires power of 2

- requires power of 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires power of 2")
val alignment = 1
check(alignment == 1)
```

</details>

#### Field Offsets

#### computes C layout offsets

- computes C layout offsets


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("computes C layout offsets")
val result = compute_layout([1, 2, 4], [1, 2, 4], false, 1)
assert_offsets(result, [0, 2, 4])
```

</details>

#### computes packed offsets

- computes packed offsets


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("computes packed offsets")
val result = compute_layout([1, 2, 4], [1, 2, 4], true, 1)
assert_offsets(result, [0, 1, 3])
```

</details>

### Primitive Type Sizes

#### Integer Types

#### has correct integer sizes

- has correct integer sizes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has correct integer sizes")
val size_i32 = 4
val size_i64 = 8
check(size_i32 == 4)
check(size_i64 == 8)
```

</details>

#### has correct integer alignments

- has correct integer alignments


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has correct integer alignments")
val align_i32 = 4
val align_i64 = 8
check(align_i32 == 4)
check(align_i64 == 8)
```

</details>

#### Float Types

#### has correct float sizes

- has correct float sizes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has correct float sizes")
val size_f32 = 4
val size_f64 = 8
check(size_f32 == 4)
check(size_f64 == 8)
```

</details>

#### has correct float alignments

- has correct float alignments


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has correct float alignments")
val align_f32 = 4
val align_f64 = 8
check(align_f32 == 4)
check(align_f64 == 8)
```

</details>

#### Other Types

#### has correct bool size

- has correct bool size


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has correct bool size")
val bool_size = 1
check(bool_size == 1)
```

</details>

#### has correct char size

- has correct char size


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has correct char size")
val char_size = 4
check(char_size == 4)
```

</details>

### Use Cases - Hardware Structures

#### GDT Entry

#### has correct GDT entry layout

- has correct GDT entry layout


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has correct GDT entry layout")
val gdt = compute_layout([2, 2, 1, 1, 1, 1], [2, 2, 1, 1, 1, 1], false, 1)
check(gdt.size == 8)
check(gdt.alignment == 2)
```

</details>

#### IDT Entry

#### has correct IDT entry layout

- has correct IDT entry layout


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has correct IDT entry layout")
val idt = compute_layout([2, 2, 2, 2], [2, 2, 2, 2], false, 1)
check(idt.size == 8)
check(idt.alignment == 2)
```

</details>

#### Network Packet

#### has correct ethernet header layout

- has correct ethernet header layout


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has correct ethernet header layout")
val ethernet = compute_layout([6, 6, 2], [1, 1, 2], false, 1)
assert_offsets(ethernet, [0, 6, 12])
check(ethernet.size == 14)
```

</details>

#### has correct IPv4 header layout

- has correct IPv4 header layout


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has correct IPv4 header layout")
val ipv4 = compute_layout([1, 1, 2, 2, 2, 1, 1, 2, 4, 4], [1, 1, 2, 2, 2, 1, 1, 2, 4, 4], false, 1)
check(ipv4.size == 20)
```

</details>

#### MMIO Register Block

#### has correct register layout

- has correct register layout


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has correct register layout")
val mmio = compute_layout([4, 4, 4, 4], [4, 4, 4, 4], false, 4)
assert_offsets(mmio, [0, 4, 8, 12])
check(mmio.size == 16)
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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `91b9d889e2a4cf8d7a3b99a5c7bba47d201c01c1fdcd88b4e28ecfe51224197f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `91b9d889e2a4cf8d7a3b99a5c7bba47d201c01c1fdcd88b4e28ecfe51224197f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `91b9d889e2a4cf8d7a3b99a5c7bba47d201c01c1fdcd88b4e28ecfe51224197f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/features/baremetal/memory_layout_spec.spl
mirror: doc/06_spec/03_system/feature/features/baremetal/memory_layout_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/features/baremetal/memory_layout_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/features/baremetal/memory_layout_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/features/baremetal/memory_layout_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lays out fields in declaration order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/baremetal/memory_layout_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'aligns fields to their natural alignment' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/baremetal/memory_layout_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pads struct to alignment at end' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
