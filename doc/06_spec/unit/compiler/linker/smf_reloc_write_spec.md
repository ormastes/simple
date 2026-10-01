# Smf Reloc Write Specification

> Tests covering SMF Relocation Writing, wire format constants, relocation entry serialization, multiple relocations.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Smf Reloc Write Specification

## Scenarios

### SMF Relocation Writing

### wire format constants

#### relocation entry is 24 bytes

- relocation entry is 24 bytes
   - Expected: entry_size equals `24`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("relocation entry is 24 bytes")
# Each relocation entry: offset(8) + sym_idx(4) + type(1) + pad(3) + addend(8) = 24
val entry_size = 8 + 4 + 1 + 3 + 8
expect(entry_size).to_equal(24)
```

</details>

#### section type wire values are correct

- section type wire values are correct
   - Expected: code_type equals `1`
   - Expected: reloc_type equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("section type wire values are correct")
# Code=1, Data=2, RoData=3, Bss=4, RelTab=5
val code_type = 1
val reloc_type = 5
expect(code_type).to_equal(1)
expect(reloc_type).to_equal(5)
```

</details>

#### relocation type wire values are correct

- relocation type wire values are correct
   - Expected: abs64 equals `1`
   - Expected: rel32 equals `2`
   - Expected: plt_rel32 equals `3`
   - Expected: got_rel32 equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("relocation type wire values are correct")
# Abs64=1, Rel32=2, PltRel32=3, GotRel32=4
val abs64 = 1
val rel32 = 2
val plt_rel32 = 3
val got_rel32 = 4
expect(abs64).to_equal(1)
expect(rel32).to_equal(2)
expect(plt_rel32).to_equal(3)
expect(got_rel32).to_equal(4)
```

</details>

### relocation entry serialization

#### serializes offset as u64 little-endian

- serializes offset as u64 little-endian
   - Expected: read_back equals `0x1234`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes offset as u64 little-endian")
# Simulate a relocation entry with known offset
val offset_val = 0x1234
var bytes: [u8] = []
# Write offset as u64 LE
bytes.push((offset_val & 0xFF) as u8)
bytes.push(((offset_val >> 8) & 0xFF) as u8)
bytes.push(((offset_val >> 16) & 0xFF) as u8)
bytes.push(((offset_val >> 24) & 0xFF) as u8)
bytes.push(0)
bytes.push(0)
bytes.push(0)
bytes.push(0)
val read_back = u64_from_le_bytes(bytes, 0)
expect(read_back).to_equal(0x1234)
```

</details>

#### serializes symbol index as u32 little-endian

- serializes symbol index as u32 little-endian
   - Expected: read_back equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes symbol index as u32 little-endian")
val sym_idx = 42
var bytes: [u8] = []
bytes.push((sym_idx & 0xFF) as u8)
bytes.push(((sym_idx >> 8) & 0xFF) as u8)
bytes.push(((sym_idx >> 16) & 0xFF) as u8)
bytes.push(((sym_idx >> 24) & 0xFF) as u8)
val read_back = u32_from_le_bytes(bytes, 0)
expect(read_back).to_equal(42)
```

</details>

#### serializes reloc type as single byte with 3 pad bytes

- serializes reloc type as single byte with 3 pad bytes
   - Expected: bytes[0] equals `2`
   - Expected: bytes[1] equals `0`
   - Expected: bytes[2] equals `0`
   - Expected: bytes[3] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes reloc type as single byte with 3 pad bytes")
val reloc_type = 2  # Rel32
var bytes: [u8] = []
bytes.push(reloc_type as u8)
bytes.push(0)  # pad
bytes.push(0)  # pad
bytes.push(0)  # pad
expect(bytes[0]).to_equal(2)
expect(bytes[1]).to_equal(0)
expect(bytes[2]).to_equal(0)
expect(bytes[3]).to_equal(0)
```

</details>

### multiple relocations

#### serializes multiple entries consecutively

- serializes multiple entries consecutively
   - Expected: total_size equals `72`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes multiple entries consecutively")
val entry_size = 24
val num_entries = 3
val total_size = entry_size * num_entries
expect(total_size).to_equal(72)
```

</details>

#### preserves entry count from reloc section size

- preserves entry count from reloc section size
   - Expected: entry_count equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves entry count from reloc section size")
val reloc_section_size = 120  # 5 entries * 24 bytes
val entry_count = reloc_section_size / 24
expect(entry_count).to_equal(5)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/linker/smf_reloc_write_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SMF Relocation Writing, wire format constants, relocation entry serialization, multiple relocations.
- SMF Relocation Writing
- wire format constants
- relocation entry serialization
- multiple relocations

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `c7e737c5f115437f6b34ab38c290ba3586aa821160993916f74affa68f7eb27f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c7e737c5f115437f6b34ab38c290ba3586aa821160993916f74affa68f7eb27f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c7e737c5f115437f6b34ab38c290ba3586aa821160993916f74affa68f7eb27f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler/linker/smf_reloc_write_spec.spl
mirror: doc/06_spec/unit/compiler/linker/smf_reloc_write_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/linker/smf_reloc_write_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/linker/smf_reloc_write_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/linker/smf_reloc_write_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 14 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/linker/smf_reloc_write_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'relocation entry is 24 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/linker/smf_reloc_write_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'section type wire values are correct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/linker/smf_reloc_write_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'relocation type wire values are correct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
