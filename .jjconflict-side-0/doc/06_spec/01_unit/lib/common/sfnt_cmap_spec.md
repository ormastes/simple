# Sfnt Cmap Specification

> Tests covering sfnt cmap glyph lookup.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sfnt Cmap Specification

## Scenarios

### sfnt cmap glyph lookup

#### prefers Unicode format 12 before format 4

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- prefers Unicode format 12 before format 4
   - Expected: sfnt_cmap_glyph_id(font, 65) equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("prefers Unicode format 12 before format 4")
val blob: [u8] = [
    0, 0, 0, 2,
    0, 3, 0, 1, 0, 0, 0, 20,
    0, 3, 0, 10, 0, 0, 0, 52,
    0, 4, 0, 32, 0, 0, 0, 4, 0, 4, 0, 1, 0, 0,
    0, 65, 255, 255, 0, 0, 0, 65, 255, 255,
    255, 201, 0, 1, 0, 0, 0, 0,
    0, 12, 0, 0, 0, 0, 0, 28, 0, 0, 0, 0, 0, 0, 0, 1,
    0, 0, 0, 65, 0, 0, 0, 65, 0, 0, 0, 99
]
val font = OtFont(blob: blob, tables: [OtTable(tag: 1668112752, offset: 0, length: 80)])

expect(sfnt_cmap_glyph_id(font, 65)).to_equal(99)
```

</details>

#### rejects a format 4 offset outside cmap

- rejects a format 4 offset outside cmap
   - Expected: parse_cmap_format4(font) equals `None`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a format 4 offset outside cmap")
val blob: [u8] = [0, 0, 0, 1, 0, 3, 0, 1, 0, 0, 1, 0]
val font = OtFont(blob: blob, tables: [OtTable(tag: 1668112752, offset: 0, length: 12)])

expect(parse_cmap_format4(font)).to_equal(None)
```

</details>

#### rejects a short declared format 4 subtable

- rejects a short declared format 4 subtable
   - Expected: parse_cmap_format4(font) equals `None`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a short declared format 4 subtable")
val blob: [u8] = [
    0, 0, 0, 1, 0, 3, 0, 1, 0, 0, 0, 12,
    0, 4, 0, 14, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0
]
val font = OtFont(blob: blob, tables: [OtTable(tag: 1668112752, offset: 0, length: 26)])

expect(parse_cmap_format4(font)).to_equal(None)
```

</details>

#### rejects segCount arrays larger than the format 4 subtable

- rejects segCount arrays larger than the format 4 subtable
   - Expected: parse_cmap_format4(font) equals `None`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects segCount arrays larger than the format 4 subtable")
val blob: [u8] = [
    0, 0, 0, 1, 0, 3, 0, 1, 0, 0, 0, 12,
    0, 4, 0, 16, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0
]
val font = OtFont(blob: blob, tables: [OtTable(tag: 1668112752, offset: 0, length: 28)])

expect(parse_cmap_format4(font)).to_equal(None)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/sfnt_cmap_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering sfnt cmap glyph lookup.
- sfnt cmap glyph lookup

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b64f5c99462d784f9732d68cf1b3679d7d89be38a1baff7920a69e8ed8644a61`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b64f5c99462d784f9732d68cf1b3679d7d89be38a1baff7920a69e8ed8644a61`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b64f5c99462d784f9732d68cf1b3679d7d89be38a1baff7920a69e8ed8644a61`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/common/sfnt_cmap_spec.spl
mirror: doc/06_spec/01_unit/lib/common/sfnt_cmap_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/sfnt_cmap_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/sfnt_cmap_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/sfnt_cmap_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/sfnt_cmap_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prefers Unicode format 12 before format 4' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/sfnt_cmap_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a format 4 offset outside cmap' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/sfnt_cmap_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a short declared format 4 subtable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
