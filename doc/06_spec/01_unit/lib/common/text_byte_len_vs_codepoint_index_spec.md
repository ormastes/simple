# Text Byte Len Vs Codepoint Index Specification

> Tests covering text length primitives are byte counts, text indexing primitives are codepoint indexed, the shared codepoint-correct measurement leaf.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Text Byte Len Vs Codepoint Index Specification

## Scenarios

### text length primitives are byte counts

#### len and length both count UTF-8 bytes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- len and length both count UTF-8 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("len and length both count UTF-8 bytes")
assert_equal("aé€😀z".len(), 11)
assert_equal("aé€😀z".length(), 11)
assert_equal("abc".len(), 3)
```

</details>

#### byte length equals codepoint length only for ASCII

- byte length equals codepoint length only for ASCII


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte length equals codepoint length only for ASCII")
assert_equal("abc".len(), 3)
assert_equal("é".len(), 2)
assert_equal("漢".len(), 3)
assert_equal("😀".len(), 4)
```

</details>

### text indexing primitives are codepoint indexed

#### iteration yields codepoints, not bytes

- iteration yields codepoints, not bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("iteration yields codepoints, not bytes")
var n = 0
for ch in "aé€😀z":
    n = n + 1
assert_equal(n, 5)
```

</details>

#### the last codepoint sits at index len_in_codepoints - 1

- the last codepoint sits at index len_in_codepoints - 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the last codepoint sits at index len_in_codepoints - 1")
assert_equal("aé€😀z".char_at(4), "z")
```

</details>

#### char_code_at reads whole codepoints

- char_code_at reads whole codepoints


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("char_code_at reads whole codepoints")
assert_equal("é".char_code_at(0), 233)
assert_equal("漢".char_code_at(0), 28450)
```

</details>

### the shared codepoint-correct measurement leaf

#### measures by codepoint cells, not by UTF-8 byte count

- measures by codepoint cells, not by UTF-8 byte count


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("measures by codepoint cells, not by UTF-8 byte count")
assert_equal(text_cell_width("abc"), text_cell_width("a") * 3)
assert_equal(codepoint_cells(233), codepoint_cells(97))
assert_equal(codepoint_cells(28450), codepoint_cells(97) * 2)
```

</details>

#### charges an accented letter the same as an unaccented one

- charges an accented letter the same as an unaccented one


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("charges an accented letter the same as an unaccented one")
assert_equal(text_cell_width("é"), text_cell_width("e"))
```

</details>

#### charges a CJK glyph two cells, not its three UTF-8 bytes

- charges a CJK glyph two cells, not its three UTF-8 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("charges a CJK glyph two cells, not its three UTF-8 bytes")
assert_equal(text_cell_width("漢"), text_cell_width("a") * 2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/text_byte_len_vs_codepoint_index_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering text length primitives are byte counts, text indexing primitives are codepoint indexed, the shared codepoint-correct measurement leaf.
- text length primitives are byte counts
- text indexing primitives are codepoint indexed
- the shared codepoint-correct measurement leaf

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

- Canonical SPipe generation for source `539b2942df2dae1d00642100e35f6be4d81707f8f7715967175daa50c177ae7b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `539b2942df2dae1d00642100e35f6be4d81707f8f7715967175daa50c177ae7b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `539b2942df2dae1d00642100e35f6be4d81707f8f7715967175daa50c177ae7b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/text_byte_len_vs_codepoint_index_spec.spl
mirror: doc/06_spec/01_unit/lib/common/text_byte_len_vs_codepoint_index_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/text_byte_len_vs_codepoint_index_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/text_byte_len_vs_codepoint_index_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/text_byte_len_vs_codepoint_index_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'len and length both count UTF-8 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/text_byte_len_vs_codepoint_index_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'byte length equals codepoint length only for ASCII' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/text_byte_len_vs_codepoint_index_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'iteration yields codepoints, not bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
