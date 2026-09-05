# Interpreter bracket-slice byte indexing Specification

> Pins BYTE indexing for the text bracket-slice operator `s[a:b]` (and the range-index form `s[a..b]`) under the tree-walking interpreter.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Interpreter bracket-slice byte indexing Specification

Pins BYTE indexing for the text bracket-slice operator `s[a:b]` (and the range-index form `s[a..b]`) under the tree-walking interpreter.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #INTERP-BRACKET-SLICE-BYTE-001 |
| Category | Runtime |
| Difficulty | 3/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | doc/08_tracking/bug/test_harness_execution_divergence_2026-07-29.md |
| Source | `test/01_unit/bugs/text_bracket_slice_byte_index_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Pins BYTE indexing for the text bracket-slice operator `s[a:b]` (and the
range-index form `s[a..b]`) under the tree-walking interpreter.

`bin/simple test` forces SIMPLE_EXECUTION_MODE=interpret for every spec,
so this spec runs under the exact engine that was broken: the
interpreter's Expr::Slice path normalized indices against the BYTE
length but then sliced a CHAR vector — an internally mixed index space.
On multi-byte text every byte-offset slice was silently wrong:
glob_match("café.txt", "caf?.txt") returned false and js
string_charAt("日本語", 1) returned "" under the test lane while the
default engine computed both correctly.

These examples red on the broken interpreter and green after the fix —
running under `bin/simple test` IS the forced-interpreter condition.

## Scenarios

### text bracket slice s[a:b] under the test-lane interpreter

#### multi-byte 3-byte sequences (CJK)

#### slices by bytes, not characters

- slices by bytes, not characters
   - Expected: s[3:6] equals `本`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("slices by bytes, not characters")
# "日本語" is 9 bytes / 3 chars; [3:6] must be the middle
# codepoint. The char-indexed interpreter returned "" here.
val s = "日本語"
expect(s[3:6]).to_equal("本")
```

</details>

#### slices the first codepoint

- slices the first codepoint
   - Expected: s[0:3] equals `日`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("slices the first codepoint")
val s = "日本語"
expect(s[0:3]).to_equal("日")
```

</details>

#### 2-byte sequences

#### keeps byte offsets aligned across a 2-byte codepoint

- keeps byte offsets aligned across a 2-byte codepoint
   - Expected: t[0:5] equals `café`
   - Expected: t[5:9] equals `Zdef`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps byte offsets aligned across a 2-byte codepoint")
# "caféZdef": é is bytes 3-4, Z is byte 5.
val t = "caféZdef"
expect(t[0:5]).to_equal("café")
expect(t[5:9]).to_equal("Zdef")
```

</details>

#### agrees with the byte-indexed .slice() method

- agrees with the byte-indexed .slice() method
   - Expected: t[5:9] equals `t.slice(5, 9)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("agrees with the byte-indexed .slice() method")
val t = "caféZdef"
expect(t[5:9]).to_equal(t.slice(5, 9))
```

</details>

#### 4-byte sequences (emoji)

#### slices an emoji by its byte range

- slices an emoji by its byte range
   - Expected: u[1:5] equals `😀`
   - Expected: u[5:6] equals `y`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("slices an emoji by its byte range")
# "x😀y": 😀 is bytes 1-4.
val u = "x😀y"
expect(u[1:5]).to_equal("😀")
expect(u[5:6]).to_equal("y")
```

</details>

#### negative and open ends stay byte-based

#### resolves a negative start against the byte length

- resolves a negative start against the byte length
   - Expected: t[-3:] equals `def`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves a negative start against the byte length")
val t = "caféZdef"
expect(t[-3:]).to_equal("def")
```

</details>

#### slices an open end to the byte length

- slices an open end to the byte length
   - Expected: s[6:] equals `語`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("slices an open end to the byte length")
val s = "日本語"
expect(s[6:]).to_equal("語")
```

</details>

#### range-index form s[a..b]

#### uses byte offsets like the colon form

- uses byte offsets like the colon form
   - Expected: t[5..9] equals `Zdef`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses byte offsets like the colon form")
val t = "caféZdef"
expect(t[5..9]).to_equal("Zdef")
```

</details>

#### handles an inclusive range by bytes

- handles an inclusive range by bytes
   - Expected: t[5..=8] equals `Zdef`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles an inclusive range by bytes")
val t = "caféZdef"
expect(t[5..=8]).to_equal("Zdef")
```

</details>

### glob and js-string shapes that redded under bin/simple test

#### glob ? wildcard across a multi-byte codepoint

#### matches caf?.txt against café.txt

- matches caf?.txt against café.txt


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches caf?.txt against café.txt")
# Red under the char-indexed interpreter (returned false):
# `?` consumes the 2-byte é, later comparisons use byte
# offsets into p and s via bracket slices.
expect(glob_match("café.txt", "caf?.txt")).to_be_true()
```

</details>

#### matches a ? against a 3-byte CJK codepoint

- matches a ? against a 3-byte CJK codepoint


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches a ? against a 3-byte CJK codepoint")
expect(glob_match("日x.txt", "?x.txt")).to_be_true()
```

</details>

#### still rejects a real mismatch

- still rejects a real mismatch


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still rejects a real mismatch")
expect_not(glob_match("café.txt", "cag?.txt"))
```

</details>

#### charAt-style byte-walk then slice

#### extracts the middle CJK character via byte positions

- extracts the middle CJK character via byte positions
   - Expected: s[byte_pos:byte_pos + this_len] equals `本`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts the middle CJK character via byte positions")
# Inline of the js string_charAt walk (that function is
# module-private): byte_pos accumulated from codepoint byte
# lengths via the same public utf8 helpers it uses, then
# bracket-sliced. Returned "" under the char-indexed
# interpreter.
val s = "日本語"
val cps = text_codepoints(s)
var byte_pos = 0
var i = 0
while i < 1:
    byte_pos = byte_pos + utf8_codepoint_byte_len(cps[i])
    i = i + 1
val this_len = utf8_codepoint_byte_len(cps[1])
expect(s[byte_pos:byte_pos + this_len]).to_equal("本")
```

</details>

### bracket-slice spec vacuity guard

#### vacuity probe

#### executes assertions in this file

- executes assertions in this file
   - Expected: s[1:3] equals `ac`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes assertions in this file")
val s = "vacuity"
expect(s[1:3]).to_equal("ac")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Research:** `doc/08_tracking/bug/test_harness_execution_divergence_2026-07-29.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `03d0ca1c4f0cdc34fd8664e684fa3986e578428582d599f31f6f1e9ce20353bd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `03d0ca1c4f0cdc34fd8664e684fa3986e578428582d599f31f6f1e9ce20353bd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `03d0ca1c4f0cdc34fd8664e684fa3986e578428582d599f31f6f1e9ce20353bd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/bugs/text_bracket_slice_byte_index_spec.spl
mirror: doc/06_spec/01_unit/bugs/text_bracket_slice_byte_index_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/bugs/text_bracket_slice_byte_index_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/bugs/text_bracket_slice_byte_index_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/bugs/text_bracket_slice_byte_index_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'slices by bytes, not characters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/bugs/text_bracket_slice_byte_index_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'slices the first codepoint' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/bugs/text_bracket_slice_byte_index_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps byte offsets aligned across a 2-byte codepoint' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
