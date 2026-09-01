# text_ops_spec

> Direct branch matrix for legacy mode-aware Unicode text operations.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# text_ops_spec

Direct branch matrix for legacy mode-aware Unicode text operations.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/encoding/text_ops_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Direct branch matrix for legacy mode-aware Unicode text operations.

## Scenarios

### mode-aware text operations

#### uses explicit byte semantics in UTF-8 compatibility mode

- uses explicit byte semantics in UTF-8 compatibility mode
   - Expected: text_len_mode("abc") equals `3`
   - Expected: text_char_at_mode("abc", 1) equals `b`
   - Expected: text_char_at_mode("abc", -1) equals ``
   - Expected: text_char_at_mode("abc", 3) equals ``
   - Expected: text_slice_mode("abcd", -2, 20) equals `abcd`
   - Expected: text_slice_mode("abcd", 3, 2) equals ``
   - Expected: text_chars_mode("abc") equals `["a", "b", "c"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("uses explicit byte semantics in UTF-8 compatibility mode")
set_char_mode(CharMode.Utf8)
expect(text_len_mode("abc")).to_equal(3)
expect(text_char_at_mode("abc", 1)).to_equal("b")
expect(text_char_at_mode("abc", -1)).to_equal("")
expect(text_char_at_mode("abc", 3)).to_equal("")
expect(text_slice_mode("abcd", -2, 20)).to_equal("abcd")
expect(text_slice_mode("abcd", 3, 2)).to_equal("")
expect(text_chars_mode("abc")).to_equal(["a", "b", "c"])
```

</details>

#### uses scalar semantics in FullUnicode compatibility mode

- uses scalar semantics in FullUnicode compatibility mode
   - Expected: text_len_mode(value) equals `4`
   - Expected: text_char_at_mode(value, 0) equals `A`
   - Expected: text_char_at_mode(value, 1) equals `é`
   - Expected: text_char_at_mode(value, 2) equals `한`
   - Expected: text_char_at_mode(value, 3) equals `😀`
   - Expected: text_char_at_mode(value, 4) equals ``
   - Expected: text_slice_mode(value, 1, 3) equals `é한`
   - Expected: text_slice_mode(value, 4, 9) equals ``
   - Expected: text_slice_mode(value, 9, 10) equals ``
   - Expected: text_chars_mode(value) equals `["A", "é", "한", "😀"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("uses scalar semantics in FullUnicode compatibility mode")
set_char_mode(CharMode.FullUnicode)
val value = "Aé한😀"
expect(text_len_mode(value)).to_equal(4)
expect(text_char_at_mode(value, 0)).to_equal("A")
expect(text_char_at_mode(value, 1)).to_equal("é")
expect(text_char_at_mode(value, 2)).to_equal("한")
expect(text_char_at_mode(value, 3)).to_equal("😀")
expect(text_char_at_mode(value, 4)).to_equal("")
expect(text_slice_mode(value, 1, 3)).to_equal("é한")
expect(text_slice_mode(value, 4, 9)).to_equal("")
expect(text_slice_mode(value, 9, 10)).to_equal("")
expect(text_chars_mode(value)).to_equal(["A", "é", "한", "😀"])
set_char_mode(CharMode.Utf8)
```

</details>

#### classifies zero narrow and wide display ranges

- classifies zero narrow and wide display ranges
   - Expected: codepoint_display_width(cp) equals `0`
   - Expected: codepoint_display_width(cp) equals `2`
   - Expected: codepoint_display_width(0x0041) equals `1`
   - Expected: text_display_width("Aé 한\u{0301}") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("classifies zero narrow and wide display ranges")
for cp in [0, 31, 127, 0x0300, 0x1AB0, 0x1DC0, 0xFE20,
        0x200B, 0x200C, 0x200D, 0xFEFF, 0x00AD]:
    expect(codepoint_display_width(cp)).to_equal(0)
for cp in [0x4E00, 0x3400, 0x20000, 0xF900, 0xAC00, 0x1100,
        0x2329, 0x3000, 0x3040, 0x30A0, 0x3100, 0x3130,
        0x3190, 0x3200, 0x3300, 0xFF01, 0xFFE0]:
    expect(codepoint_display_width(cp)).to_equal(2)
expect(codepoint_display_width(0x0041)).to_equal(1)
expect(text_display_width("Aé 한\u{0301}")).to_equal(5)
```

</details>

#### classifies every simplified script range and fallthrough

- classifies every simplified script range and fallthrough
   - Expected: codepoint_script(cps[i]) equals `scripts[i]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("classifies every simplified script range and fallthrough")
val cps = [0x0041, 0x1E00, 0x0400, 0x0600, 0x0750, 0x08A0,
    0xFB50, 0xFE70, 0x0900, 0xA8E0, 0x0980, 0xAC00, 0x1100,
    0x3130, 0xA960, 0xD7B0, 0x4E00, 0x3400, 0x20000,
    0x3040, 0xF900, 0x0030, 0x2000, 0x3000, 0x10FFFF]
val scripts = [UnicodeScript.Latin, UnicodeScript.Latin,
    UnicodeScript.Cyrillic, UnicodeScript.Arabic,
    UnicodeScript.Arabic, UnicodeScript.Arabic, UnicodeScript.Arabic,
    UnicodeScript.Arabic, UnicodeScript.Devanagari,
    UnicodeScript.Devanagari, UnicodeScript.Bengali,
    UnicodeScript.Hangul, UnicodeScript.Hangul, UnicodeScript.Hangul,
    UnicodeScript.Hangul, UnicodeScript.Hangul, UnicodeScript.CJK,
    UnicodeScript.CJK, UnicodeScript.CJK, UnicodeScript.CJK,
    UnicodeScript.CJK, UnicodeScript.Common, UnicodeScript.Common,
    UnicodeScript.Common, UnicodeScript.Unknown]
var i: i64 = 0
while i < cps.len():
    expect(codepoint_script(cps[i])).to_equal(scripts[i])
    i = i + 1
```

</details>

#### delegates indexed access slicing and length to WidthIndex

- delegates indexed access slicing and length to WidthIndex
   - Expected: text_char_at_indexed(index, 2) equals `한`
   - Expected: text_char_at_indexed(index, 9) equals ``
   - Expected: text_slice_indexed(index, 1, 3) equals `é한`
   - Expected: text_slice_indexed(index, -1, 3) equals ``
   - Expected: text_len_indexed(index) equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("delegates indexed access slicing and length to WidthIndex")
val index = WidthIndex.for_text("Aé한😀")
expect(text_char_at_indexed(index, 2)).to_equal("한")
expect(text_char_at_indexed(index, 9)).to_equal("")
expect(text_slice_indexed(index, 1, 3)).to_equal("é한")
expect(text_slice_indexed(index, -1, 3)).to_equal("")
expect(text_len_indexed(index)).to_equal(4)
index.free()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `b70347fcfbf36ca0002f66fa677019147e08b65c98427ee011abdaf3c8018f7c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b70347fcfbf36ca0002f66fa677019147e08b65c98427ee011abdaf3c8018f7c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b70347fcfbf36ca0002f66fa677019147e08b65c98427ee011abdaf3c8018f7c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/encoding/text_ops_spec.spl
mirror: doc/06_spec/01_unit/lib/common/encoding/text_ops_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/encoding/text_ops_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/encoding/text_ops_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/encoding/text_ops_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/encoding/text_ops_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses explicit byte semantics in UTF-8 compatibility mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/encoding/text_ops_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses scalar semantics in FullUnicode compatibility mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/encoding/text_ops_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'classifies zero narrow and wide display ranges' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
