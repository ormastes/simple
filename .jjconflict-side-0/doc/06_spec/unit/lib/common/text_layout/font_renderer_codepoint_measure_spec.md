# font_renderer_codepoint_measure_spec

> Purpose: Prove that FontRenderer measures by codepoint, not by UTF-8 byte.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# font_renderer_codepoint_measure_spec

Purpose: Prove that FontRenderer measures by codepoint, not by UTF-8 byte.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/text_layout/font_renderer_codepoint_measure_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that FontRenderer measures by codepoint, not by UTF-8 byte.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### FontRenderer measures by codepoint, not by UTF-8 byte

#### emits one advance per codepoint for a Latin-1 accented run

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- emits one advance per codepoint for a Latin-1 accented run
- Verify: emits one advance per codepoint for a Latin-1 accented run
   - Expected: "aéb".len() equals `4`
   - Expected: text_codepoints("aéb").len() equals `3`
   - Expected: renderer.measure_text_advances("aéb", 16).len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits one advance per codepoint for a Latin-1 accented run")
step("Verify: emits one advance per codepoint for a Latin-1 accented run")
# @req: REQ-LIB-COMMON-001
var renderer = FontRenderer.bitmap_only()
# "aéb" is 3 codepoints but 4 UTF-8 bytes.
expect("aéb".len()).to_equal(4)
expect(text_codepoints("aéb").len()).to_equal(3)
expect(renderer.measure_text_advances("aéb", 16).len()).to_equal(3)
```

</details>

#### emits one advance per codepoint for a CJK run

- emits one advance per codepoint for a CJK run
- Verify: emits one advance per codepoint for a CJK run
   - Expected: "漢字".len() equals `6`
   - Expected: renderer.measure_text_advances("漢字", 16).len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits one advance per codepoint for a CJK run")
step("Verify: emits one advance per codepoint for a CJK run")
var renderer = FontRenderer.bitmap_only()
# "漢字" is 2 codepoints but 6 UTF-8 bytes.
expect("漢字".len()).to_equal(6)
expect(renderer.measure_text_advances("漢字", 16).len()).to_equal(2)
```

</details>

#### measures an accented character the same as an unaccented one

- measures an accented character the same as an unaccented one
- Verify: measures an accented character the same as an unaccented one
   - Expected: accented equals `plain`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("measures an accented character the same as an unaccented one")
step("Verify: measures an accented character the same as an unaccented one")
var renderer = FontRenderer.bitmap_only()
val plain = renderer.measure_text_width("e", 16)
val accented = renderer.measure_text_width("é", 16)
expect(plain).to_be_greater_than(0)
expect(accented).to_equal(plain)
```

</details>

#### does not charge a CJK character three characters' worth of advance

- does not charge a CJK character three characters' worth of advance
- Verify: does not charge a CJK character three characters' worth of advance


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not charge a CJK character three characters' worth of advance")
step("Verify: does not charge a CJK character three characters' worth of advance")
var renderer = FontRenderer.bitmap_only()
val one_ascii = renderer.measure_text_width("a", 16)
val one_cjk = renderer.measure_text_width("漢", 16)
expect(one_ascii).to_be_greater_than(0)
# A byte count charged 3 * one_ascii here. The advance comes from the
# glyph, so the exact value is the font's business; what this pins is
# that it is not the UTF-8 byte inflation.
expect(one_cjk).to_be_less_than(one_ascii * 3)
```

</details>

#### measures no phantom codepoints past the end of a multibyte run

- measures no phantom codepoints past the end of a multibyte run
- Verify: measures no phantom codepoints past the end of a multibyte run


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("measures no phantom codepoints past the end of a multibyte run")
step("Verify: measures no phantom codepoints past the end of a multibyte run")
var renderer = FontRenderer.bitmap_only()
# Under the byte-indexed loop the three bytes of "漢" produced one real
# codepoint plus TWO reads of codepoint 0, so a 1-character string
# measured wider than a 2-character ASCII one.
val cjk = renderer.measure_text_width("漢", 16)
val two_ascii = renderer.measure_text_width("ab", 16)
expect(cjk).to_be_less_than(two_ascii * 2)
```

</details>

#### keeps pure-ASCII measurement unchanged

- keeps pure-ASCII measurement unchanged
- Verify: keeps pure-ASCII measurement unchanged
   - Expected: advances.len() equals `3`
   - Expected: renderer.measure_text_width("abc", 16) equals `total`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps pure-ASCII measurement unchanged")
step("Verify: keeps pure-ASCII measurement unchanged")
var renderer = FontRenderer.bitmap_only()
val advances = renderer.measure_text_advances("abc", 16)
expect(advances.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
var total = 0
for advance in advances:
    total = total + advance
# Kerning is folded into the advances, so the width is their sum.
expect(renderer.measure_text_width("abc", 16)).to_equal(total)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-LIB-COMMON-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `98d918ae0bab5fa386bdbfd813cc4270ff82b9ce7a15058f68b56c49613b1fd4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `98d918ae0bab5fa386bdbfd813cc4270ff82b9ce7a15058f68b56c49613b1fd4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `98d918ae0bab5fa386bdbfd813cc4270ff82b9ce7a15058f68b56c49613b1fd4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/common/text_layout/font_renderer_codepoint_measure_spec.spl
mirror: doc/06_spec/unit/lib/common/text_layout/font_renderer_codepoint_measure_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/text_layout/font_renderer_codepoint_measure_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/text_layout/font_renderer_codepoint_measure_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/text_layout/font_renderer_codepoint_measure_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/text_layout/font_renderer_codepoint_measure_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits one advance per codepoint for a Latin-1 accented run' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/text_layout/font_renderer_codepoint_measure_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits one advance per codepoint for a CJK run' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/text_layout/font_renderer_codepoint_measure_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'measures an accented character the same as an unaccented one' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
