# HTML Numeric Character References

> This executable specification proves WHATWG numeric character-reference normalization across tokenizer text and attribute contexts, canonical BeDOM semantics, Web-to-Draw-IR lowering, and Engine2D pixels.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HTML Numeric Character References

This executable specification proves WHATWG numeric character-reference normalization across tokenizer text and attribute contexts, canonical BeDOM semantics, Web-to-Draw-IR lowering, and Engine2D pixels.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/html/html_numeric_character_references_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This executable specification proves WHATWG numeric character-reference
normalization across tokenizer text and attribute contexts, canonical BeDOM
semantics, Web-to-Draw-IR lowering, and Engine2D pixels.

The C1 table includes every value from `0x80` through `0x9F`. Defined legacy
Windows-1252 replacements map to their Unicode scalars; the five undefined C1
controls remain identity values.

## Requirement Traceability

- `REQ-WEB-BROWSER-002` requires deterministic canonical HTML semantics.
- `REQ-WEB-BROWSER-003` requires bounded parser behavior for hostile input.
- `REQ-WEB-BROWSER-004` requires Web output to lower through Draw IR and
  Engine2D.

## Claim Boundary

Parse errors are not exposed by the current tokenizer API. This scenario
therefore verifies emitted characters and bounded consumption, not parse-error
reporting.

## Scenarios

### WHATWG numeric character references

#### should normalize the complete C1 table through Web rendering

- should normalize the complete C1 table through Web rendering
   - HTML capture: after_step
- Decode every C1 value in decimal and hexadecimal
   - HTML capture: after_step
   - Evidence: HTML text verified by 2 expected checks
   - Expected: C1_HEX.len() equals `32`
   - Expected: C1_EXPECTED.len() equals `32`
- Preserve numeric missing-semicolon rules in text and attributes
   - HTML capture: after_step
   - Evidence: HTML text verified by 1 expected check
   - Expected: text_result equals `expected_missing`
- Replace invalid scalars while retaining delimiters and quotas
   - HTML capture: after_step
   - Evidence: HTML text verified by 3 expected checks
   - Expected: limited.truncated is true
   - Expected: limited.tokens.len() equals `3`
   - Expected: limited.tokens[1].data equals `replacement`
- Match literal Unicode through BeDOM, Draw IR, and Engine2D
   - HTML capture: after_step
   - Evidence: HTML text verified by 3 expected checks
   - Expected: be_dom_get_attr(entity_node, "title") equals `A€B`
   - Expected: be_dom_get_text_content(entity_node) equals `L€R`
   - Expected: entity_pixels equals `literal_pixels`


<details>
<summary>Executable SSpec</summary>

Runnable source: 116 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should normalize the complete C1 table through Web rendering")
step("Decode every C1 value in decimal and hexadecimal")
expect(C1_HEX.len()).to_equal(32)
expect(C1_EXPECTED.len()).to_equal(32)
var index = 0
while index < C1_EXPECTED.len():
    val expected = text.from_char_code(C1_EXPECTED[index])
    val decimal = (128 + index).to_string()
    expect(_character_data(
        "<p>&#" + decimal + ";</p>"
    )).to_equal(expected)
    expect(_character_data(
        "<p>&#x" + C1_HEX[index] + ";</p>"
    )).to_equal(expected)
    index = index + 1

step("Preserve numeric missing-semicolon rules in text and attributes")
val text_result = _character_data(
    "<p>&#128x|&#x80=|&#129z|&#;|&#x;</p>"
)
val attr = _first_start_tag(
    "<p title='&#128x|&#x80=|&#129z|&#;|&#x;|&not=x'>"
)
val expected_missing = (
    "€x|€=|" + text.from_char_code(0x81) + "z|&#;|&#x;"
)
expect(text_result).to_equal(expected_missing)
expect(_token_attr(attr, "title")).to_equal(
    expected_missing + "|&not=x"
)

step("Replace invalid scalars while retaining delimiters and quotas")
val replacement = text.from_char_code(0xFFFD)
val overflow_digits = (
    "99999999999999999999999999999999" +
    "99999999999999999999999999999999"
)
val scalar_inputs = [
    "&#0;", "&#xD800;", "&#xDFFF;", "&#x110000;",
    "&#" + overflow_digits + ";"
]
for input in scalar_inputs:
    expect(_character_data("<p>" + input + "</p>")).to_equal(
        replacement
    )
expect(_character_data(
    "<p>&#13;|&#1;|&#xFDD0;|&#x10FFFF;</p>"
)).to_equal(
    "\r|" + text.from_char_code(1) + "|" +
    text.from_char_code(0xFDD0) + "|" +
    text.from_char_code(0x10FFFF)
)
expect(_character_data(
    "<p>&#" + overflow_digits + ";tail</p>"
)).to_equal(replacement + "tail")
val limited = html_tokenizer_tokenize_with_limit(
    html_tokenizer_new(
        "<p>&#" + overflow_digits + ";</p>"
    ),
    2
)
expect(limited.truncated).to_equal(true)
expect(limited.tokens.len()).to_equal(3)
expect(limited.tokens[1].data).to_equal(replacement)

step("Match literal Unicode through BeDOM, Draw IR, and Engine2D")
val entity_html = (
    "<html><body style='margin:0'><div id='sample' " +
    "title='A&#128;B' style='display:block;width:96px;height:32px;" +
    "color:#111827;background:#e0f2fe'>L&#128;R</div></body></html>"
)
val literal_html = (
    "<html><body style='margin:0'><div id='sample' " +
    "title='A€B' style='display:block;width:96px;height:32px;" +
    "color:#111827;background:#e0f2fe'>L€R</div></body></html>"
)
val control_html = (
    "<html><body style='margin:0'><div id='sample' " +
    "title='AXB' style='display:block;width:96px;height:32px;" +
    "color:#111827;background:#e0f2fe'>LXR</div></body></html>"
)
val entity_node = _node(entity_html, "sample")
expect(be_dom_get_attr(entity_node, "title")).to_equal("A€B")
expect(be_dom_get_text_content(entity_node)).to_equal("L€R")
val entity_draw = simple_web_layout_render_html_draw_ir_result(
    entity_html, 96, 32
)
val literal_draw = simple_web_layout_render_html_draw_ir_result(
    literal_html, 96, 32
)
expect(_text_command(
    entity_draw.composition, "L€R"
).text_value).to_equal(
    _text_command(literal_draw.composition, "L€R").text_value
)
val entity_pixels = (
    simple_web_layout_render_html_readback_engine2d_result(
        entity_html, 96, 32, "software"
    ).readback.pixels
)
val literal_pixels = (
    simple_web_layout_render_html_readback_engine2d_result(
        literal_html, 96, 32, "software"
    ).readback.pixels
)
val control_pixels = (
    simple_web_layout_render_html_readback_engine2d_result(
        control_html, 96, 32, "software"
    ).readback.pixels
)
expect(entity_pixels).to_equal(literal_pixels)
expect(_pixel_difference_count(
    entity_pixels, control_pixels
)).to_be_greater_than(0)
expect(entity_pixels).to_contain(0xFFE0F2FEu32)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-WEB-BROWSER-002`
- `REQ-WEB-BROWSER-003`
- `REQ-WEB-BROWSER-004`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c5735db28b20e8d133ba64a2c9f4a8937e6e2695d8c6e0668ec11020ea717741`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c5735db28b20e8d133ba64a2c9f4a8937e6e2695d8c6e0668ec11020ea717741`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c5735db28b20e8d133ba64a2c9f4a8937e6e2695d8c6e0668ec11020ea717741`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/feature/web_platform/html/html_numeric_character_references_spec.spl
mirror: doc/06_spec/03_system/feature/web_platform/html/html_numeric_character_references_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=95 oracle=70
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/03_system/feature/web_platform/html/html_numeric_character_references_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/web_platform/html/html_numeric_character_references_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/web_platform/html/html_numeric_character_references_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/web_platform/html/html_numeric_character_references_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/feature/web_platform/html/html_numeric_character_references_spec.spl:127:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should normalize the complete C1 table through Web rendering' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/html/html_numeric_character_references_spec.spl:127:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should normalize the complete C1 table through Web rendering' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
