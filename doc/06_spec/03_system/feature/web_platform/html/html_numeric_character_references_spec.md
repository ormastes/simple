# HTML Numeric Character References

> WHATWG numeric character-reference normalization from tokenizer semantics
> through canonical BeDOM, Draw IR, and Engine2D.

| Scenarios | Active | Skipped | Pending |
|-----------|--------|---------|---------|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

## At a Glance

| Field | Value |
|-------|-------|
| Status | Runnable; runtime not executed for this artifact update |
| Requirements | REQ-WEB-BROWSER-002, REQ-WEB-BROWSER-003, REQ-WEB-BROWSER-004 |
| Source | `test/03_system/feature/web_platform/html/html_numeric_character_references_spec.spl` |
| Source lines | 232 |
| Source SHA-256 | `a76f26ef14411c31c8683d0ab71dc8ad2be02997cd669ecfb9ede76599581c6d` |
| Scenario count | 1 |
| Visible step count | 4 |
| Direct assertion sites | 18 |
| Folded executable lines | 114 |
| Updated | 2026-07-31 |

## Overview

The scenario verifies every numeric reference from `0x80` through `0x9F` in
decimal and hexadecimal. The 27 defined Windows-1252 compatibility values map
to their WHATWG Unicode replacements. Undefined C1 values `0x81`, `0x8D`,
`0x8F`, `0x90`, and `0x9D` remain identity controls.

Missing semicolons decode in text and attributes even before ASCII letters or
`=`, unlike the named-reference attribute ambiguity rule. Zero, surrogates,
out-of-range scalars, and overflowing digit runs become `U+FFFD`; valid
controls and noncharacters retain their scalar values.

The final step compares three equal-sized frames:

- the numeric entity `L&#128;R`;
- the literal Unicode text `L€R`;
- the negative-control glyph text `LXR`.

The entity and literal-Euro frames must be identical. The negative-control
frame must differ by at least one pixel, preventing an all-background or
renderer-no-op result from satisfying the parity assertion.

## Evidence

| Step | Evidence |
|------|----------|
| Decode the C1 table | 32 decimal and 32 hexadecimal direct equality checks, plus exact table counts |
| Preserve context rules | Exact text and quoted-attribute values, including missing semicolons, no-digit references, undefined C1 identity, and named-reference ambiguity |
| Bound invalid input | Exact replacement/identity scalars, delimiter retention, saturation of a 64-digit overflow, and token-limit truncation |
| Render canonical output | Exact BeDOM title/text, exact Draw IR text parity, exact entity/literal pixel parity, positive negative-control pixel difference, and a known background pixel |

The manual records static source parity only. It does not claim that the
scenario was executed or passed.

## Scenario

### should normalize the complete C1 table through Web rendering

1. Decode every C1 value in decimal and hexadecimal.
2. Preserve numeric missing-semicolon rules in text and attributes.
3. Replace invalid scalars while retaining delimiters and quotas.
4. Match literal Unicode through BeDOM, Draw IR, and Engine2D.

<details>
<summary>Executable SSpec</summary>

Scenario body: 114 lines folded for review.

Parity: this block is exactly source lines 119–232 with only the common
eight-space scenario-body indent removed. It uses the imports, constants, and
helpers in the source file above; it is not a standalone file. The source path,
total line count, and SHA-256 are recorded above.

```simple
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

## Failure Interpretation

- A table mismatch is a numeric-reference normalization defect.
- A text/attribute mismatch is a tokenizer context defect.
- A delimiter or quota mismatch is a bounded-consumption defect.
- A BeDOM mismatch is a canonical tree semantic defect.
- A Draw IR mismatch is a Web lowering defect.
- Equal Euro/control frames indicate a nondiscriminating Engine2D oracle.
- Different entity/literal-Euro frames indicate normalization did not reach
  canonical pixels.

</details>

## Artifact Integrity

The folded executable is tied to the source path, 232-line count, 114-line
scenario-body count, and SHA-256 above. Any source edit requires refreshing all
four values and the folded block together.
