# CSS Generated Content And Text Layout

> Proves authored and generated text cross the production HTML/CSS semantic and

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CSS Generated Content And Text Layout

Proves authored and generated text cross the production HTML/CSS semantic and

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/css/pseudo_text_wpt_spec.spl` |
| Updated | 2026-07-29 |
| Generator | `simple spipe-docgen` (Simple) |

Proves authored and generated text cross the production HTML/CSS semantic and
layout owner, preserve `::before`/element/`::after` order in canonical Draw IR,
and render from that same composition through Engine2D.

The remaining WPT-derived cases retain executable coverage for `attr()`,
generated-content suppression, overflow, wrapping, and alignment. They are
compatibility evidence, not substitutes for the canonical ordering scenario.

## Scenarios

### Production CSS generated content and text layout

#### should order before authored and after text on one exact line

- Resolve generated content in canonical web semantic and layout state
   - Protocol capture: after_step
- identify missing features
   - Protocol capture: after_step
- "pseudo-elements
   - Protocol capture: after_step
- Lower three parented text runs in exact CSS generated-content order
   - Protocol capture: after_step
   - Evidence: protocol response verified by 1 expected check
   - Expected: commands.len() equals `3`
- fail
   - Protocol capture: after_step
   - Evidence: protocol response verified by 15 expected checks
   - Expected: before.text_value equals `A`
   - Expected: authored.text_value equals `M`
   - Expected: after.text_value equals `Z`
   - Expected: before.parent_id equals `line`
   - Expected: authored.parent_id equals `line`
   - Expected: after.parent_id equals `line`
   - Expected: before.x equals `0`
   - Expected: before.y equals `0`
   - Expected: authored.x equals `before.x + before.width`
   - Expected: authored.y equals `0`
   - Expected: after.x equals `authored.x + authored.width`
   - Expected: after.y equals `0`
   - Expected: before.height equals `8`
   - Expected: authored.height equals `8`
   - Expected: after.height equals `8`
- Read exact ordered glyph pixels through Engine2D
   - Protocol capture: after_step
   - Evidence: protocol response verified by 4 expected checks
   - Expected: artifact.pixels.len() equals `WIDTH * HEIGHT`
   - Expected: _count_color(artifact.pixels, before_color) equals `32`
   - Expected: _count_color(artifact.pixels, authored_color) equals `32`
   - Expected: _count_color(artifact.pixels, after_color) equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 100 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val before_color = 0xFF2563EBu32
val authored_color = 0xFF16A34Au32
val after_color = 0xFFDC2626u32
val html = _html(
    "#line{display:block;width:48px;height:8px;color:#16a34a;" +
    "font-size:8px;line-height:8px;white-space:nowrap}" +
    "#line::before{content:'A';color:#2563eb}" +
    "#line::after{content:'Z';color:#dc2626}",
    "<div id='line'>M</div>"
)

step("Resolve generated content in canonical web semantic and layout state")
expect(_contains(
    identify_missing_features(html),
    "pseudo-elements (::before/::after)"
)).to_be(false)
expect(simple_web_layout_debug_style_by_id(
    html, "line", "display"
)).to_equal("block")
expect(simple_web_layout_debug_style_by_id(
    html, "line", "white_space_nowrap"
)).to_equal("true")
expect(simple_web_layout_debug_layout_by_id(
    html, WIDTH, HEIGHT, "line", "x"
)).to_equal("0")
expect(simple_web_layout_debug_layout_by_id(
    html, WIDTH, HEIGHT, "line", "y"
)).to_equal("0")
expect(simple_web_layout_debug_layout_by_id(
    html, WIDTH, HEIGHT, "line", "w"
)).to_equal("48")
expect(simple_web_layout_debug_layout_by_id(
    html, WIDTH, HEIGHT, "line", "h"
)).to_equal("8")

step("Lower three parented text runs in exact CSS generated-content order")
val composition = simple_web_layout_render_html_draw_ir(
    html, WIDTH, HEIGHT
)
val commands = _text_commands(composition)
expect(commands.len()).to_equal(3)
if commands.len() != 3:
    fail("expected ::before, authored, and ::after Draw IR text commands")
    return
val before = commands[0]
val authored = commands[1]
val after = commands[2]
expect(before.text_value).to_equal("A")
expect(authored.text_value).to_equal("M")
expect(after.text_value).to_equal("Z")
expect(before.parent_id).to_equal("line")
expect(authored.parent_id).to_equal("line")
expect(after.parent_id).to_equal("line")
expect(before.component_id.len()).to_be_greater_than(0)
expect(authored.component_id.len()).to_be_greater_than(0)
expect(after.component_id.len()).to_be_greater_than(0)
expect(before.x).to_equal(0)
expect(before.y).to_equal(0)
expect(authored.x).to_equal(before.x + before.width)
expect(authored.y).to_equal(0)
expect(after.x).to_equal(authored.x + authored.width)
expect(after.y).to_equal(0)
expect(before.width).to_be_greater_than(0)
expect(authored.width).to_be_greater_than(0)
expect(after.width).to_be_greater_than(0)
expect(before.height).to_equal(8)
expect(authored.height).to_equal(8)
expect(after.height).to_equal(8)

step("Read exact ordered glyph pixels through Engine2D")
val request = web_render_adapter_request(
    WEB_RENDER_TARGET_PURE_SIMPLE,
    "css-generated-content-order",
    "CSS generated content order",
    html,
    "",
    "",
    WIDTH,
    HEIGHT
).with_pixel_output()
val artifact = web_render_draw_ir_request_to_pixel_artifact(
    request, composition, "cpu"
)
expect(artifact.engine2d_status).to_equal(
    WEB_RENDER_ENGINE2D_STATUS_RENDERED
)
expect(artifact.pixels.len()).to_equal(WIDTH * HEIGHT)
expect(_count_color(artifact.pixels, before_color)).to_equal(32)
expect(_count_color(artifact.pixels, authored_color)).to_equal(32)
expect(_count_color(artifact.pixels, after_color)).to_equal(32)
expect(_last_color_x(
    artifact.pixels, before_color
)).to_be_less_than(_first_color_x(
    artifact.pixels, authored_color
))
expect(_last_color_x(
    artifact.pixels, authored_color
)).to_be_less_than(_first_color_x(
    artifact.pixels, after_color
))
```

</details>

#### should resolve generated attr text and keep a missing attr empty

- Resolve before attr content
   - Artifact capture: after_step
- "div::before{content:attr
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: before_count equals `96`
- Resolve after attr content
   - Artifact capture: after_step
- "div::after{content:attr
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: after_count equals `64`
- Keep a missing attr empty
   - Artifact capture: after_step
- "div::after{content:attr
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: missing_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve before attr content")
val before_count = _pixel_count(
    "div{color:#2563eb;font-size:8px}" +
    "div::before{content:attr(data-label)}",
    "<div data-label='ABC'></div>",
    0xFF2563EBu32
)
expect(before_count).to_equal(96)

step("Resolve after attr content")
val after_count = _pixel_count(
    "div{color:#dc2626;font-size:8px}" +
    "div::after{content:attr(data-label)}",
    "<div data-label='XY'></div>",
    0xFFDC2626u32
)
expect(after_count).to_equal(64)

step("Keep a missing attr empty")
val missing_count = _pixel_count(
    "div{color:#dc2626;font-size:8px}" +
    "div::after{content:attr(data-label)}",
    "<div></div>",
    0xFFDC2626u32
)
expect(missing_count).to_equal(0)
```

</details>

#### should suppress generated text for hidden host and pseudo boxes

- Suppress generated text with a hidden host box
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: hidden_host_count equals `0`
- Suppress generated text with a hidden before box
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: hidden_before_count equals `0`
- Suppress generated text with a hidden after box
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: hidden_after_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Suppress generated text with a hidden host box")
val hidden_host_count = _pixel_count(
    "div{display:none;color:#0891b2}" +
    "div::before{content:'Hidden'}",
    "<div></div>",
    0xFF0891B2u32
)
expect(hidden_host_count).to_equal(0)

step("Suppress generated text with a hidden before box")
val hidden_before_count = _pixel_count(
    "div{color:#0891b2}" +
    "div::before{content:'Hidden';display:none}",
    "<div></div>",
    0xFF0891B2u32
)
expect(hidden_before_count).to_equal(0)

step("Suppress generated text with a hidden after box")
val hidden_after_count = _pixel_count(
    "div{color:#0891b2}" +
    "div::after{content:'Hidden';display:none}",
    "<div></div>",
    0xFF0891B2u32
)
expect(hidden_after_count).to_equal(0)
```

</details>

#### should clip a nowrap line with an ellipsis

- Render the bounded ellipsis line
   - Artifact capture: after_step
- Render the unbounded control line
   - Artifact capture: after_step
- Compare visible glyph masks
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = "<div>ThisIsAVeryLongWordThatOverflows</div>"

step("Render the bounded ellipsis line")
val truncated = _pixel_count(
    "div{width:40px;overflow:hidden;white-space:nowrap;" +
    "text-overflow:ellipsis;color:#0f766e;font-size:8px}",
    body,
    0xFF0F766Eu32
)

step("Render the unbounded control line")
val control = _pixel_count(
    "div{width:40px;color:#0f766e;font-size:8px}",
    body,
    0xFF0F766Eu32
)

step("Compare visible glyph masks")
expect(truncated).to_be_less_than(control)
```

</details>

#### should wrap long words with break-all and break-word

- Wrap a break-all word onto the second line
   - Artifact capture: after_step
- Wrap a break-word word onto the second line
   - Artifact capture: after_step
- Keep the first line populated for both wrapping modes
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = "<div>ABCDEFGHIJKLMNOPQRST</div>"
val second_line_row = 14

step("Wrap a break-all word onto the second line")
val break_all_second = _has_color_at_row(
    "div{width:40px;word-break:break-all;" +
    "color:#4338ca;font-size:8px}",
    body,
    0xFF4338CAu32,
    second_line_row
)
expect(break_all_second).to_be(true)

step("Wrap a break-word word onto the second line")
val break_word_second = _has_color_at_row(
    "div{width:40px;overflow-wrap:break-word;" +
    "color:#9333ea;font-size:8px}",
    body,
    0xFF9333EAu32,
    second_line_row
)
expect(break_word_second).to_be(true)

step("Keep the first line populated for both wrapping modes")
val break_all_first = _has_color_at_row(
    "div{width:40px;word-break:break-all;" +
    "color:#4338ca;font-size:8px}",
    body,
    0xFF4338CAu32,
    2
)
expect(break_all_first).to_be(true)
```

</details>

#### should center and right-align short text in an exact block width

- Center the short line inside forty pixels
   - Artifact capture: after_step
- Right-align the short line inside forty pixels
   - Artifact capture: after_step
- Keep both aligned runs on the first text row
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 46 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = "<div>AB</div>"

step("Center the short line inside forty pixels")
val center_ink = _has_color_at(
    "div{width:40px;text-align:center;color:#ea580c;font-size:8px}",
    body,
    0xFFEA580Cu32,
    15,
    2
)
val center_control = _has_color_at(
    "div{width:40px;text-align:center;color:#ea580c;font-size:8px}",
    body,
    0xFFEA580Cu32,
    0,
    2
)
expect(center_ink).to_be(true)
expect(center_control).to_be(false)

step("Right-align the short line inside forty pixels")
val right_ink = _has_color_at(
    "div{width:40px;text-align:right;color:#0d9488;font-size:8px}",
    body,
    0xFF0D9488u32,
    30,
    2
)
val right_control = _has_color_at(
    "div{width:40px;text-align:right;color:#0d9488;font-size:8px}",
    body,
    0xFF0D9488u32,
    0,
    2
)
expect(right_ink).to_be(true)
expect(right_control).to_be(false)

step("Keep both aligned runs on the first text row")
val center_row = _has_color_at_row(
    "div{width:40px;text-align:center;color:#ea580c;font-size:8px}",
    body,
    0xFFEA580Cu32,
    2
)
expect(center_row).to_be(true)
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
