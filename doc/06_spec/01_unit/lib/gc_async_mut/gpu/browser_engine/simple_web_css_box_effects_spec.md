# Simple Web CSS Box Effects Specification

> Focused parser and Draw IR producer evidence for nonuniform border radii and

| Tests | Active | Skipped | Pending |
|-------|-------:|--------:|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web CSS Box Effects Specification

Focused parser and Draw IR producer evidence for nonuniform border radii and

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_css_box_effects_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Focused parser and Draw IR producer evidence for nonuniform border radii and
ordered box-shadow layers.

## Scenarios

### SimpleWebCssBoxEffects

#### should apply cascaded outline offset through Draw IR to CPU pixels

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should apply cascaded outline offset through Draw IR to CPU pixels
- Render a card whose outline offset is declared after the outline shorthand
- Assert the computed offset survives Draw IR and moves the painted outline
   - Expected: _draw_ir_style_value(card, "outline-width") equals `2`
   - Expected: _draw_ir_style_value(card, "outline-offset") equals `3`
   - Expected: _pixel_at(pixels, 32, 3, 3) equals `0xFFEF4444u32`
   - Expected: _pixel_at(pixels, 32, 8, 8) equals `0xFFFFFFFFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should apply cascaded outline offset through Draw IR to CPU pixels")
step("Render a card whose outline offset is declared after the outline shorthand")
val html = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff}" +
    "#card{display:block;margin:8px;width:10px;height:8px;" +
    "background:#ffffff;outline:2px solid #ef4444;outline-offset:3px}" +
    "</style></head><body><div id='card'></div></body></html>"
)
val composition = simple_web_layout_render_html_draw_ir(html, 32, 32)
val card = _draw_ir_command_by_id(composition.batches[0].commands, "card")
val pixels = simple_web_render_html_to_pixels_with_cpu_draw_ir_backend(
    html, 32, 32, "cpu")

step("Assert the computed offset survives Draw IR and moves the painted outline")
expect(_draw_ir_style_value(card, "outline-width")).to_equal("2")
expect(_draw_ir_style_value(card, "outline-offset")).to_equal("3")
expect(_pixel_at(pixels, 32, 3, 3)).to_equal(0xFFEF4444u32)
expect(_pixel_at(pixels, 32, 8, 8)).to_equal(0xFFFFFFFFu32)
```

</details>

#### should preserve bordered gradient text pixels through the CPU Draw IR adapter

- should preserve bordered gradient text pixels through the CPU Draw IR adapter
- Render one clipped web composition through CPU and CPU SIMD
- Keep exact shared-executor pixels after adapter shutdown
   - Expected: cpu.len() equals `32 * 24`
   - Expected: simd.len() equals `32 * 24`
   - Expected: cpu equals `simd`
   - Expected: _pixel_at(cpu, 32, 0, 0) equals `0xFFEF4444u32`
   - Expected: _pixel_at(cpu, 32, 2, 2) equals `0xFF22C55Eu32`
   - Expected: _pixel_at(cpu, 32, 2, 3) equals `0xFF1D4ED8u32`
   - Expected: _pixel_at(cpu, 32, 16, 6) equals `0xFFFFFFFFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should preserve bordered gradient text pixels through the CPU Draw IR adapter")
step("Render one clipped web composition through CPU and CPU SIMD")
val html = (
    "<html><head><style>" +
    "html,body{margin:0;padding:0;background:#ffffff}" +
    "#card{display:block;width:12px;height:12px;border:2px solid " +
    "#ef4444;overflow:hidden;background:#ffffff}" +
    "#gradient{display:block;width:8px;height:2px;" +
    "background-image:linear-gradient(#22c55e,#1d4ed8)}" +
    "#copy{display:block;width:32px;height:8px;color:#111827;" +
    "font-size:8px;white-space:nowrap}" +
    "</style></head><body><section id='card'><div id='gradient'></div>" +
    "<span id='copy'>WIDE TEXT</span></section></body></html>"
)
val cpu = simple_web_render_html_to_pixels_with_cpu_draw_ir_backend(
    html, 32, 24, "cpu")
val simd = simple_web_render_html_to_pixels_with_cpu_draw_ir_backend(
    html, 32, 24, "cpu_simd")
val composition = simple_web_layout_render_html_draw_ir(html, 32, 24)
val copy = _draw_ir_command_by_id(composition.batches[0].commands, "copy")

step("Keep exact shared-executor pixels after adapter shutdown")
expect(cpu.len()).to_equal(32 * 24)
expect(simd.len()).to_equal(32 * 24)
expect(cpu).to_equal(simd)
expect(_pixel_at(cpu, 32, 0, 0)).to_equal(0xFFEF4444u32)
expect(_pixel_at(cpu, 32, 2, 2)).to_equal(0xFF22C55Eu32)
expect(_pixel_at(cpu, 32, 2, 3)).to_equal(0xFF1D4ED8u32)
expect(cpu).to_contain(0xFF111827u32)
expect(copy.clip_rect.present).to_be(true)
expect(_pixel_at(cpu, 32, 16, 6)).to_equal(0xFFFFFFFFu32)
```

</details>

#### parses integer-px border radius shorthand with CSS corner expansion

- parses integer-px border radius shorthand with CSS corner expansion
   - Expected: two.top_left_px equals `12`
   - Expected: two.top_right_px equals `18`
   - Expected: two.bottom_right_px equals `12`
   - Expected: two.bottom_left_px equals `18`
   - Expected: three.top_left_px equals `8`
   - Expected: three.top_right_px equals `12`
   - Expected: three.bottom_right_px equals `20`
   - Expected: three.bottom_left_px equals `12`
   - Expected: four.top_left_px equals `4`
   - Expected: four.top_right_px equals `8`
   - Expected: four.bottom_right_px equals `12`
   - Expected: four.bottom_left_px equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses integer-px border radius shorthand with CSS corner expansion")
val two = parse_border_radius_shorthand("12px 18px")
val three = parse_border_radius_shorthand("8px 12px 20px")
val four = parse_border_radius_shorthand("4px 8px 12px 16px")
val elliptical = parse_border_radius_shorthand("12px / 18px")
val negative = parse_border_radius_shorthand("-1px")

expect(two.valid).to_be(true)
expect(two.top_left_px).to_equal(12)
expect(two.top_right_px).to_equal(18)
expect(two.bottom_right_px).to_equal(12)
expect(two.bottom_left_px).to_equal(18)
expect(three.valid).to_be(true)
expect(three.top_left_px).to_equal(8)
expect(three.top_right_px).to_equal(12)
expect(three.bottom_right_px).to_equal(20)
expect(three.bottom_left_px).to_equal(12)
expect(four.valid).to_be(true)
expect(four.top_left_px).to_equal(4)
expect(four.top_right_px).to_equal(8)
expect(four.bottom_right_px).to_equal(12)
expect(four.bottom_left_px).to_equal(16)
expect(elliptical.valid).to_be(false)
expect(negative.valid).to_be(false)
```

</details>

#### honors authored radius order in dispatch and full declaration paths

- honors authored radius order in dispatch and full declaration paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("honors authored radius order in dispatch and full declaration paths")
val html = (
    "<html><head><style>" +
    ".card{display:block;width:18px;height:12px}" +
    "#dispatch{border-top-left-radius:9px;" +
    "border-radius:1px 2px 3px 4px;" +
    "border-start-end-radius:7px}" +
    "#full{background-color:#1d4ed8;" +
    "border-radius:1px 2px 3px 4px;" +
    "border-start-start-radius:6px;" +
    "border-top-left-radius:8px;" +
    "border-bottom-right-radius:9px;" +
    "border-end-end-radius:5px}" +
    "</style></head><body>" +
    "<section class='card' id='dispatch'></section>" +
    "<section class='card' id='full'></section>" +
    "</body></html>"
)
val composition = simple_web_layout_render_html_draw_ir(html, 64, 48)
val commands = composition.batches[0].commands
val dispatch = _draw_ir_command_by_id(commands, "dispatch")
val full = _draw_ir_command_by_id(commands, "full")

expect(_draw_ir_style_value(
    dispatch, "border-top-left-radius")).to_equal("1")
expect(_draw_ir_style_value(
    dispatch, "border-top-right-radius")).to_equal("7")
expect(_draw_ir_style_value(
    dispatch, "border-bottom-right-radius")).to_equal("3")
expect(_draw_ir_style_value(
    dispatch, "border-bottom-left-radius")).to_equal("4")
expect(_draw_ir_style_value(
    full, "border-top-left-radius")).to_equal("8")
expect(_draw_ir_style_value(
    full, "border-top-right-radius")).to_equal("2")
expect(_draw_ir_style_value(
    full, "border-bottom-right-radius")).to_equal("5")
expect(_draw_ir_style_value(
    full, "border-bottom-left-radius")).to_equal("4")
```

</details>

#### projects no-shadow 2 3 and 4 value radii independently in Draw IR

- projects no-shadow 2 3 and 4 value radii independently in Draw IR


<details>
<summary>Executable SSpec</summary>

Runnable source: 60 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("projects no-shadow 2 3 and 4 value radii independently in Draw IR")
val html = (
    "<html><head><style>" +
    ".card{display:block;width:18px;height:12px}" +
    "#dispatch-two{border-radius:12px 18px}" +
    "#full-three{background-color:#1d4ed8;" +
    "border-radius:8px 12px 20px}" +
    "#dispatch-four{border-radius:4px 8px 12px 16px}" +
    "</style></head><body>" +
    "<section class='card' id='dispatch-two'></section>" +
    "<section class='card' id='full-three'></section>" +
    "<section class='card' id='dispatch-four'></section>" +
    "</body></html>"
)
val composition = simple_web_layout_render_html_draw_ir(html, 64, 64)
val commands = composition.batches[0].commands
val two = _draw_ir_command_by_id(commands, "dispatch-two")
val three = _draw_ir_command_by_id(commands, "full-three")
val four = _draw_ir_command_by_id(commands, "dispatch-four")

expect(_draw_ir_style_value(
    two, "border-top-left-radius")).to_equal("12")
expect(_draw_ir_style_value(
    two, "border-top-right-radius")).to_equal("18")
expect(_draw_ir_style_value(
    two, "border-bottom-right-radius")).to_equal("12")
expect(_draw_ir_style_value(
    two, "border-bottom-left-radius")).to_equal("18")
expect(_draw_ir_style_value(
    three, "border-top-left-radius")).to_equal("8")
expect(_draw_ir_style_value(
    three, "border-top-right-radius")).to_equal("12")
expect(_draw_ir_style_value(
    three, "border-bottom-right-radius")).to_equal("20")
expect(_draw_ir_style_value(
    three, "border-bottom-left-radius")).to_equal("12")
expect(_draw_ir_style_value(
    four, "border-top-left-radius")).to_equal("4")
expect(_draw_ir_style_value(
    four, "border-top-right-radius")).to_equal("8")
expect(_draw_ir_style_value(
    four, "border-bottom-right-radius")).to_equal("12")
expect(_draw_ir_style_value(
    four, "border-bottom-left-radius")).to_equal("16")
expect(_draw_ir_style_value(
    two, "box-shadow-layer-schema")).to_equal(
        "web-box-shadow-layers-v1")
expect(_draw_ir_style_value(
    two, "box-shadow-layer-count")).to_equal("0")
expect(_draw_ir_style_value(
    three, "box-shadow-layer-schema")).to_equal(
        "web-box-shadow-layers-v1")
expect(_draw_ir_style_value(
    three, "box-shadow-layer-count")).to_equal("0")
expect(_draw_ir_style_value(
    four, "box-shadow-layer-schema")).to_equal(
        "web-box-shadow-layers-v1")
expect(_draw_ir_style_value(
    four, "box-shadow-layer-count")).to_equal("0")
```

</details>

#### parses ordered Aetheric outer and inset box shadow layers

- parses ordered Aetheric outer and inset box shadow layers
   - Expected: parsed.layers.len() equals `2`
   - Expected: parsed.layers[0].kind equals `outer`
   - Expected: parsed.layers[0].offset_x_px equals `0`
   - Expected: parsed.layers[0].offset_y_px equals `18`
   - Expected: parsed.layers[0].blur_radius_px equals `46`
   - Expected: parsed.layers[0].spread_radius_px equals `0`
   - Expected: parsed.layers[0].color_rgba equals `0x57000000u32`
   - Expected: parsed.layers[1].kind equals `inset`
   - Expected: parsed.layers[1].offset_x_px equals `0`
   - Expected: parsed.layers[1].offset_y_px equals `1`
   - Expected: parsed.layers[1].blur_radius_px equals `1`
   - Expected: parsed.layers[1].spread_radius_px equals `0`
   - Expected: parsed.layers[1].color_rgba equals `0x1AFFFFFFu32`
   - Expected: current.layers[0].offset_y_px equals `-3`
   - Expected: current.layers[0].color_rgba equals `0xFFADC6FFu32`
   - Expected: malformed.layers.len() equals `0`
   - Expected: none.layers.len() equals `0`
   - Expected: empty.layers.len() equals `0`
   - Expected: transparent.layers[0].color_rgba equals `0u32`
   - Expected: zero_alpha.layers[0].color_rgba equals `0u32`
   - Expected: zero_alpha_hex.layers[0].color_rgba equals `0u32`
   - Expected: boundary.layers[0].offset_x_px equals `1000000`
   - Expected: boundary.layers[0].offset_y_px equals `-1000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 92 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses ordered Aetheric outer and inset box shadow layers")
val parsed = parse_box_shadow_layers(
    "0 18px 46px rgba(0,0,0,0.34), " +
    "inset 0 1px 1px rgba(255,255,255,0.10)",
    0xFFADC6FFu32
)
val current = parse_box_shadow_layers(
    "2px -3px currentcolor", 0xFFADC6FFu32)
val malformed = parse_box_shadow_layers(
    "0 2px -4px rgba(0,0,0,0.4)", 0xFFADC6FFu32)
val none = parse_box_shadow_layers("none", 0xFFADC6FFu32)
val empty = parse_box_shadow_layers("", 0xFFADC6FFu32)
val transparent = parse_box_shadow_layers(
    "0 1px transparent", 0xFFADC6FFu32)
val zero_alpha = parse_box_shadow_layers(
    "0 1px rgba(0,0,0,0)", 0xFFADC6FFu32)
val zero_alpha_hex = parse_box_shadow_layers(
    "0 1px #0000", 0xFFADC6FFu32)
val exact_alpha_hex = parse_box_shadow_layers(
    "0 1px #11223344", 0xFFADC6FFu32)
val boundary = parse_box_shadow_layers(
    "1000000px -1000000px black", 0xFFADC6FFu32)
val oversized_positive = parse_box_shadow_layers(
    "1000001px 0 black", 0xFFADC6FFu32)
val oversized_negative = parse_box_shadow_layers(
    "0 -1000001px black", 0xFFADC6FFu32)
val overflow_positive = parse_box_shadow_layers(
    "999999999999999999999px 0 black", 0xFFADC6FFu32)
val overflow_negative = parse_box_shadow_layers(
    "0 -999999999999999999999px black", 0xFFADC6FFu32)
val malformed_hex = parse_box_shadow_layers(
    "0 1px #12gg00", 0xFFADC6FFu32)
val overlong_hex = parse_box_shadow_layers(
    "0 1px #000000000", 0xFFADC6FFu32)
val malformed_rgb = parse_box_shadow_layers(
    "0 1px rgb(0,0)", 0xFFADC6FFu32)
val malformed_rgba = parse_box_shadow_layers(
    "0 1px rgba(0,0,0)", 0xFFADC6FFu32)
val overlong_rgba = parse_box_shadow_layers(
    "0 1px rgba(0,0,0,0,1)", 0xFFADC6FFu32)
val ranged_rgb = parse_box_shadow_layers(
    "0 1px rgb(256,0,0)", 0xFFADC6FFu32)
val ranged_alpha = parse_box_shadow_layers(
    "0 1px rgba(0,0,0,1.1)", 0xFFADC6FFu32)

expect(parsed.valid).to_be(true)
expect(parsed.layers.len()).to_equal(2)
expect(parsed.layers[0].kind).to_equal("outer")
expect(parsed.layers[0].offset_x_px).to_equal(0)
expect(parsed.layers[0].offset_y_px).to_equal(18)
expect(parsed.layers[0].blur_radius_px).to_equal(46)
expect(parsed.layers[0].spread_radius_px).to_equal(0)
expect(parsed.layers[0].color_rgba).to_equal(0x57000000u32)
expect(parsed.layers[1].kind).to_equal("inset")
expect(parsed.layers[1].offset_x_px).to_equal(0)
expect(parsed.layers[1].offset_y_px).to_equal(1)
expect(parsed.layers[1].blur_radius_px).to_equal(1)
expect(parsed.layers[1].spread_radius_px).to_equal(0)
expect(parsed.layers[1].color_rgba).to_equal(0x1AFFFFFFu32)
expect(current.valid).to_be(true)
expect(current.layers[0].offset_y_px).to_equal(-3)
expect(current.layers[0].color_rgba).to_equal(0xFFADC6FFu32)
expect(malformed.valid).to_be(false)
expect(malformed.layers.len()).to_equal(0)
expect(none.valid).to_be(true)
expect(none.layers.len()).to_equal(0)
expect(empty.valid).to_be(true)
expect(empty.layers.len()).to_equal(0)
expect(transparent.valid).to_be(true)
expect(transparent.layers[0].color_rgba).to_equal(0u32)
expect(zero_alpha.valid).to_be(true)
expect(zero_alpha.layers[0].color_rgba).to_equal(0u32)
expect(zero_alpha_hex.valid).to_be(true)
expect(zero_alpha_hex.layers[0].color_rgba).to_equal(0u32)
expect(exact_alpha_hex.valid).to_be(true)
expect(exact_alpha_hex.layers[0].color_rgba).to_equal(
    0x44112233u32)
expect(boundary.valid).to_be(true)
expect(boundary.layers[0].offset_x_px).to_equal(1000000)
expect(boundary.layers[0].offset_y_px).to_equal(-1000000)
expect(oversized_positive.valid).to_be(false)
expect(oversized_negative.valid).to_be(false)
expect(overflow_positive.valid).to_be(false)
expect(overflow_negative.valid).to_be(false)
expect(malformed_hex.valid).to_be(false)
expect(overlong_hex.valid).to_be(false)
expect(malformed_rgb.valid).to_be(false)
expect(malformed_rgba.valid).to_be(false)
expect(overlong_rgba.valid).to_be(false)
expect(ranged_rgb.valid).to_be(false)
expect(ranged_alpha.valid).to_be(false)
```

</details>

#### projects exact Aetheric shadow layers into Draw IR schema fields

- projects exact Aetheric shadow layers into Draw IR schema fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 57 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("projects exact Aetheric shadow layers into Draw IR schema fields")
val html = (
    "<html><body>" +
    "<section id='aetheric' style='display:block;width:12px;" +
    "height:8px;color:#adc6ff;box-shadow:" +
    "0 18px 46px rgba(0,0,0,0.34), " +
    "inset 0 1px 1px rgba(255,255,255,0.10)'></section>" +
    "<section id='malformed' style='display:block;width:12px;" +
    "height:8px;box-shadow:0 2px -4px " +
    "rgba(0,0,0,0.4)'></section>" +
    "<section id='none' style='display:block;width:12px;" +
    "height:8px;box-shadow:none'></section>" +
    "</body></html>"
)
val composition = simple_web_layout_render_html_draw_ir(html, 64, 48)
val commands = composition.batches[0].commands
val aetheric = _draw_ir_command_by_id(commands, "aetheric")
val malformed = _draw_ir_command_by_id(commands, "malformed")
val none = _draw_ir_command_by_id(commands, "none")

expect(_draw_ir_style_value(
    aetheric, "box-shadow-layer-schema")).to_equal(
        "web-box-shadow-layers-v1")
expect(_draw_ir_style_value(
    aetheric, "box-shadow-layer-count")).to_equal("2")
expect(_draw_ir_style_value(
    aetheric, "box-shadow-layer-0-kind")).to_equal("outer")
expect(_draw_ir_style_value(
    aetheric, "box-shadow-layer-0-offset-x")).to_equal("0")
expect(_draw_ir_style_value(
    aetheric, "box-shadow-layer-0-offset-y")).to_equal("18")
expect(_draw_ir_style_value(
    aetheric, "box-shadow-layer-0-blur-radius")).to_equal("46")
expect(_draw_ir_style_value(
    aetheric, "box-shadow-layer-0-spread-radius")).to_equal("0")
expect(_draw_ir_style_value(
    aetheric, "box-shadow-layer-0-color")).to_equal("1459617792")
expect(_draw_ir_style_value(
    aetheric, "box-shadow-layer-1-kind")).to_equal("inset")
expect(_draw_ir_style_value(
    aetheric, "box-shadow-layer-1-offset-x")).to_equal("0")
expect(_draw_ir_style_value(
    aetheric, "box-shadow-layer-1-offset-y")).to_equal("1")
expect(_draw_ir_style_value(
    aetheric, "box-shadow-layer-1-blur-radius")).to_equal("1")
expect(_draw_ir_style_value(
    aetheric, "box-shadow-layer-1-spread-radius")).to_equal("0")
expect(_draw_ir_style_value(
    aetheric, "box-shadow-layer-1-color")).to_equal("452984831")
expect(_draw_ir_style_value(
    malformed, "box-shadow-layer-schema")).to_equal("")
expect(_draw_ir_style_value(
    none, "box-shadow-layer-schema")).to_equal(
        "web-box-shadow-layers-v1")
expect(_draw_ir_style_value(
    none, "box-shadow-layer-count")).to_equal("0")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-WEB-BROWSER-003`
- `REQ-WEB-BROWSER-004`
- `REQ-WEB-BROWSER-021`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d22ab28c09faced545a45750fcdb05602d85adcbb34b4234e4f68f717498549b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d22ab28c09faced545a45750fcdb05602d85adcbb34b4234e4f68f717498549b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d22ab28c09faced545a45750fcdb05602d85adcbb34b4234e4f68f717498549b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **79/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_css_box_effects_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_css_box_effects_spec.md (current)
findings: 9 blockers: 1
  narrative=100 structure=90 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=79; blocker cap makes effective=49
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_css_box_effects_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_css_box_effects_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_css_box_effects_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 27 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_css_box_effects_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 4 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_css_box_effects_spec.spl:51:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should apply cascaded outline offset through Draw IR to CPU pixels' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_css_box_effects_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should apply cascaded outline offset through Draw IR to CPU pixels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_css_box_effects_spec.spl:74:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve bordered gradient text pixels through the CPU Draw IR adapter' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_css_box_effects_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve bordered gradient text pixels through the CPU Draw IR adapter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_css_box_effects_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses integer-px border radius shorthand with CSS corner expansion' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
