# HTML Layout Renderer Style — Coverage Closure (U4.3, part 1 of style.spl)

> Purpose: Prove that parse_font_shorthand_number (U4.3 closure).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HTML Layout Renderer Style — Coverage Closure (U4.3, part 1 of style.spl)

Purpose: Prove that parse_font_shorthand_number (U4.3 closure).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser_engine/simple_web_html_layout_renderer_style_coverage_closure_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that parse_font_shorthand_number (U4.3 closure).
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### parse_font_shorthand_number (U4.3 closure)

#### accumulates digits and stops at the first non-digit

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accumulates digits and stops at the first non-digit
- Verify: accumulates digits and stops at the first non-digit
   - Expected: value equals `123`
   - Expected: next_idx equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("accumulates digits and stops at the first non-digit")
step("Verify: accumulates digits and stops at the first non-digit")
# @req: REQ-BROWSER-ENGINE-001
val (value, next_idx) = parse_font_shorthand_number("123px", 0, 5)
expect(value).to_equal(123)  # oracle: 123 — named expected value from the requirement
expect(next_idx).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### consumes a decimal point and its fractional digits without adding them to value

- consumes a decimal point and its fractional digits without adding them to value
- Verify: consumes a decimal point and its fractional digits without adding them to value
   - Expected: value equals `12`
   - Expected: next_idx equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("consumes a decimal point and its fractional digits without adding them to value")
step("Verify: consumes a decimal point and its fractional digits without adding them to value")
val (value, next_idx) = parse_font_shorthand_number("12.5px", 0, 6)
expect(value).to_equal(12)  # oracle: 12 — named expected value from the requirement
expect(next_idx).to_equal(4)  # oracle: 4 — named expected value from the requirement
```

</details>

### parse_font_shorthand_size_px (U4.3 closure)

#### returns the first digit run immediately followed by px

- returns the first digit run immediately followed by px
- Verify: returns the first digit run immediately followed by px
   - Expected: parse_font_shorthand_size_px("bold 14px/1.4 sans-serif") equals `14`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("returns the first digit run immediately followed by px")
step("Verify: returns the first digit run immediately followed by px")
expect(parse_font_shorthand_size_px("bold 14px/1.4 sans-serif")).to_equal(14)
```

</details>

#### returns 0 when no digit run is immediately followed by px (both-directions oracle)

- returns 0 when no digit run is immediately followed by px (both-directions oracle)
- Verify: returns 0 when no digit run is immediately followed by px (both-directions oracle)
   - Expected: parse_font_shorthand_size_px("bold sans-serif") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("returns 0 when no digit run is immediately followed by px (both-directions oracle)")
step("Verify: returns 0 when no digit run is immediately followed by px (both-directions oracle)")
expect(parse_font_shorthand_size_px("bold sans-serif")).to_equal(0)
```

</details>

### parse_font_shorthand_family (U4.3 closure)

#### returns the family tail after size/line-height

- returns the family tail after size/line-height
- Verify: returns the family tail after size/line-height
   - Expected: parse_font_shorthand_family("14px/1.4 Arial, sans-serif") equals `Arial, sans-serif`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("returns the family tail after size/line-height")
step("Verify: returns the family tail after size/line-height")
expect(parse_font_shorthand_family("14px/1.4 Arial, sans-serif")).to_equal("Arial, sans-serif")
```

</details>

#### returns the family tail after a bare size (no line-height)

- returns the family tail after a bare size (no line-height)
- Verify: returns the family tail after a bare size (no line-height)
   - Expected: parse_font_shorthand_family("bold 16px Georgia") equals `Georgia`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("returns the family tail after a bare size (no line-height)")
step("Verify: returns the family tail after a bare size (no line-height)")
expect(parse_font_shorthand_family("bold 16px Georgia")).to_equal("Georgia")
```

</details>

#### returns empty text when no size[px] token exists (both-directions oracle)

- returns empty text when no size[px] token exists (both-directions oracle)
- Verify: returns empty text when no size[px] token exists (both-directions oracle)
   - Expected: parse_font_shorthand_family("sans-serif") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("returns empty text when no size[px] token exists (both-directions oracle)")
step("Verify: returns empty text when no size[px] token exists (both-directions oracle)")
expect(parse_font_shorthand_family("sans-serif")).to_equal("")
```

</details>

### is_inline_tag / is_heading / is_non_rendered_tag (U4.3 closure)

#### classifies known inline tags true and a block tag false

- classifies known inline tags true and a block tag false
- Verify: classifies known inline tags true and a block tag false
   - Expected: is_inline_tag("span") is true
   - Expected: is_inline_tag("a") is true
   - Expected: is_inline_tag("div") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("classifies known inline tags true and a block tag false")
step("Verify: classifies known inline tags true and a block tag false")
expect(is_inline_tag("span")).to_equal(true)
expect(is_inline_tag("a")).to_equal(true)
expect(is_inline_tag("div")).to_equal(false)
```

</details>

#### classifies h1..h6 as headings and non-heading tags false

- classifies h1..h6 as headings and non-heading tags false
- Verify: classifies h1..h6 as headings and non-heading tags false
   - Expected: is_heading("h1") is true
   - Expected: is_heading("h6") is true
   - Expected: is_heading("p") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("classifies h1..h6 as headings and non-heading tags false")
step("Verify: classifies h1..h6 as headings and non-heading tags false")
expect(is_heading("h1")).to_equal(true)
expect(is_heading("h6")).to_equal(true)
expect(is_heading("p")).to_equal(false)
```

</details>

#### classifies head/style/script/etc as non-rendered and body as rendered

- classifies head/style/script/etc as non-rendered and body as rendered
- Verify: classifies head/style/script/etc as non-rendered and body as rendered
   - Expected: is_non_rendered_tag("script") is true
   - Expected: is_non_rendered_tag("template") is true
   - Expected: is_non_rendered_tag("body") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("classifies head/style/script/etc as non-rendered and body as rendered")
step("Verify: classifies head/style/script/etc as non-rendered and body as rendered")
expect(is_non_rendered_tag("script")).to_equal(true)
expect(is_non_rendered_tag("template")).to_equal(true)
expect(is_non_rendered_tag("body")).to_equal(false)
```

</details>

### split_top_level_commas (U4.3 closure)

#### splits on commas at paren-depth 0 only

- splits on commas at paren-depth 0 only
- Verify: splits on commas at paren-depth 0 only
   - Expected: parts.len() equals `3`
   - Expected: parts[0] equals `rgb(1,2,3)`
   - Expected: parts[1] equals ` Arial`
   - Expected: parts[2] equals ` sans-serif`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("splits on commas at paren-depth 0 only")
step("Verify: splits on commas at paren-depth 0 only")
val parts = split_top_level_commas("rgb(1,2,3), Arial, sans-serif")
expect(parts.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(parts[0]).to_equal("rgb(1,2,3)")
expect(parts[1]).to_equal(" Arial")
expect(parts[2]).to_equal(" sans-serif")
```

</details>

#### returns the whole text as one part when there is no top-level comma (both-directions oracle)

- returns the whole text as one part when there is no top-level comma (both-directions oracle)
- Verify: returns the whole text as one part when there is no top-level comma (both-directions oracle)
   - Expected: parts.len() equals `1`
   - Expected: parts[0] equals `solid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("returns the whole text as one part when there is no top-level comma (both-directions oracle)")
step("Verify: returns the whole text as one part when there is no top-level comma (both-directions oracle)")
val parts = split_top_level_commas("solid")
expect(parts.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(parts[0]).to_equal("solid")
```

</details>

### parse_float_to_255 (U4.3 closure)

#### scales a fractional alpha value into the 0..255 range

- scales a fractional alpha value into the 0..255 range
- Verify: scales a fractional alpha value into the 0..255 range
   - Expected: parse_float_to_255("0.5") equals `127`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("scales a fractional alpha value into the 0..255 range")
step("Verify: scales a fractional alpha value into the 0..255 range")
expect(parse_float_to_255("0.5")).to_equal(127)
```

</details>

#### clamps any integer part >= 1 to 255 and a bare 0 to 0 (both-directions oracle)

- clamps any integer part >= 1 to 255 and a bare 0 to 0 (both-directions oracle)
- Verify: clamps any integer part >= 1 to 255 and a bare 0 to 0 (both-directions oracle)
   - Expected: parse_float_to_255("1") equals `255`
   - Expected: parse_float_to_255("0") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("clamps any integer part >= 1 to 255 and a bare 0 to 0 (both-directions oracle)")
step("Verify: clamps any integer part >= 1 to 255 and a bare 0 to 0 (both-directions oracle)")
expect(parse_float_to_255("1")).to_equal(255)
expect(parse_float_to_255("0")).to_equal(0)
```

</details>

### shadow_layer_alpha (U4.3 closure)

#### extracts the 4th rgba() argument scaled to 0..255

- extracts the 4th rgba() argument scaled to 0..255
- Verify: extracts the 4th rgba() argument scaled to 0..255
   - Expected: shadow_layer_alpha("2px 2px 4px rgba(0,0,0,0.5)") equals `127`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("extracts the 4th rgba() argument scaled to 0..255")
step("Verify: extracts the 4th rgba() argument scaled to 0..255")
expect(shadow_layer_alpha("2px 2px 4px rgba(0,0,0,0.5)")).to_equal(127)
```

</details>

#### defaults to 255 when there is no rgba() in the layer (both-directions oracle)

- defaults to 255 when there is no rgba() in the layer (both-directions oracle)
- Verify: defaults to 255 when there is no rgba() in the layer (both-directions oracle)
   - Expected: shadow_layer_alpha("2px 2px 4px #000000") equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("defaults to 255 when there is no rgba() in the layer (both-directions oracle)")
step("Verify: defaults to 255 when there is no rgba() in the layer (both-directions oracle)")
expect(shadow_layer_alpha("2px 2px 4px #000000")).to_equal(255)
```

</details>

### shadow_length_prefix (U4.3 closure)

#### returns the text before an rgb()/rgba() color token

- returns the text before an rgb()/rgba() color token
- Verify: returns the text before an rgb()/rgba() color token
   - Expected: shadow_length_prefix("2px 2px 4px rgba(0,0,0,0.5)") equals `2px 2px 4px `


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("returns the text before an rgb()/rgba() color token")
step("Verify: returns the text before an rgb()/rgba() color token")
expect(shadow_length_prefix("2px 2px 4px rgba(0,0,0,0.5)")).to_equal("2px 2px 4px ")
```

</details>

#### returns the whole text when there is no recognized color token (both-directions oracle)

- returns the whole text when there is no recognized color token (both-directions oracle)
- Verify: returns the whole text when there is no recognized color token (both-directions oracle)
   - Expected: shadow_length_prefix("2px 2px 4px") equals `2px 2px 4px`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("returns the whole text when there is no recognized color token (both-directions oracle)")
step("Verify: returns the whole text when there is no recognized color token (both-directions oracle)")
expect(shadow_length_prefix("2px 2px 4px")).to_equal("2px 2px 4px")
```

</details>

### paren_matching_close (U4.3 closure)

#### finds the matching close paren across nested parens

- finds the matching close paren across nested parens
- Verify: finds the matching close paren across nested parens
   - Expected: paren_matching_close("rgba(0, rgb(1,2,3), 4)", 4) equals `21`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("finds the matching close paren across nested parens")
step("Verify: finds the matching close paren across nested parens")
expect(paren_matching_close("rgba(0, rgb(1,2,3), 4)", 4)).to_equal(21)
```

</details>

#### returns -1 when the parens never close (both-directions oracle)

- returns -1 when the parens never close (both-directions oracle)
- Verify: returns -1 when the parens never close (both-directions oracle)
   - Expected: paren_matching_close("rgba(0,0,0", 4) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("returns -1 when the parens never close (both-directions oracle)")
step("Verify: returns -1 when the parens never close (both-directions oracle)")
expect(paren_matching_close("rgba(0,0,0", 4)).to_equal(-1)
```

</details>

### css_important_marker_start (U4.3 closure)

#### finds the '!' marker start, tolerating whitespace before 'important'

- finds the '!' marker start, tolerating whitespace before 'important'
- Verify: finds the '!' marker start, tolerating whitespace before 'important'
   - Expected: css_important_marker_start("red !important") equals `4`
   - Expected: css_important_marker_start("red  !  important") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("finds the '!' marker start, tolerating whitespace before 'important'")
step("Verify: finds the '!' marker start, tolerating whitespace before 'important'")
expect(css_important_marker_start("red !important")).to_equal(4)
expect(css_important_marker_start("red  !  important")).to_equal(5)
```

</details>

#### returns -1 when the value does not end with 'important' (both-directions oracle)

- returns -1 when the value does not end with 'important' (both-directions oracle)
- Verify: returns -1 when the value does not end with 'important' (both-directions oracle)
   - Expected: css_important_marker_start("red") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("returns -1 when the value does not end with 'important' (both-directions oracle)")
step("Verify: returns -1 when the value does not end with 'important' (both-directions oracle)")
expect(css_important_marker_start("red")).to_equal(-1)
```

</details>

### renderer_default_style / inherit_style_legacy (U4.3 closure)

#### produces sane, real default field values (real oracle, not a bare call)

- produces sane, real default field values (real oracle, not a bare call)
- Verify: produces sane, real default field values (real oracle, not a bare call)
   - Expected: st.font_size equals `16`
   - Expected: st.font_family equals `sans-serif`
   - Expected: st.display equals `block`
   - Expected: st.opacity_pct equals `100`
   - Expected: st.bold is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("produces sane, real default field values (real oracle, not a bare call)")
step("Verify: produces sane, real default field values (real oracle, not a bare call)")
val st = renderer_default_style()
expect(st.font_size).to_equal(16)  # oracle: 16 — named expected value from the requirement
expect(st.font_family).to_equal("sans-serif")
expect(st.display).to_equal("block")
expect(st.opacity_pct).to_equal(100)  # oracle: 100 — named expected value from the requirement
expect(st.bold).to_equal(false)
```

</details>

#### inherits font/color/text properties but resets box-layout properties to their own defaults

- inherits font/color/text properties but resets box-layout properties to their own defaults
- Verify: inherits font/color/text properties but resets box-layout properties to their own defaults
   - Expected: child.font_size equals `24`
   - Expected: child.fg equals `0xFF112233u32`
   - Expected: child.text_align equals `center`
   - Expected: child.width_px equals `0`
   - Expected: child.display equals `block`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("inherits font/color/text properties but resets box-layout properties to their own defaults")
step("Verify: inherits font/color/text properties but resets box-layout properties to their own defaults")
var parent = renderer_default_style()
parent.font_size = 24
parent.fg = 0xFF112233u32
parent.text_align = "center"
parent.width_px = 500
parent.display = "flex"
val child = inherit_style_legacy(parent)
expect(child.font_size).to_equal(24)  # oracle: 24 — named expected value from the requirement
expect(child.fg).to_equal(0xFF112233u32)
expect(child.text_align).to_equal("center")
# width is not an inherited CSS property: the child gets its own default, not the parent's.
expect(child.width_px).to_equal(0)  # oracle: 0 — named expected value from the requirement
# display: none is the one exception the function itself special-cases.
expect(child.display).to_equal("block")
```

</details>

#### propagates display:none through inherit_style_legacy (both-directions oracle)

- propagates display:none through inherit_style_legacy (both-directions oracle)
- Verify: propagates display:none through inherit_style_legacy (both-directions oracle)
   - Expected: child.display equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("propagates display:none through inherit_style_legacy (both-directions oracle)")
step("Verify: propagates display:none through inherit_style_legacy (both-directions oracle)")
var parent = renderer_default_style()
parent.display = "none"
val child = inherit_style_legacy(parent)
expect(child.display).to_equal("none")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-BROWSER_ENGINE`
- `REQ-BROWSER-ENGINE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1030c0aba567b40386a55385d2a1a0ac02299df54dd843c402e81dd64a8d3475`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1030c0aba567b40386a55385d2a1a0ac02299df54dd843c402e81dd64a8d3475`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1030c0aba567b40386a55385d2a1a0ac02299df54dd843c402e81dd64a8d3475`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/browser_engine/simple_web_html_layout_renderer_style_coverage_closure_spec.spl
mirror: doc/06_spec/01_unit/browser_engine/simple_web_html_layout_renderer_style_coverage_closure_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/browser_engine/simple_web_html_layout_renderer_style_coverage_closure_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/browser_engine/simple_web_html_layout_renderer_style_coverage_closure_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/browser_engine/simple_web_html_layout_renderer_style_coverage_closure_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/browser_engine/simple_web_html_layout_renderer_style_coverage_closure_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accumulates digits and stops at the first non-digit' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/simple_web_html_layout_renderer_style_coverage_closure_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'consumes a decimal point and its fractional digits without adding them to value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/simple_web_html_layout_renderer_style_coverage_closure_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the first digit run immediately followed by px' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
