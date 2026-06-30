# Simple Web Generated HTML/CSS Combinations Specification

> This focused spec covers common generated GUI HTML/CSS combinations against the pure Simple Web renderer. It complements the broad renderer spec without adding more runtime to that already-large file.

<!-- sdn-diagram:id=simple_web_generated_html_css_combinations_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_web_generated_html_css_combinations_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_web_generated_html_css_combinations_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_web_generated_html_css_combinations_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web Generated HTML/CSS Combinations Specification

This focused spec covers common generated GUI HTML/CSS combinations against the pure Simple Web renderer. It complements the broad renderer spec without adding more runtime to that already-large file.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/sys_test/html_css_spec_traceability.md |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Research | doc/03_plan/sys_test/html_css_spec_traceability.md |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_generated_html_css_combinations_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This focused spec covers common generated GUI HTML/CSS combinations against the
pure Simple Web renderer. It complements the broad renderer spec without adding
more runtime to that already-large file.

**Plan:** doc/03_plan/sys_test/html_css_spec_traceability.md

**Design:** doc/04_architecture/ui/simple_gui_stack.md

**Research:** doc/03_plan/sys_test/html_css_spec_traceability.md

**Requirements:** N/A

## Syntax

The spec uses `std.spec` scenarios and direct pixel-color assertions. Each
scenario renders generated HTML/CSS through `simple_web_render_html_to_pixels`
and asserts colors that can only appear when the relevant tag group and CSS
declarations participate in the render path.

## Examples

- semantic generated GUI shell: `main`, `header`, `button`, `span`, `section`
  with flex, padding, border, background, color, and text styles;
- generated form shell: `form`, `fieldset`, `legend`, `label`, `input`,
  `select`, `option`, `selectedcontent`, and `progress` with grouped selectors;
- generated media shell: `canvas`, `picture`, `source`, `img`, `video`,
  `object`, and fallback text with overflow and box styling.

## Scenarios

### Simple Web generated HTML/CSS combinations

#### renders generated GUI semantic panels with flex, padding, border, and text styles

- Render a generated GUI shell composed from semantic HTML tags and CSS layout properties
- Assert the generated semantic container and CSS colors produce visible pixels
   - Expected: pixels.len() equals `120 * 80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render a generated GUI shell composed from semantic HTML tags and CSS layout properties")
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}.app{display:flex;flex-direction:column;width:90px;height:54px;padding:3px;border:2px solid #0f172a;background-color:#e0f2fe;background-attachment:fixed;color:#111827;font-size:8px}.bar{display:flex;gap:2px;background-color:#1d4ed8;color:#ffffff;padding:1px}.content{display:block;margin-top:2px;background-color:#dcfce7;width:70px;height:20px}</style></head><body><main id='app' class='app'><header class='bar'><button>Run</button><span>Status</span></header><section class='content'>Ready</section></main></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 120, 80)

step("Assert the generated semantic container and CSS colors produce visible pixels")
expect(pixels.len()).to_equal(120 * 80)
expect(_count_color(pixels, 0xFFE0F2FEu32)).to_be_greater_than(0)
expect(_count_color(pixels, 0xFF1D4ED8u32)).to_be_greater_than(0)
expect(_count_color(pixels, 0xFFDCFCE7u32)).to_be_greater_than(0)
```

</details>

#### renders generated form control combinations with fieldset, label, input, select, and progress

- Render form-oriented generated HTML with common CSS box properties
- Assert form control tags and shared CSS selectors contribute visible styled output
   - Expected: pixels.len() equals `128 * 72`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render form-oriented generated HTML with common CSS box properties")
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}fieldset{display:block;width:96px;height:44px;padding:3px;border:1px solid #334155;background-color:#f8fafc}label{display:block;color:#111827;font-size:8px}input,select,progress{display:block;width:60px;height:8px;margin-top:2px;background-color:#fde68a;color:#111827}</style></head><body><form><fieldset><legend>Prefs</legend><label>Name<input value='Ada'></label><select><option>One</option><selectedcontent></selectedcontent></select><progress value='1' max='2'></progress></fieldset></form></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 128, 72)

step("Assert form control tags and shared CSS selectors contribute visible styled output")
expect(pixels.len()).to_equal(128 * 72)
expect(_count_color(pixels, 0xFFF8FAFCu32)).to_be_greater_than(0)
expect(_count_color(pixels, 0xFFFDE68Au32)).to_be_greater_than(0)
expect(_count_color(pixels, 0xFF334155u32)).to_be_greater_than(0)
```

</details>

#### renders generated media and canvas placeholders with overflow and object box styles

- Render media-oriented generated HTML using canvas, picture, img, video, and object placeholders
- Assert mixed media placeholder tags and CSS overflow/background styling render
   - Expected: pixels.len() equals `128 * 72`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render media-oriented generated HTML using canvas, picture, img, video, and object placeholders")
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}.stage{display:block;width:104px;height:56px;overflow:hidden;background-color:#f1f5f9}.tile{display:inline;width:20px;height:16px;margin:2px;background-color:#c4b5fd;border:1px solid #4c1d95}.fallback{display:block;width:80px;height:12px;background-color:#fed7aa;color:#111827;font-size:8px}</style></head><body><section class='stage'><canvas class='tile'></canvas><picture><source srcset='x'><img class='tile' alt='image'></picture><video class='tile'></video><object class='tile'></object><div class='fallback'>media fallback</div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 128, 72)

step("Assert mixed media placeholder tags and CSS overflow/background styling render")
expect(pixels.len()).to_equal(128 * 72)
expect(_count_color(pixels, 0xFFF1F5F9u32)).to_be_greater_than(0)
expect(_count_color(pixels, 0xFFC4B5FDu32)).to_be_greater_than(0)
expect(_count_color(pixels, 0xFFFED7AAu32)).to_be_greater_than(0)
```

</details>

#### renders place-content shorthand through flex alignment

- Render a flex container using place-content as the align-content and justify-content shorthand
- Assert place-content:center moves the flex child away from the start edge
   - Expected: pixels.len() equals `120 * 48`
   - Expected: _pixel_at(pixels, 120, 5, 6) equals `0xFFDBEAFEu32`
   - Expected: _pixel_at(pixels, 120, 50, 6) equals `0xFFEF4444u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render a flex container using place-content as the align-content and justify-content shorthand")
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}.stage{display:flex;width:100px;height:24px;place-content:center;background-color:#dbeafe}.chip{width:20px;height:12px;background-color:#ef4444}</style></head><body><section class='stage'><div class='chip'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 120, 48)

step("Assert place-content:center moves the flex child away from the start edge")
expect(pixels.len()).to_equal(120 * 48)
expect(_count_color(pixels, 0xFFEF4444u32)).to_be_greater_than(0)
expect(_pixel_at(pixels, 120, 5, 6)).to_equal(0xFFDBEAFEu32)
expect(_pixel_at(pixels, 120, 50, 6)).to_equal(0xFFEF4444u32)
```

</details>

#### renders place-items and place-self shorthands through flex cross-axis alignment

- Render flex children using place-items on the container and place-self on one child
- Assert place-items centers one child while place-self overrides the other to the end
   - Expected: pixels.len() equals `80 * 40`
   - Expected: _pixel_at(pixels, 80, 5, 3) equals `0xFFDBEAFEu32`
   - Expected: _pixel_at(pixels, 80, 5, 10) equals `0xFF1D4ED8u32`
   - Expected: _pixel_at(pixels, 80, 15, 10) equals `0xFFDBEAFEu32`
   - Expected: _pixel_at(pixels, 80, 15, 20) equals `0xFFEF4444u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render flex children using place-items on the container and place-self on one child")
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}.stage{display:flex;width:64px;height:24px;background-color:#dbeafe;place-items:center}.a{width:10px;height:6px;background-color:#1d4ed8}.b{width:10px;height:6px;background-color:#ef4444;place-self:flex-end}</style></head><body><section class='stage'><div class='a'></div><div class='b'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 80, 40)

step("Assert place-items centers one child while place-self overrides the other to the end")
expect(pixels.len()).to_equal(80 * 40)
expect(_pixel_at(pixels, 80, 5, 3)).to_equal(0xFFDBEAFEu32)
expect(_pixel_at(pixels, 80, 5, 10)).to_equal(0xFF1D4ED8u32)
expect(_pixel_at(pixels, 80, 15, 10)).to_equal(0xFFDBEAFEu32)
expect(_pixel_at(pixels, 80, 15, 20)).to_equal(0xFFEF4444u32)
```

</details>

#### renders individual translate property as a paint offset

- Render a block using the CSS individual translate property
- Assert translate moves the painted box away from its original origin
   - Expected: pixels.len() equals `96 * 48`
   - Expected: _pixel_at(pixels, 96, 5, 4) equals `0xFFDBEAFEu32`
   - Expected: _pixel_at(pixels, 96, 24, 8) equals `0xFFEF4444u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render a block using the CSS individual translate property")
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}.stage{width:80px;height:36px;background-color:#dbeafe}.chip{width:12px;height:8px;background-color:#ef4444;translate:20px 6px}</style></head><body><section class='stage'><div class='chip'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 48)

step("Assert translate moves the painted box away from its original origin")
expect(pixels.len()).to_equal(96 * 48)
expect(_count_color(pixels, 0xFFEF4444u32)).to_be_greater_than(0)
expect(_pixel_at(pixels, 96, 5, 4)).to_equal(0xFFDBEAFEu32)
expect(_pixel_at(pixels, 96, 24, 8)).to_equal(0xFFEF4444u32)
```

</details>

#### renders filter opacity through blended box paint

- Render a block using filter:opacity over a known background color
- Assert the filter opacity path blends foreground and background pixels
   - Expected: pixels.len() equals `80 * 40`
   - Expected: _pixel_at(pixels, 80, 5, 5) equals `0xFFE597A1u32`
   - Expected: _pixel_at(pixels, 80, 30, 5) equals `0xFFDBEAFEu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render a block using filter:opacity over a known background color")
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}.stage{width:64px;height:32px;background-color:#dbeafe}.chip{width:20px;height:12px;background-color:#ef4444;filter:opacity(50%)}</style></head><body><section class='stage'><div class='chip'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 80, 40)

step("Assert the filter opacity path blends foreground and background pixels")
expect(pixels.len()).to_equal(80 * 40)
expect(_pixel_at(pixels, 80, 5, 5)).to_equal(0xFFE597A1u32)
expect(_pixel_at(pixels, 80, 30, 5)).to_equal(0xFFDBEAFEu32)
```

</details>

#### renders color-scheme dark as default surface colors

- Render a block with color-scheme:dark and no explicit background color
- Assert color-scheme:dark supplies a dark default painted surface
   - Expected: pixels.len() equals `64 * 32`
   - Expected: _pixel_at(pixels, 64, 5, 5) equals `0xFF111827u32`
   - Expected: _pixel_at(pixels, 64, 45, 5) equals `0xFFFFFFFFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render a block with color-scheme:dark and no explicit background color")
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}.panel{width:40px;height:20px;color-scheme:dark}</style></head><body><section class='panel'></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 64, 32)

step("Assert color-scheme:dark supplies a dark default painted surface")
expect(pixels.len()).to_equal(64 * 32)
expect(_pixel_at(pixels, 64, 5, 5)).to_equal(0xFF111827u32)
expect(_pixel_at(pixels, 64, 45, 5)).to_equal(0xFFFFFFFFu32)
```

</details>

#### renders individual scale property as a scaled painted box

- Render a block using the CSS individual scale property
- Assert scale expands the painted box dimensions
   - Expected: pixels.len() equals `96 * 48`
   - Expected: _pixel_at(pixels, 96, 20, 12) equals `0xFFEF4444u32`
   - Expected: _pixel_at(pixels, 96, 28, 12) equals `0xFFDBEAFEu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render a block using the CSS individual scale property")
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}.stage{width:80px;height:40px;background-color:#dbeafe}.chip{width:12px;height:8px;background-color:#ef4444;scale:2}</style></head><body><section class='stage'><div class='chip'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 48)

step("Assert scale expands the painted box dimensions")
expect(pixels.len()).to_equal(96 * 48)
expect(_count_color(pixels, 0xFFEF4444u32)).to_be_greater_than(12 * 8)
expect(_pixel_at(pixels, 96, 20, 12)).to_equal(0xFFEF4444u32)
expect(_pixel_at(pixels, 96, 28, 12)).to_equal(0xFFDBEAFEu32)
```

</details>

#### renders individual rotate property as a quarter-turn painted box

- Render a block using the CSS individual rotate property
- Assert rotate:90deg swaps the painted box dimensions
   - Expected: pixels.len() equals `96 * 48`
   - Expected: _count_color(pixels, 0xFFEF4444u32) equals `8 * 20`
   - Expected: _pixel_at(pixels, 96, 5, 16) equals `0xFFEF4444u32`
   - Expected: _pixel_at(pixels, 96, 12, 5) equals `0xFFDBEAFEu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render a block using the CSS individual rotate property")
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}.stage{width:80px;height:40px;background-color:#dbeafe}.chip{width:20px;height:8px;background-color:#ef4444;rotate:90deg}</style></head><body><section class='stage'><div class='chip'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 48)

step("Assert rotate:90deg swaps the painted box dimensions")
expect(pixels.len()).to_equal(96 * 48)
expect(_count_color(pixels, 0xFFEF4444u32)).to_equal(8 * 20)
expect(_pixel_at(pixels, 96, 5, 16)).to_equal(0xFFEF4444u32)
expect(_pixel_at(pixels, 96, 12, 5)).to_equal(0xFFDBEAFEu32)
```

</details>

#### renders clip rect as a clipped painted box

- Render a block using CSS clip:rect
- Assert clip:rect constrains the painted box dimensions
   - Expected: pixels.len() equals `96 * 48`
   - Expected: _count_color(pixels, 0xFFEF4444u32) equals `8 * 6`
   - Expected: _pixel_at(pixels, 96, 7, 5) equals `0xFFEF4444u32`
   - Expected: _pixel_at(pixels, 96, 9, 5) equals `0xFFDBEAFEu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render a block using CSS clip:rect")
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}.stage{width:80px;height:40px;background-color:#dbeafe}.chip{width:20px;height:12px;background-color:#ef4444;clip:rect(0px,8px,6px,0px)}</style></head><body><section class='stage'><div class='chip'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 48)

step("Assert clip:rect constrains the painted box dimensions")
expect(pixels.len()).to_equal(96 * 48)
expect(_count_color(pixels, 0xFFEF4444u32)).to_equal(8 * 6)
expect(_pixel_at(pixels, 96, 7, 5)).to_equal(0xFFEF4444u32)
expect(_pixel_at(pixels, 96, 9, 5)).to_equal(0xFFDBEAFEu32)
```

</details>

#### renders empty-cells hide by suppressing empty table-cell background paint

- Render table cells where only the empty cell uses empty-cells:hide
- Assert the empty cell shows the table background while the non-empty cell keeps its own background
   - Expected: pixels.len() equals `64 * 32`
   - Expected: _pixel_at(pixels, 64, 5, 4) equals `0xFFDBEAFEu32`
   - Expected: _pixel_at(pixels, 64, 5, 12) equals `0xFFEF4444u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render table cells where only the empty cell uses empty-cells:hide")
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}table{width:40px;background-color:#dbeafe}td{display:block;width:20px;height:8px;background-color:#ef4444;empty-cells:hide;color:#111827;font-size:8px}</style></head><body><table><tr><td></td><td>x</td></tr></table></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 64, 32)

step("Assert the empty cell shows the table background while the non-empty cell keeps its own background")
expect(pixels.len()).to_equal(64 * 32)
expect(_pixel_at(pixels, 64, 5, 4)).to_equal(0xFFDBEAFEu32)
expect(_pixel_at(pixels, 64, 5, 12)).to_equal(0xFFEF4444u32)
```

</details>

#### renders accent-color on generated checkbox controls

- Render a checkbox input with a CSS accent color
- Assert the generated checkbox accent swatch uses the authored accent-color
   - Expected: pixels.len() equals `40 * 30`
   - Expected: _pixel_at(pixels, 40, 1, 1) equals `0xFF22C55Eu32`
   - Expected: _pixel_at(pixels, 40, 5, 5) equals `0xFF22C55Eu32`
   - Expected: _pixel_at(pixels, 40, 20, 5) equals `0xFFFFFFFFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render a checkbox input with a CSS accent color")
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}input{display:block;width:14px;height:14px;accent-color:#22c55e}</style></head><body><input type='checkbox' checked></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 40, 30)

step("Assert the generated checkbox accent swatch uses the authored accent-color")
expect(pixels.len()).to_equal(40 * 30)
expect(_pixel_at(pixels, 40, 1, 1)).to_equal(0xFF22C55Eu32)
expect(_pixel_at(pixels, 40, 5, 5)).to_equal(0xFF22C55Eu32)
expect(_pixel_at(pixels, 40, 20, 5)).to_equal(0xFFFFFFFFu32)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/sys_test/html_css_spec_traceability.md](doc/03_plan/sys_test/html_css_spec_traceability.md)
- **Design:** [doc/04_architecture/ui/simple_gui_stack.md](doc/04_architecture/ui/simple_gui_stack.md)
- **Research:** [doc/03_plan/sys_test/html_css_spec_traceability.md](doc/03_plan/sys_test/html_css_spec_traceability.md)


</details>
