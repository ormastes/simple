# Simple Web Generated HTML/CSS Combinations Specification

> This focused spec covers common generated GUI HTML/CSS combinations against the pure Simple Web renderer. It complements the broad renderer spec without adding more runtime to that already-large file.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 38 | 38 | 0 | 0 |

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
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- renders generated GUI semantic panels with flex, padding, border, and text styles
- Render a generated GUI shell composed from semantic HTML tags and CSS layout properties
- Assert the generated semantic container and CSS colors produce visible pixels
   - Expected: pixels.len() equals `120 * 80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders generated GUI semantic panels with flex, padding, border, and text styles")
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

#### renders legacy grid gap aliases through flex gap layout

- renders legacy grid gap aliases through flex gap layout
- Render row and column flex layouts using legacy grid gap aliases
- Assert the legacy aliases create visible column and row gaps
   - Expected: pixels.len() equals `64 * 40`
   - Expected: _pixel_at(pixels, 64, 8, 3) equals `0xFFDBEAFEu32`
   - Expected: _pixel_at(pixels, 64, 11, 3) equals `0xFF22C55Eu32`
   - Expected: _pixel_at(pixels, 64, 3, 16) equals `0xFFFEF3C7u32`
   - Expected: _pixel_at(pixels, 64, 3, 21) equals `0xFF22C55Eu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders legacy grid gap aliases through flex gap layout")
step("Render row and column flex layouts using legacy grid gap aliases")
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}.row{display:flex;grid-column-gap:4px;background-color:#dbeafe;width:20px;height:8px}.col{display:flex;flex-direction:column;grid-gap:4px;background-color:#fef3c7;width:8px;height:20px;margin-top:2px}.a{width:6px;height:6px;background-color:#ef4444}.b{width:6px;height:6px;background-color:#22c55e}</style></head><body><section class='row'><div class='a'></div><div class='b'></div></section><section class='col'><div class='a'></div><div class='b'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 64, 40)

step("Assert the legacy aliases create visible column and row gaps")
expect(pixels.len()).to_equal(64 * 40)
expect(_pixel_at(pixels, 64, 8, 3)).to_equal(0xFFDBEAFEu32)
expect(_pixel_at(pixels, 64, 11, 3)).to_equal(0xFF22C55Eu32)
expect(_pixel_at(pixels, 64, 3, 16)).to_equal(0xFFFEF3C7u32)
expect(_pixel_at(pixels, 64, 3, 21)).to_equal(0xFF22C55Eu32)
```

</details>

#### renders simple grid template rows and columns through existing layout

- renders simple grid template rows and columns through existing layout
- Render fixed grid template columns and rows with visible gaps
- Assert grid column children sit beside each other and grid row children honor row gap
   - Expected: pixels.len() equals `64 * 40`
   - Expected: _pixel_at(pixels, 64, 8, 3) equals `0xFFDBEAFEu32`
   - Expected: _pixel_at(pixels, 64, 11, 3) equals `0xFF22C55Eu32`
   - Expected: _pixel_at(pixels, 64, 3, 16) equals `0xFFFEF3C7u32`
   - Expected: _pixel_at(pixels, 64, 3, 21) equals `0xFF22C55Eu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders simple grid template rows and columns through existing layout")
step("Render fixed grid template columns and rows with visible gaps")
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}.cols{display:grid;grid-template-columns:6px 6px;column-gap:4px;background-color:#dbeafe;width:20px;height:8px}.rows{display:grid;grid-template-rows:6px 6px;row-gap:4px;background-color:#fef3c7;width:8px;height:20px;margin-top:2px}.a{width:6px;height:6px;background-color:#ef4444}.b{width:6px;height:6px;background-color:#22c55e}</style></head><body><section class='cols'><div class='a'></div><div class='b'></div></section><section class='rows'><div class='a'></div><div class='b'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 64, 40)

step("Assert grid column children sit beside each other and grid row children honor row gap")
expect(pixels.len()).to_equal(64 * 40)
expect(_pixel_at(pixels, 64, 8, 3)).to_equal(0xFFDBEAFEu32)
expect(_pixel_at(pixels, 64, 11, 3)).to_equal(0xFF22C55Eu32)
expect(_pixel_at(pixels, 64, 3, 16)).to_equal(0xFFFEF3C7u32)
expect(_pixel_at(pixels, 64, 3, 21)).to_equal(0xFF22C55Eu32)
```

</details>

#### renders grid-template shorthand through existing row and column layout

- renders grid-template shorthand through existing row and column layout
- Render grid-template shorthand with column and row forms
- Assert the shorthand column form lays out beside and row form stacks with a gap
   - Expected: pixels.len() equals `64 * 40`
   - Expected: _pixel_at(pixels, 64, 8, 3) equals `0xFFDBEAFEu32`
   - Expected: _pixel_at(pixels, 64, 11, 3) equals `0xFF22C55Eu32`
   - Expected: _pixel_at(pixels, 64, 3, 16) equals `0xFFFEF3C7u32`
   - Expected: _pixel_at(pixels, 64, 3, 21) equals `0xFF22C55Eu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders grid-template shorthand through existing row and column layout")
step("Render grid-template shorthand with column and row forms")
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}.cols{display:grid;grid-template:6px / 6px 6px;column-gap:4px;background-color:#dbeafe;width:20px;height:8px}.rows{display:grid;grid-template:6px 6px;row-gap:4px;background-color:#fef3c7;width:8px;height:20px;margin-top:2px}.a{width:6px;height:6px;background-color:#ef4444}.b{width:6px;height:6px;background-color:#22c55e}</style></head><body><section class='cols'><div class='a'></div><div class='b'></div></section><section class='rows'><div class='a'></div><div class='b'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 64, 40)

step("Assert the shorthand column form lays out beside and row form stacks with a gap")
expect(pixels.len()).to_equal(64 * 40)
expect(_pixel_at(pixels, 64, 8, 3)).to_equal(0xFFDBEAFEu32)
expect(_pixel_at(pixels, 64, 11, 3)).to_equal(0xFF22C55Eu32)
expect(_pixel_at(pixels, 64, 3, 16)).to_equal(0xFFFEF3C7u32)
expect(_pixel_at(pixels, 64, 3, 21)).to_equal(0xFF22C55Eu32)
```

</details>

#### renders grid shorthand through existing row and column layout

- renders grid shorthand through existing row and column layout
- Render grid shorthand with column and row forms
- Assert the grid shorthand column form lays out beside and row form stacks with a gap
   - Expected: pixels.len() equals `64 * 40`
   - Expected: _pixel_at(pixels, 64, 8, 3) equals `0xFFDBEAFEu32`
   - Expected: _pixel_at(pixels, 64, 11, 3) equals `0xFF22C55Eu32`
   - Expected: _pixel_at(pixels, 64, 3, 16) equals `0xFFFEF3C7u32`
   - Expected: _pixel_at(pixels, 64, 3, 21) equals `0xFF22C55Eu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders grid shorthand through existing row and column layout")
step("Render grid shorthand with column and row forms")
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}.cols{display:grid;grid:6px / 6px 6px;column-gap:4px;background-color:#dbeafe;width:20px;height:8px}.rows{display:grid;grid:6px 6px;row-gap:4px;background-color:#fef3c7;width:8px;height:20px;margin-top:2px}.a{width:6px;height:6px;background-color:#ef4444}.b{width:6px;height:6px;background-color:#22c55e}</style></head><body><section class='cols'><div class='a'></div><div class='b'></div></section><section class='rows'><div class='a'></div><div class='b'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 64, 40)

step("Assert the grid shorthand column form lays out beside and row form stacks with a gap")
expect(pixels.len()).to_equal(64 * 40)
expect(_pixel_at(pixels, 64, 8, 3)).to_equal(0xFFDBEAFEu32)
expect(_pixel_at(pixels, 64, 11, 3)).to_equal(0xFF22C55Eu32)
expect(_pixel_at(pixels, 64, 3, 16)).to_equal(0xFFFEF3C7u32)
expect(_pixel_at(pixels, 64, 3, 21)).to_equal(0xFF22C55Eu32)
```

</details>

#### renders grid-auto-flow through one-dimensional implicit grid layout

- renders grid-auto-flow through one-dimensional implicit grid layout
- Render row and column auto-flow forms through the existing layout path
- Assert column auto-flow places children beside and row auto-flow stacks them
   - Expected: pixels.len() equals `64 * 40`
   - Expected: _pixel_at(pixels, 64, 8, 3) equals `0xFFDBEAFEu32`
   - Expected: _pixel_at(pixels, 64, 11, 3) equals `0xFF22C55Eu32`
   - Expected: _pixel_at(pixels, 64, 3, 16) equals `0xFFFEF3C7u32`
   - Expected: _pixel_at(pixels, 64, 3, 21) equals `0xFF22C55Eu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders grid-auto-flow through one-dimensional implicit grid layout")
step("Render row and column auto-flow forms through the existing layout path")
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}.cols{display:grid;grid-auto-flow:column;column-gap:4px;background-color:#dbeafe;width:20px;height:8px}.rows{display:grid;grid-auto-flow:row;row-gap:4px;background-color:#fef3c7;width:8px;height:20px;margin-top:2px}.a{width:6px;height:6px;background-color:#ef4444}.b{width:6px;height:6px;background-color:#22c55e}</style></head><body><section class='cols'><div class='a'></div><div class='b'></div></section><section class='rows'><div class='a'></div><div class='b'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 64, 40)

step("Assert column auto-flow places children beside and row auto-flow stacks them")
expect(pixels.len()).to_equal(64 * 40)
expect(_pixel_at(pixels, 64, 8, 3)).to_equal(0xFFDBEAFEu32)
expect(_pixel_at(pixels, 64, 11, 3)).to_equal(0xFF22C55Eu32)
expect(_pixel_at(pixels, 64, 3, 16)).to_equal(0xFFFEF3C7u32)
expect(_pixel_at(pixels, 64, 3, 21)).to_equal(0xFF22C55Eu32)
```

</details>

#### renders grid placement starts through existing one-dimensional ordering

- renders grid placement starts through existing one-dimensional ordering
- Render grid column and row start placement with visible reordered items
- Assert lower placement start renders first in row and column flows
   - Expected: pixels.len() equals `64 * 40`
   - Expected: _pixel_at(pixels, 64, 3, 3) equals `0xFF22C55Eu32`
   - Expected: _pixel_at(pixels, 64, 13, 3) equals `0xFFEF4444u32`
   - Expected: _pixel_at(pixels, 64, 3, 13) equals `0xFF22C55Eu32`
   - Expected: _pixel_at(pixels, 64, 3, 23) equals `0xFFEF4444u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders grid placement starts through existing one-dimensional ordering")
step("Render grid column and row start placement with visible reordered items")
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}.cols{display:grid;grid-auto-flow:column;column-gap:4px;background-color:#dbeafe;width:20px;height:8px}.rows{display:grid;grid-auto-flow:row;row-gap:4px;background-color:#fef3c7;width:8px;height:20px;margin-top:2px}.a{width:6px;height:6px;background-color:#ef4444;grid-column-start:2;grid-row-start:2}.b{width:6px;height:6px;background-color:#22c55e;grid-column-start:1;grid-row-start:1}</style></head><body><section class='cols'><div class='a'></div><div class='b'></div></section><section class='rows'><div class='a'></div><div class='b'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 64, 40)

step("Assert lower placement start renders first in row and column flows")
expect(pixels.len()).to_equal(64 * 40)
expect(_pixel_at(pixels, 64, 3, 3)).to_equal(0xFF22C55Eu32)
expect(_pixel_at(pixels, 64, 13, 3)).to_equal(0xFFEF4444u32)
expect(_pixel_at(pixels, 64, 3, 13)).to_equal(0xFF22C55Eu32)
expect(_pixel_at(pixels, 64, 3, 23)).to_equal(0xFFEF4444u32)
```

</details>

#### renders grid placement shorthands through existing one-dimensional ordering

- renders grid placement shorthands through existing one-dimensional ordering
- Render grid column and row shorthands with visible reordered items
- Assert lower shorthand placement start renders first in row and column flows
   - Expected: pixels.len() equals `64 * 40`
   - Expected: _pixel_at(pixels, 64, 3, 3) equals `0xFF22C55Eu32`
   - Expected: _pixel_at(pixels, 64, 13, 3) equals `0xFFEF4444u32`
   - Expected: _pixel_at(pixels, 64, 3, 13) equals `0xFF22C55Eu32`
   - Expected: _pixel_at(pixels, 64, 3, 23) equals `0xFFEF4444u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders grid placement shorthands through existing one-dimensional ordering")
step("Render grid column and row shorthands with visible reordered items")
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}.cols{display:grid;grid-auto-flow:column;column-gap:4px;background-color:#dbeafe;width:20px;height:8px}.rows{display:grid;grid-auto-flow:row;row-gap:4px;background-color:#fef3c7;width:8px;height:20px;margin-top:2px}.a{width:6px;height:6px;background-color:#ef4444;grid-column:2 / 3;grid-row:2 / 3}.b{width:6px;height:6px;background-color:#22c55e;grid-column:1 / 2;grid-row:1 / 2}</style></head><body><section class='cols'><div class='a'></div><div class='b'></div></section><section class='rows'><div class='a'></div><div class='b'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 64, 40)

step("Assert lower shorthand placement start renders first in row and column flows")
expect(pixels.len()).to_equal(64 * 40)
expect(_pixel_at(pixels, 64, 3, 3)).to_equal(0xFF22C55Eu32)
expect(_pixel_at(pixels, 64, 13, 3)).to_equal(0xFFEF4444u32)
expect(_pixel_at(pixels, 64, 3, 13)).to_equal(0xFF22C55Eu32)
expect(_pixel_at(pixels, 64, 3, 23)).to_equal(0xFFEF4444u32)
```

</details>

#### renders numeric grid-area starts through existing one-dimensional ordering

- renders numeric grid-area starts through existing one-dimensional ordering
- Render numeric grid-area placement with visible reordered items
- Assert lower numeric grid-area start renders first in row and column flows
   - Expected: pixels.len() equals `64 * 40`
   - Expected: _pixel_at(pixels, 64, 3, 3) equals `0xFF22C55Eu32`
   - Expected: _pixel_at(pixels, 64, 13, 3) equals `0xFFEF4444u32`
   - Expected: _pixel_at(pixels, 64, 3, 13) equals `0xFF22C55Eu32`
   - Expected: _pixel_at(pixels, 64, 3, 23) equals `0xFFEF4444u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders numeric grid-area starts through existing one-dimensional ordering")
step("Render numeric grid-area placement with visible reordered items")
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}.cols{display:grid;grid-auto-flow:column;column-gap:4px;background-color:#dbeafe;width:20px;height:8px}.rows{display:grid;grid-auto-flow:row;row-gap:4px;background-color:#fef3c7;width:8px;height:20px;margin-top:2px}.a{width:6px;height:6px;background-color:#ef4444;grid-area:2 / 2 / 3 / 3}.b{width:6px;height:6px;background-color:#22c55e;grid-area:1 / 1 / 2 / 2}</style></head><body><section class='cols'><div class='a'></div><div class='b'></div></section><section class='rows'><div class='a'></div><div class='b'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 64, 40)

step("Assert lower numeric grid-area start renders first in row and column flows")
expect(pixels.len()).to_equal(64 * 40)
expect(_pixel_at(pixels, 64, 3, 3)).to_equal(0xFF22C55Eu32)
expect(_pixel_at(pixels, 64, 13, 3)).to_equal(0xFFEF4444u32)
expect(_pixel_at(pixels, 64, 3, 13)).to_equal(0xFF22C55Eu32)
expect(_pixel_at(pixels, 64, 3, 23)).to_equal(0xFFEF4444u32)
```

</details>

#### renders generated form control combinations with fieldset, label, input, select, and progress

- renders generated form control combinations with fieldset, label, input, select, and progress
- Render form-oriented generated HTML with common CSS box properties
- Assert form control tags and shared CSS selectors contribute visible styled output
   - Expected: pixels.len() equals `128 * 72`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders generated form control combinations with fieldset, label, input, select, and progress")
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

- renders generated media and canvas placeholders with overflow and object box styles
- Render media-oriented generated HTML using canvas, picture, img, video, and object placeholders
- Assert mixed media placeholder tags and CSS overflow/background styling render
   - Expected: pixels.len() equals `128 * 72`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders generated media and canvas placeholders with overflow and object box styles")
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

- renders place-content shorthand through flex alignment
- Render a flex container using place-content as the align-content and justify-content shorthand
- Assert place-content:center moves the flex child away from the start edge
   - Expected: pixels.len() equals `120 * 48`
   - Expected: _pixel_at(pixels, 120, 5, 6) equals `0xFFDBEAFEu32`
   - Expected: _pixel_at(pixels, 120, 50, 6) equals `0xFFEF4444u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders place-content shorthand through flex alignment")
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

- renders place-items and place-self shorthands through flex cross-axis alignment
- Render flex children using place-items on the container and place-self on one child
- Assert place-items centers one child while place-self overrides the other to the end
   - Expected: pixels.len() equals `80 * 40`
   - Expected: _pixel_at(pixels, 80, 5, 3) equals `0xFFDBEAFEu32`
   - Expected: _pixel_at(pixels, 80, 5, 10) equals `0xFF1D4ED8u32`
   - Expected: _pixel_at(pixels, 80, 15, 10) equals `0xFFDBEAFEu32`
   - Expected: _pixel_at(pixels, 80, 15, 20) equals `0xFFEF4444u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders place-items and place-self shorthands through flex cross-axis alignment")
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

#### renders justify-self on definite-width block children

- renders justify-self on definite-width block children
- Render fixed-width block children with center and end self alignment
- Assert end and center alignment shift the child boxes horizontally
   - Expected: pixels.len() equals `64 * 32`
   - Expected: _pixel_at(pixels, 64, 5, 3) equals `0xFFDBEAFEu32`
   - Expected: _pixel_at(pixels, 64, 35, 3) equals `0xFFEF4444u32`
   - Expected: _pixel_at(pixels, 64, 20, 10) equals `0xFF1D4ED8u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders justify-self on definite-width block children")
step("Render fixed-width block children with center and end self alignment")
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}.stage{width:40px;height:18px;background-color:#dbeafe}.end{display:block;width:10px;height:6px;background-color:#ef4444;justify-self:end}.center{display:block;width:10px;height:6px;background-color:#1d4ed8;justify-self:center;margin-top:2px}</style></head><body><section class='stage'><div class='end'></div><div class='center'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 64, 32)

step("Assert end and center alignment shift the child boxes horizontally")
expect(pixels.len()).to_equal(64 * 32)
expect(_pixel_at(pixels, 64, 5, 3)).to_equal(0xFFDBEAFEu32)
expect(_pixel_at(pixels, 64, 35, 3)).to_equal(0xFFEF4444u32)
expect(_pixel_at(pixels, 64, 20, 10)).to_equal(0xFF1D4ED8u32)
```

</details>

#### renders justify-items as the default self alignment for block children

- renders justify-items as the default self alignment for block children
- Render fixed-width block children with parent justify-items
- Assert justify-items shifts the auto child while explicit justify-self overrides it
   - Expected: pixels.len() equals `64 * 32`
   - Expected: _pixel_at(pixels, 64, 35, 3) equals `0xFFEF4444u32`
   - Expected: _pixel_at(pixels, 64, 5, 10) equals `0xFF1D4ED8u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders justify-items as the default self alignment for block children")
step("Render fixed-width block children with parent justify-items")
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}.stage{width:40px;height:16px;background-color:#dbeafe;justify-items:end}.a{display:block;width:10px;height:6px;background-color:#ef4444}.b{display:block;width:10px;height:6px;background-color:#1d4ed8;justify-self:start;margin-top:2px}</style></head><body><section class='stage'><div class='a'></div><div class='b'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 64, 32)

step("Assert justify-items shifts the auto child while explicit justify-self overrides it")
expect(pixels.len()).to_equal(64 * 32)
expect(_pixel_at(pixels, 64, 35, 3)).to_equal(0xFFEF4444u32)
expect(_pixel_at(pixels, 64, 5, 10)).to_equal(0xFF1D4ED8u32)
```

</details>

#### renders individual translate property as a paint offset

- renders individual translate property as a paint offset
- Render a block using the CSS individual translate property
- Assert translate moves the painted box away from its original origin
   - Expected: pixels.len() equals `96 * 48`
   - Expected: _pixel_at(pixels, 96, 5, 4) equals `0xFFDBEAFEu32`
   - Expected: _pixel_at(pixels, 96, 24, 8) equals `0xFFEF4444u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders individual translate property as a paint offset")
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

#### renders text-emphasis marks with color and under position

- renders text-emphasis marks with color and under position
- Render text with emphasis shorthand and longhand position
- Assert emphasis marks paint below the glyphs using the emphasis color
   - Expected: pixels.len() equals `96 * 40`
   - Expected: _pixel_at(pixels, 96, 4, 10) equals `0xFFEF4444u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders text-emphasis marks with color and under position")
step("Render text with emphasis shorthand and longhand position")
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}.stage{width:80px;height:24px;background-color:#dbeafe}.mark{font-size:8px;line-height:12px;color:#111827;text-emphasis:dot #ef4444;text-emphasis-position:under}</style></head><body><section class='stage'><div class='mark'>HI</div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 40)

step("Assert emphasis marks paint below the glyphs using the emphasis color")
expect(pixels.len()).to_equal(96 * 40)
expect(_count_color(pixels, 0xFFEF4444u32)).to_be_greater_than(0)
expect(_pixel_at(pixels, 96, 4, 10)).to_equal(0xFFEF4444u32)
```

</details>

#### renders quotes on q text and supports quotes none

- renders quotes on q text and supports quotes none
- Render q text with custom quotes and a second q suppressing quotes
- Assert custom quotes add visible text pixels before the q content
   - Expected: pixels.len() equals `112 * 40`
   - Expected: _pixel_at(pixels, 112, 2, 3) equals `0xFF111827u32`
   - Expected: _pixel_at(pixels, 112, 2, 13) equals `0xFFDBEAFEu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders quotes on q text and supports quotes none")
step("Render q text with custom quotes and a second q suppressing quotes")
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}.stage{width:96px;height:28px;background-color:#dbeafe;color:#111827;font-size:8px;line-height:10px}.quoted{color:#111827;quotes:'[' ']'} .plain{color:#111827;quotes:none}</style></head><body><section class='stage'><q class='quoted'>A</q><br><q class='plain'>A</q></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 112, 40)

step("Assert custom quotes add visible text pixels before the q content")
expect(pixels.len()).to_equal(112 * 40)
expect(_count_color(pixels, 0xFF111827u32)).to_be_greater_than(0)
expect(_pixel_at(pixels, 112, 2, 3)).to_equal(0xFF111827u32)
expect(_pixel_at(pixels, 112, 2, 13)).to_equal(0xFFDBEAFEu32)
```

</details>

#### renders filter opacity through blended box paint

- renders filter opacity through blended box paint
- Render a block using filter:opacity over a known background color
- Assert the filter opacity path blends foreground and background pixels
   - Expected: pixels.len() equals `80 * 40`
   - Expected: _pixel_at(pixels, 80, 5, 5) equals `0xFFE597A1u32`
   - Expected: _pixel_at(pixels, 80, 30, 5) equals `0xFFDBEAFEu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders filter opacity through blended box paint")
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

- renders color-scheme dark as default surface colors
- Render a block with color-scheme:dark and no explicit background color
- Assert color-scheme:dark supplies a dark default painted surface
   - Expected: pixels.len() equals `64 * 32`
   - Expected: _pixel_at(pixels, 64, 5, 5) equals `0xFF111827u32`
   - Expected: _pixel_at(pixels, 64, 45, 5) equals `0xFFFFFFFFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders color-scheme dark as default surface colors")
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

- renders individual scale property as a scaled painted box
- Render a block using the CSS individual scale property
- Assert scale expands the painted box dimensions
   - Expected: pixels.len() equals `96 * 48`
   - Expected: _pixel_at(pixels, 96, 20, 12) equals `0xFFEF4444u32`
   - Expected: _pixel_at(pixels, 96, 28, 12) equals `0xFFDBEAFEu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders individual scale property as a scaled painted box")
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

- renders individual rotate property as a quarter-turn painted box
- Render a block using the CSS individual rotate property
- Assert rotate:90deg swaps the painted box dimensions
   - Expected: pixels.len() equals `96 * 48`
   - Expected: _count_color(pixels, 0xFFEF4444u32) equals `8 * 20`
   - Expected: _pixel_at(pixels, 96, 5, 16) equals `0xFFEF4444u32`
   - Expected: _pixel_at(pixels, 96, 12, 5) equals `0xFFDBEAFEu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders individual rotate property as a quarter-turn painted box")
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

- renders clip rect as a clipped painted box
- Render a block using CSS clip:rect
- Assert clip:rect constrains the painted box dimensions
   - Expected: pixels.len() equals `96 * 48`
   - Expected: _count_color(pixels, 0xFFEF4444u32) equals `8 * 6`
   - Expected: _pixel_at(pixels, 96, 7, 5) equals `0xFFEF4444u32`
   - Expected: _pixel_at(pixels, 96, 9, 5) equals `0xFFDBEAFEu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders clip rect as a clipped painted box")
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

#### renders clip-path inset as a clipped painted box

- renders clip-path inset as a clipped painted box
- Render a block using CSS clip-path:inset
- Assert clip-path:inset constrains the painted box dimensions
   - Expected: pixels.len() equals `96 * 48`
   - Expected: _count_color(pixels, 0xFFEF4444u32) equals `8 * 6`
   - Expected: _pixel_at(pixels, 96, 2, 4) equals `0xFFDBEAFEu32`
   - Expected: _pixel_at(pixels, 96, 5, 4) equals `0xFFEF4444u32`
   - Expected: _pixel_at(pixels, 96, 11, 4) equals `0xFFDBEAFEu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders clip-path inset as a clipped painted box")
step("Render a block using CSS clip-path:inset")
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}.stage{width:80px;height:40px;background-color:#dbeafe}.chip{width:20px;height:12px;background-color:#ef4444;clip-path:inset(2px 9px 4px 3px)}</style></head><body><section class='stage'><div class='chip'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 48)

step("Assert clip-path:inset constrains the painted box dimensions")
expect(pixels.len()).to_equal(96 * 48)
expect(_count_color(pixels, 0xFFEF4444u32)).to_equal(8 * 6)
expect(_pixel_at(pixels, 96, 2, 4)).to_equal(0xFFDBEAFEu32)
expect(_pixel_at(pixels, 96, 5, 4)).to_equal(0xFFEF4444u32)
expect(_pixel_at(pixels, 96, 11, 4)).to_equal(0xFFDBEAFEu32)
```

</details>

#### renders backface-visibility hidden by suppressing a rotated backface

- renders backface-visibility hidden by suppressing a rotated backface
- Render a block whose back face is hidden after a 3D half turn
- Assert the rotated back face does not paint its background
   - Expected: pixels.len() equals `96 * 48`
   - Expected: _count_color(pixels, 0xFFEF4444u32) equals `0`
   - Expected: _pixel_at(pixels, 96, 5, 5) equals `0xFFDBEAFEu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders backface-visibility hidden by suppressing a rotated backface")
step("Render a block whose back face is hidden after a 3D half turn")
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}.stage{width:80px;height:40px;background-color:#dbeafe}.chip{width:20px;height:12px;background-color:#ef4444;backface-visibility:hidden;transform:rotateY(180deg)}</style></head><body><section class='stage'><div class='chip'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 48)

step("Assert the rotated back face does not paint its background")
expect(pixels.len()).to_equal(96 * 48)
expect(_count_color(pixels, 0xFFEF4444u32)).to_equal(0)
expect(_pixel_at(pixels, 96, 5, 5)).to_equal(0xFFDBEAFEu32)
```

</details>

#### renders empty-cells hide by suppressing empty table-cell background paint

- renders empty-cells hide by suppressing empty table-cell background paint
- Render table cells where only the empty cell uses empty-cells:hide
- Assert the empty cell shows the table background while the non-empty cell keeps its own background
   - Expected: pixels.len() equals `64 * 32`
   - Expected: _pixel_at(pixels, 64, 5, 4) equals `0xFFDBEAFEu32`
   - Expected: _pixel_at(pixels, 64, 5, 12) equals `0xFFEF4444u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders empty-cells hide by suppressing empty table-cell background paint")
step("Render table cells where only the empty cell uses empty-cells:hide")
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}table{width:40px;background-color:#dbeafe}td{display:block;width:20px;height:8px;background-color:#ef4444;empty-cells:hide;color:#111827;font-size:8px}</style></head><body><table><tr><td></td><td>x</td></tr></table></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 64, 32)

step("Assert the empty cell shows the table background while the non-empty cell keeps its own background")
expect(pixels.len()).to_equal(64 * 32)
expect(_pixel_at(pixels, 64, 5, 4)).to_equal(0xFFDBEAFEu32)
expect(_pixel_at(pixels, 64, 5, 12)).to_equal(0xFFEF4444u32)
```

</details>

#### renders border-collapse collapse by suppressing the table wrapper border

- renders border-collapse collapse by suppressing the table wrapper border
- Render a collapsed-border table with a visible cell border
- Assert the table border no longer paints while the cell border still does
   - Expected: pixels.len() equals `64 * 32`
   - Expected: _count_color(pixels, 0xFFEF4444u32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders border-collapse collapse by suppressing the table wrapper border")
step("Render a collapsed-border table with a visible cell border")
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}table{border-collapse:collapse;border:4px solid #ef4444;background-color:#dbeafe}td{display:block;width:20px;height:8px;border:2px solid #1d4ed8;background-color:#22c55e}</style></head><body><table><tr><td></td></tr></table></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 64, 32)

step("Assert the table border no longer paints while the cell border still does")
expect(pixels.len()).to_equal(64 * 32)
expect(_count_color(pixels, 0xFFEF4444u32)).to_equal(0)
expect(_count_color(pixels, 0xFF1D4ED8u32)).to_be_greater_than(0)
```

</details>

#### renders border-spacing as table inner spacing before cells

- renders border-spacing as table inner spacing before cells
- Render a table with border-spacing and a painted cell
- Assert the table background is visible before the shifted cell
   - Expected: pixels.len() equals `64 * 32`
   - Expected: _pixel_at(pixels, 64, 2, 2) equals `0xFFDBEAFEu32`
   - Expected: _pixel_at(pixels, 64, 5, 5) equals `0xFF22C55Eu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders border-spacing as table inner spacing before cells")
step("Render a table with border-spacing and a painted cell")
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}table{border-spacing:4px;background-color:#dbeafe}td{display:block;width:20px;height:8px;background-color:#22c55e}</style></head><body><table><tr><td></td></tr></table></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 64, 32)

step("Assert the table background is visible before the shifted cell")
expect(pixels.len()).to_equal(64 * 32)
expect(_pixel_at(pixels, 64, 2, 2)).to_equal(0xFFDBEAFEu32)
expect(_pixel_at(pixels, 64, 5, 5)).to_equal(0xFF22C55Eu32)
```

</details>

#### renders caption-side bottom by placing the caption below table content

- renders caption-side bottom by placing the caption below table content
- Render a table with a source-first caption moved to the bottom
- Assert table content paints before the bottom caption
   - Expected: pixels.len() equals `64 * 32`
   - Expected: cell_y equals `0`
   - Expected: caption_y equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders caption-side bottom by placing the caption below table content")
step("Render a table with a source-first caption moved to the bottom")
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}table{width:30px;background-color:#f8fafc}caption{caption-side:bottom;display:block;width:30px;height:6px;background-color:#1d4ed8}tr{display:block;width:30px;height:8px}td{display:block;width:30px;height:8px;background-color:#ef4444}</style></head><body><table><caption id='cap'></caption><tr><td id='cell'></td></tr></table></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 64, 32)
val cell_y = simple_web_layout_debug_layout_by_id(html, 64, 32, "cell", "y")
val caption_y = simple_web_layout_debug_layout_by_id(html, 64, 32, "cap", "y")

step("Assert table content paints before the bottom caption")
expect(pixels.len()).to_equal(64 * 32)
expect(cell_y).to_equal("0")
expect(caption_y).to_equal("8")
expect(_count_color(pixels, 0xFF1D4ED8u32)).to_be_greater_than(0)
```

</details>

#### renders list-style-position inside by moving the list marker into the item box

- renders list-style-position inside by moving the list marker into the item box
- Render outside and inside list markers with distinct foreground colors
- Assert the outside marker paints before the item box and the inside marker paints within it
   - Expected: pixels.len() equals `48 * 28`
   - Expected: _pixel_at(pixels, 48, 6, 4) equals `0xFFEF4444u32`
   - Expected: _pixel_at(pixels, 48, 14, 14) equals `0xFF1D4ED8u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders list-style-position inside by moving the list marker into the item box")
step("Render outside and inside list markers with distinct foreground colors")
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}ul{margin:0;padding-left:12px}.outside{display:block;width:24px;height:10px;color:#ef4444;list-style-position:outside}.inside{display:block;width:24px;height:10px;color:#1d4ed8;list-style-position:inside}</style></head><body><ul><li class='outside'></li><li class='inside'></li></ul></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 48, 28)

step("Assert the outside marker paints before the item box and the inside marker paints within it")
expect(pixels.len()).to_equal(48 * 28)
expect(_pixel_at(pixels, 48, 6, 4)).to_equal(0xFFEF4444u32)
expect(_pixel_at(pixels, 48, 14, 14)).to_equal(0xFF1D4ED8u32)
```

</details>

#### renders list-style-image markers and suppresses list-style-type none

- renders list-style-image markers and suppresses list-style-type none
- Render one hidden list marker and one image marker placeholder
- Assert none removes the first marker and url image paints a marker placeholder
   - Expected: pixels.len() equals `48 * 28`
   - Expected: _pixel_at(pixels, 48, 6, 4) equals `0xFFFFFFFFu32`
   - Expected: _pixel_at(pixels, 48, 6, 13) equals `0xFF2563EBu32`
   - Expected: _pixel_at(pixels, 48, 7, 14) equals `0xFFF59E0Bu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders list-style-image markers and suppresses list-style-type none")
step("Render one hidden list marker and one image marker placeholder")
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}ul{margin:0;padding-left:12px}.none{display:block;width:24px;height:10px;color:#ef4444;list-style-type:none}.image{display:block;width:24px;height:10px;color:#111827;list-style-image:url(marker.png)}</style></head><body><ul><li class='none'></li><li class='image'></li></ul></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 48, 28)

step("Assert none removes the first marker and url image paints a marker placeholder")
expect(pixels.len()).to_equal(48 * 28)
expect(_pixel_at(pixels, 48, 6, 4)).to_equal(0xFFFFFFFFu32)
expect(_pixel_at(pixels, 48, 6, 13)).to_equal(0xFF2563EBu32)
expect(_pixel_at(pixels, 48, 7, 14)).to_equal(0xFFF59E0Bu32)
```

</details>

#### renders column-count by placing simple children into columns

- renders column-count by placing simple children into columns
- Render two child boxes in a two-column container
- Assert the second child paints beside the first child
   - Expected: pixels.len() equals `64 * 32`
   - Expected: _pixel_at(pixels, 64, 5, 4) equals `0xFFEF4444u32`
   - Expected: _pixel_at(pixels, 64, 12, 4) equals `0xFF22C55Eu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders column-count by placing simple children into columns")
step("Render two child boxes in a two-column container")
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}.cols{column-count:2;background-color:#dbeafe;width:40px;height:16px}.a{width:10px;height:8px;background-color:#ef4444}.b{width:10px;height:8px;background-color:#22c55e}</style></head><body><section class='cols'><div class='a'></div><div class='b'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 64, 32)

step("Assert the second child paints beside the first child")
expect(pixels.len()).to_equal(64 * 32)
expect(_pixel_at(pixels, 64, 5, 4)).to_equal(0xFFEF4444u32)
expect(_pixel_at(pixels, 64, 12, 4)).to_equal(0xFF22C55Eu32)
```

</details>

#### renders column-width by placing simple children into columns

- renders column-width by placing simple children into columns
- Render two child boxes in a fixed-width column container
- Assert the second child paints beside the first child
   - Expected: pixels.len() equals `64 * 32`
   - Expected: _pixel_at(pixels, 64, 5, 4) equals `0xFFEF4444u32`
   - Expected: _pixel_at(pixels, 64, 12, 4) equals `0xFF22C55Eu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders column-width by placing simple children into columns")
step("Render two child boxes in a fixed-width column container")
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}.cols{column-width:10px;background-color:#dbeafe;width:40px;height:16px}.a{width:10px;height:8px;background-color:#ef4444}.b{width:10px;height:8px;background-color:#22c55e}</style></head><body><section class='cols'><div class='a'></div><div class='b'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 64, 32)

step("Assert the second child paints beside the first child")
expect(pixels.len()).to_equal(64 * 32)
expect(_pixel_at(pixels, 64, 5, 4)).to_equal(0xFFEF4444u32)
expect(_pixel_at(pixels, 64, 12, 4)).to_equal(0xFF22C55Eu32)
```

</details>

#### renders columns shorthand by placing simple children into columns

- renders columns shorthand by placing simple children into columns
- Render two child boxes in a shorthand column container
- Assert the second child paints beside the first child
   - Expected: pixels.len() equals `64 * 32`
   - Expected: _pixel_at(pixels, 64, 5, 4) equals `0xFFEF4444u32`
   - Expected: _pixel_at(pixels, 64, 12, 4) equals `0xFF22C55Eu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders columns shorthand by placing simple children into columns")
step("Render two child boxes in a shorthand column container")
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}.cols{columns:2;background-color:#dbeafe;width:40px;height:16px}.a{width:10px;height:8px;background-color:#ef4444}.b{width:10px;height:8px;background-color:#22c55e}</style></head><body><section class='cols'><div class='a'></div><div class='b'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 64, 32)

step("Assert the second child paints beside the first child")
expect(pixels.len()).to_equal(64 * 32)
expect(_pixel_at(pixels, 64, 5, 4)).to_equal(0xFFEF4444u32)
expect(_pixel_at(pixels, 64, 12, 4)).to_equal(0xFF22C55Eu32)
```

</details>

#### renders column-rule shorthand as a visible gap between simple columns

- renders column-rule shorthand as a visible gap between simple columns
- Render two child boxes separated by a column rule
- Assert the column rule paints between the two children
   - Expected: pixels.len() equals `64 * 32`
   - Expected: _pixel_at(pixels, 64, 5, 4) equals `0xFFEF4444u32`
   - Expected: _pixel_at(pixels, 64, 10, 4) equals `0xFF1D4ED8u32`
   - Expected: _pixel_at(pixels, 64, 12, 4) equals `0xFF22C55Eu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders column-rule shorthand as a visible gap between simple columns")
step("Render two child boxes separated by a column rule")
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}.cols{columns:2;column-rule:2px solid #1d4ed8;width:22px;height:8px}.a{width:10px;height:8px;background-color:#ef4444}.b{width:10px;height:8px;background-color:#22c55e}</style></head><body><section class='cols'><div class='a'></div><div class='b'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 64, 32)

step("Assert the column rule paints between the two children")
expect(pixels.len()).to_equal(64 * 32)
expect(_pixel_at(pixels, 64, 5, 4)).to_equal(0xFFEF4444u32)
expect(_pixel_at(pixels, 64, 10, 4)).to_equal(0xFF1D4ED8u32)
expect(_pixel_at(pixels, 64, 12, 4)).to_equal(0xFF22C55Eu32)
```

</details>

#### renders column-rule longhands as a visible gap between simple columns

- renders column-rule longhands as a visible gap between simple columns
- Render two child boxes separated by column rule longhands
- Assert the longhand column rule paints between the two children
   - Expected: pixels.len() equals `64 * 32`
   - Expected: _pixel_at(pixels, 64, 5, 4) equals `0xFFEF4444u32`
   - Expected: _pixel_at(pixels, 64, 10, 4) equals `0xFF7C3AEDu32`
   - Expected: _pixel_at(pixels, 64, 12, 4) equals `0xFF22C55Eu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders column-rule longhands as a visible gap between simple columns")
step("Render two child boxes separated by column rule longhands")
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}.cols{columns:2;column-rule-width:2px;column-rule-style:solid;column-rule-color:#7c3aed;width:22px;height:8px}.a{width:10px;height:8px;background-color:#ef4444}.b{width:10px;height:8px;background-color:#22c55e}</style></head><body><section class='cols'><div class='a'></div><div class='b'></div></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 64, 32)

step("Assert the longhand column rule paints between the two children")
expect(pixels.len()).to_equal(64 * 32)
expect(_pixel_at(pixels, 64, 5, 4)).to_equal(0xFFEF4444u32)
expect(_pixel_at(pixels, 64, 10, 4)).to_equal(0xFF7C3AEDu32)
expect(_pixel_at(pixels, 64, 12, 4)).to_equal(0xFF22C55Eu32)
```

</details>

#### renders accent-color on generated checkbox controls

- renders accent-color on generated checkbox controls
- Render a checkbox input with a CSS accent color
- Assert the generated checkbox accent swatch uses the authored accent-color
   - Expected: pixels.len() equals `40 * 30`
   - Expected: _pixel_at(pixels, 40, 20, 5) equals `0xFFFFFFFFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders accent-color on generated checkbox controls")
step("Render a checkbox input with a CSS accent color")
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}input{display:block;width:14px;height:14px;accent-color:#22c55e}</style></head><body><input type='checkbox' checked></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 40, 30)

step("Assert the generated checkbox accent swatch uses the authored accent-color")
expect(pixels.len()).to_equal(40 * 30)
expect(_count_color(pixels, 0xFF22C55Eu32)).to_be_greater_than(0)
expect(_pixel_at(pixels, 40, 20, 5)).to_equal(0xFFFFFFFFu32)
```

</details>

#### renders background-blend-mode multiply over a solid background color

- renders background-blend-mode multiply over a solid background color
- Render a generated panel with a red gradient multiplied by a gray background
- Assert multiply blending darkens the gradient to the expected red channel
   - Expected: pixels.len() equals `32 * 24`
   - Expected: _pixel_at(pixels, 32, 4, 4) equals `0xFF800000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders background-blend-mode multiply over a solid background color")
step("Render a generated panel with a red gradient multiplied by a gray background")
val html = "<html><head><style>html,body{margin:0;padding:0;background-color:#ffffff}.blend{display:block;width:12px;height:8px;background-color:#808080;background-image:linear-gradient(#ff0000,#ff0000);background-blend-mode:multiply}</style></head><body><section class='blend'></section></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 32, 24)

step("Assert multiply blending darkens the gradient to the expected red channel")
expect(pixels.len()).to_equal(32 * 24)
expect(_pixel_at(pixels, 32, 4, 4)).to_equal(0xFF800000u32)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 38 |
| Active scenarios | 38 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/sys_test/html_css_spec_traceability.md`
- **Design:** `doc/04_architecture/ui/simple_gui_stack.md`
- **Research:** `doc/03_plan/sys_test/html_css_spec_traceability.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f01ed5bc66495e9914d1046e17c7a4a05e029dc632876f94d532bec41a316392`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f01ed5bc66495e9914d1046e17c7a4a05e029dc632876f94d532bec41a316392`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f01ed5bc66495e9914d1046e17c7a4a05e029dc632876f94d532bec41a316392`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_generated_html_css_combinations_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_generated_html_css_combinations_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_generated_html_css_combinations_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_generated_html_css_combinations_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_generated_html_css_combinations_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_generated_html_css_combinations_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders generated GUI semantic panels with flex, padding, border, and text styles' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_generated_html_css_combinations_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders legacy grid gap aliases through flex gap layout' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_generated_html_css_combinations_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders simple grid template rows and columns through existing layout' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
