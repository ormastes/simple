# Markdown WYSIWYG Graphical Render Specification

> This unit spec proves the end-to-end graphical markdown path: raw markdown is built into a `WysiwygView`, wrapped as styled preview HTML via `wysiwyg_preview_pane`, and rendered to pixels through the EXACT same renderer entrypoint the `md_wysiwyg_ppm` / `md_wysiwyg_gui` apps use (`simple_web_render_html_to_pixels_with_engine2d_backend`, backend `cpu_simd`).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Markdown WYSIWYG Graphical Render Specification

This unit spec proves the end-to-end graphical markdown path: raw markdown is built into a `WysiwygView`, wrapped as styled preview HTML via `wysiwyg_preview_pane`, and rendered to pixels through the EXACT same renderer entrypoint the `md_wysiwyg_ppm` / `md_wysiwyg_gui` apps use (`simple_web_render_html_to_pixels_with_engine2d_backend`, backend `cpu_simd`).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | N/A — implementation/architecture evidence for the markdown -> |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Source | `test/01_unit/app/office/md_wysiwyg_render_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This unit spec proves the end-to-end graphical markdown path: raw markdown is
built into a `WysiwygView`, wrapped as styled preview HTML via
`wysiwyg_preview_pane`, and rendered to pixels through the EXACT same renderer
entrypoint the `md_wysiwyg_ppm` / `md_wysiwyg_gui` apps use
(`simple_web_render_html_to_pixels_with_engine2d_backend`, backend `cpu_simd`).

The oracle is the framebuffer itself — exact pixel count, a non-background ink
count, and an absolute painted color (`0xFF000000`, the default body glyph ink) —
not an `expect(true)` placeholder. Markdown must actually paint ink, and two
different markdown documents must produce two different framebuffers.

Heading lines (`# ...`) are exercised too: the earlier seed crash in
`markdown_strip_heading_marker` (a chained `.slice` on a text temporary) is fixed,
so heading markdown now renders to `<h{n}>` and paints to pixels through the same
path — covering the feature's own `# Title` example and "all variety" of markdown.

**Requirements:** N/A — implementation/architecture evidence for the markdown ->
graphical glue (feature: markdown_wysiwyg_graphical_render_app_2026-06-15).

**Design:** doc/04_architecture/ui/simple_gui_stack.md

## Scenarios

### markdown WYSIWYG graphical render

#### paints markdown through the same cpu_simd renderer with absolute black glyph ink

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- paints markdown through the same cpu_simd renderer with absolute black glyph ink
   - Expected: pixels.len() equals `200 * 60`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("paints markdown through the same cpu_simd renderer with absolute black glyph ink")
# One render proves the whole oracle (size + ink + absolute black glyph +
# surviving white page); T1/T2 previously re-rendered identical content.
val pixels = _render_markdown("Hello body paragraph text", 200, 60)
# (1) exact framebuffer size
expect(pixels.len()).to_equal(200 * 60)
# (2) markdown actually paints — non-background ink exists
expect(_count_non_bg(pixels, 0xFFFFFFFFu32)).to_be_greater_than(0)
# (3) absolute color invariant: the styled paragraph paints opaque black
# glyph ink (#000000 -> 0xFF000000) onto the otherwise-white page.
expect(_count_color(pixels, 0xFF000000u32)).to_be_greater_than(0)
# The white page background still survives around the glyphs.
expect(_count_color(pixels, 0xFFFFFFFFu32)).to_be_greater_than(0)
```

</details>

#### paints a heading line to pixels (the formerly-crashing case)

- paints a heading line to pixels (the formerly-crashing case)
   - Expected: pixels.len() equals `200 * 80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("paints a heading line to pixels (the formerly-crashing case)")
# `# ...` was the crash case and is the feature doc's own example. Prove
# it now paints end-to-end through the same app renderer path.
val pixels = _render_markdown("# Heading\nbody text", 200, 80)
expect(pixels.len()).to_equal(200 * 80)
expect(_count_non_bg(pixels, 0xFFFFFFFFu32)).to_be_greater_than(0)
# A heading + body paints differently than the body alone.
val body_only = _render_markdown("body text", 200, 80)
expect(_pixels_equal(pixels, body_only)).to_be(false)
```

</details>

#### decodes HTML entities so escaped chars paint as single glyphs

- decodes HTML entities so escaped chars paint as single glyphs
   - Expected: esc.len() equals `240 * 40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes HTML entities so escaped chars paint as single glyphs")
# Markdown body escaping turns `&` into `&amp;` inside the preview HTML.
# The renderer must DECODE that back to a single `&` glyph, not paint the
# literal 5-char `&amp;`. Oracle: 8 ampersands and 8 reference glyphs
# decode to the same glyph COUNT, so their ink is the same order of
# magnitude. If entities leaked through undecoded, `&amp;`x8 = 40 painted
# chars would produce several times the ink of 8 glyphs.
val esc = _render_markdown("&&&&&&&&", 240, 40)
val plain = _render_markdown("oooooooo", 240, 40)
expect(esc.len()).to_equal(240 * 40)
val esc_ink = _count_non_bg(esc, 0xFFFFFFFFu32)
val plain_ink = _count_non_bg(plain, 0xFFFFFFFFu32)
expect(esc_ink).to_be_greater_than(0)
expect(esc_ink).to_be_less_than(plain_ink * 3)
```

</details>

#### wraps a long line inside the surface instead of clipping the right edge

- wraps a long line inside the surface instead of clipping the right edge
   - Expected: narrow.len() equals `240 * 100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wraps a long line inside the surface instead of clipping the right edge")
# A long line at a narrow width must WRAP so every glyph paints; it must
# not run off the right edge and clip (web_render_no_line_wrapping_right_edge_clip).
# Oracle: the same text rendered on a narrow-but-tall surface preserves its
# ink (all glyphs survive the wrap), matching a wide surface that fits it
# on fewer lines. A right-edge clip would drop glyphs and lower the ink.
val long_md = "Render markdown to pixels via the shared web Engine2D lane now"
# Surfaces sit just above the painted ink (narrow wraps to ~84px, wide to
# ~50px). The web-layout lane is interpreter-bound under the test runner
# (~0.2 ms/px), so blank rows are pure cost — keep these tight.
val narrow = _render_markdown(long_md, 240, 100)
val wide = _render_markdown(long_md, 480, 64)
expect(narrow.len()).to_equal(240 * 100)
val narrow_ink = _count_non_bg(narrow, 0xFFFFFFFFu32)
val wide_ink = _count_non_bg(wide, 0xFFFFFFFFu32)
expect(wide_ink).to_be_greater_than(0)
# every glyph survives the wrap: narrow ink is within ~10% of the wide ink
# (identical glyph set, just laid out on more lines). A clip would drop a
# large fraction of the glyphs.
expect(narrow_ink * 10).to_be_greater_than(wide_ink * 9)
```

</details>

#### preserves leading indentation in fenced code blocks

- preserves leading indentation in fenced code blocks
   - Expected: indented.len() equals `200 * 32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves leading indentation in fenced code blocks")
# Inside a ``` fence, lines render as preformatted monospace and keep their
# indentation (web_render_preformatted_whitespace_not_preserved). Oracle:
# an indented code line's first black glyph sits well to the right of an
# unindented code line's first glyph. (The ``` delimiters are hidden and a
# leading # stays code, not a heading.)
# One code line paints in the top ~17px; height is sized just above it
# (the renderer is interpreter-bound per-pixel under the test runner).
val indented = _render_markdown("```\n        code_x()\n```", 200, 32)
val plain = _render_markdown("```\ncode_x()\n```", 200, 32)
expect(indented.len()).to_equal(200 * 32)
val indented_col = _min_color_col(indented, 0xFF000000u32, 200)
val plain_col = _min_color_col(plain, 0xFF000000u32, 200)
# both code lines actually paint glyph ink (a missing match would make
# _min_color_col return the surface width 200, so the bound is < 200).
expect(plain_col).to_be_less_than(200)
expect(indented_col).to_be_less_than(200)
# the 8-space indent shifts the first glyph far to the right
expect(indented_col).to_be_greater_than(plain_col + 30)
```

</details>

#### reserves wrapped-text height so a following block does not overlap

- reserves wrapped-text height so a following block does not overlap


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reserves wrapped-text height so a following block does not overlap")
# A block whose inline text wraps to multiple lines must reserve N lines
# of height; otherwise the next block is placed over the wrapped tail
# (web_render_line_height_overlap_at_bottom). Narrow width forces the
# first block's text to wrap; the second block must sit fully below it.
val html = "<div id=\"a\" style=\"font-size: 32px;\">one two three four five six seven eight nine ten</div><p id=\"b\" style=\"font-size: 16px;\">next</p>"
val ya = simple_web_layout_debug_layout_by_id(html, 200, 400, "a", "y").to_i32()
val ha = simple_web_layout_debug_layout_by_id(html, 200, 400, "a", "h").to_i32()
val yb = simple_web_layout_debug_layout_by_id(html, 200, 400, "b", "y").to_i32()
val one_line = 9 * (32 / 8)  # line_h(32) = 9 * glyph_scale(32)
# the first block actually wrapped (taller than a single line)...
expect(ha).to_be_greater_than(one_line)
# ...and reserves at least two lines...
expect(ha).to_be_greater_than(one_line * 2 - 1)
# ...so the next block starts at or below the first block's bottom.
expect(yb).to_be_greater_than(ya + ha - 1)
```

</details>

#### renders different markdown to different framebuffers

- renders different markdown to different framebuffers
   - Expected: a.len() equals `200 * 60`
   - Expected: b.len() equals `200 * 60`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders different markdown to different framebuffers")
val a = _render_markdown("Hello body paragraph text", 200, 60)
val b = _render_markdown("A completely different sentence", 200, 60)
expect(a.len()).to_equal(200 * 60)
expect(b.len()).to_equal(200 * 60)
# (4) distinct markdown content yields distinct pixels — the renderer is
# genuinely consuming the WYSIWYG HTML, not emitting a fixed bitmap.
expect(_pixels_equal(a, b)).to_be(false)
expect(_count_non_bg(b, 0xFFFFFFFFu32)).to_be_greater_than(0)
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


## Related Documentation

- **Requirements:** `N/A — implementation/architecture evidence for the markdown ->`
- **Design:** `doc/04_architecture/ui/simple_gui_stack.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `42b5afe0c2c57a4747d9fd9d1d72e027402c92f011354b12527571a0e0b99eb6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `42b5afe0c2c57a4747d9fd9d1d72e027402c92f011354b12527571a0e0b99eb6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `42b5afe0c2c57a4747d9fd9d1d72e027402c92f011354b12527571a0e0b99eb6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/md_wysiwyg_render_spec.spl
mirror: doc/06_spec/01_unit/app/office/md_wysiwyg_render_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/md_wysiwyg_render_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/md_wysiwyg_render_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/md_wysiwyg_render_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'paints markdown through the same cpu_simd renderer with absolute black glyph ink' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/md_wysiwyg_render_spec.spl:107:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'paints a heading line to pixels (the formerly-crashing case)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/md_wysiwyg_render_spec.spl:119:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decodes HTML entities so escaped chars paint as single glyphs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
