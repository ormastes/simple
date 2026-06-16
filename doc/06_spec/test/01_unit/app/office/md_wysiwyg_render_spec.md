# Markdown WYSIWYG Graphical Render Specification

> This unit spec proves the end-to-end graphical markdown path: raw markdown is built into a `WysiwygView`, wrapped as styled preview HTML via `wysiwyg_preview_pane`, and rendered to pixels through the EXACT same renderer entrypoint the `md_wysiwyg_ppm` / `md_wysiwyg_gui` apps use (`simple_web_render_html_to_pixels_with_engine2d_backend`, backend `cpu_simd`).

<!-- sdn-diagram:id=md_wysiwyg_render_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=md_wysiwyg_render_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

md_wysiwyg_render_spec -> std
md_wysiwyg_render_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=md_wysiwyg_render_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

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
| Updated | 2026-06-01 |
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

#### paints markdown through the same cpu_simd renderer the apps use

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = _render_markdown("Hello body paragraph text", 200, 60)
# (1) exact framebuffer size
expect(pixels.len()).to_equal(200 * 60)
# (2) markdown actually paints — non-background ink exists
expect(_count_non_bg(pixels, 0xFFFFFFFFu32)).to_be_greater_than(0)
```

</details>

#### paints absolute black glyph ink for styled markdown body text

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = _render_markdown("Hello body paragraph text", 200, 60)
expect(pixels.len()).to_equal(200 * 60)
# (3) absolute color invariant: the styled paragraph paints opaque black
# glyph ink (#000000 -> 0xFF000000) onto the otherwise-white page.
expect(_count_color(pixels, 0xFF000000u32)).to_be_greater_than(0)
# The white page background still survives around the glyphs.
expect(_count_color(pixels, 0xFFFFFFFFu32)).to_be_greater_than(0)
```

</details>

#### paints a heading line to pixels (the formerly-crashing case)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# `# ...` was the crash case and is the feature doc's own example. Prove
# it now paints end-to-end through the same app renderer path.
val pixels = _render_markdown("# Heading\nbody text", 200, 80)
expect(pixels.len()).to_equal(200 * 80)
expect(_count_non_bg(pixels, 0xFFFFFFFFu32)).to_be_greater_than(0)
# A heading + body paints differently than the body alone.
val body_only = _render_markdown("body text", 200, 80)
expect(_pixels_equal(pixels, body_only)).to_equal(false)
```

</details>

#### renders different markdown to different framebuffers

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = _render_markdown("Hello body paragraph text", 200, 60)
val b = _render_markdown("A completely different sentence", 200, 60)
expect(a.len()).to_equal(200 * 60)
expect(b.len()).to_equal(200 * 60)
# (4) distinct markdown content yields distinct pixels — the renderer is
# genuinely consuming the WYSIWYG HTML, not emitting a fixed bitmap.
expect(_pixels_equal(a, b)).to_equal(false)
expect(_count_non_bg(b, 0xFFFFFFFFu32)).to_be_greater_than(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [N/A — implementation/architecture evidence for the markdown ->](N/A — implementation/architecture evidence for the markdown ->)
- **Design:** [doc/04_architecture/ui/simple_gui_stack.md](doc/04_architecture/ui/simple_gui_stack.md)


</details>
