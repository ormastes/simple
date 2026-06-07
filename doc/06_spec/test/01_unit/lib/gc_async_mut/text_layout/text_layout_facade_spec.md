# Text Layout Facade Specification

> <details>

<!-- sdn-diagram:id=text_layout_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=text_layout_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

text_layout_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=text_layout_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Text Layout Facade Specification

## Scenarios

### gc_async_mut text_layout facades

#### re-exports deterministic font metadata and records

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(default_mono_font_name()).to_equal("Fira Code Nerd Font Mono")
expect(default_mono_font_path().contains("FiraCodeNerdFontMono-Regular.ttf")).to_equal(true)
expect(vf_glyph_width(65)).to_equal(11)
expect(vf_glyph_commands(65)[0]).to_equal(0)
expect(vf_glyph_commands(65)[vf_glyph_commands(65).len() - 3]).to_equal(3)

val family = browser_font_face_family_value("Example Sans", "file:///tmp/example.ttf")
expect(browser_font_face_source_from_family_value(family)).to_equal("/tmp/example.ttf")
expect(browser_font_face_local_source_path("'file:///tmp/example.ttf'")).to_equal("/tmp/example.ttf")
expect(browser_font_face_cached_source_path("https://example.test/font.woff2").starts_with(browser_font_cache_dir())).to_equal(true)

val result = BrowserFontMaterializeResult(ok: true, attempted_download: false, status: "available", stdout: "", stderr: "", exit_code: 0)
expect(result.status).to_equal("available")

val glyph = CachedGlyph.empty(65, 24)
expect(glyph.codepoint).to_equal(65)
expect(glyph.pixels.len()).to_equal(0)
expect(GlyphCache.new(2).max_entries).to_equal(2)
expect(FontRenderer.new().use_vector).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/text_layout/text_layout_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut text_layout facades

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
