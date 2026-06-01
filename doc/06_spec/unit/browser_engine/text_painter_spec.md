# Text Painter Specification

## Scenarios

### Browser text painter

#### keeps Chrome text glyph scanlines at their native y coordinate

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(browser_chrome_text_scanline_write_y_probe(2)).to_equal(2)
expect(browser_chrome_text_scanline_write_y_probe(48)).to_equal(48)
expect(browser_chrome_text_scanline_write_y_probe(49)).to_equal(49)
```

</details>

#### wraps the Google corpus text into multiple pixel-width lines

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div style='width: 120px; height: 40px; background-color: #2563eb; font-family: Arial, sans-serif'>Google search deterministic compatibility fixture</div></body></html>"
val lines = br_famous_site_corpus_layout_lines(html, 16, 120)
expect(lines.len()).to_equal(4)
expect(lines.join("|")).to_equal("Google search|deterministic|compatibility|fixture")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/unit/browser_engine/text_painter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Browser text painter

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |
