# Chrome HTML Compat Geometry Manifest Evidence

- status: pass
- fixtures: 1
- pass count: 1
- fail count: 0
- viewport: 320x240
- build dir: `build/chrome_html_compat_geometry_fixture22_subpixel_evidence`
- blur/tolerance used: false

This wrapper captures real Chrome headless geometry for each listed
html_compat fixture and compares it against Simple structural boxes.
It compares exact border-box geometry plus computed padding, border
widths, and background color. The structural report also records
diagnostic subpixel client rects plus computed text/style metadata
such as display, align-items, font size, line height, font family,
font weight, and color for diagnosis; those fields are evidence,
not a pixel-parity shortcut.
It does not use blur, downscaling, pixel tolerance, copied Chromium
pixels, or text antialiasing normalization.

## Rows

| Fixture | Status | Mismatches | Geometry | Structural report |
|---------|--------|-----------:|----------|-------------------|
| `22_flex_align_items_baseline` | pass | 0 | `build/chrome_html_compat_geometry_fixture22_subpixel_evidence/22_flex_align_items_baseline_chrome_geometry.json` | `build/chrome_html_compat_geometry_fixture22_subpixel_evidence/22_flex_align_items_baseline_structural_report.sdn` |
