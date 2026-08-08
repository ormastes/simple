# Chrome HTML Compat Geometry Manifest Evidence

- status: pass
- fixtures: 7
- pass count: 7
- fail count: 0
- viewport: 320x240
- build dir: `build/chrome_html_compat_geometry_flex_fraction_evidence`
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
| `18_flex_grow_weights` | pass | 0 | `build/chrome_html_compat_geometry_flex_fraction_evidence/18_flex_grow_weights_chrome_geometry.json` | `build/chrome_html_compat_geometry_flex_fraction_evidence/18_flex_grow_weights_structural_report.sdn` |
| `19_flex_shrink_weights` | pass | 0 | `build/chrome_html_compat_geometry_flex_fraction_evidence/19_flex_shrink_weights_chrome_geometry.json` | `build/chrome_html_compat_geometry_flex_fraction_evidence/19_flex_shrink_weights_structural_report.sdn` |
| `20_flex_basis_override` | pass | 0 | `build/chrome_html_compat_geometry_flex_fraction_evidence/20_flex_basis_override_chrome_geometry.json` | `build/chrome_html_compat_geometry_flex_fraction_evidence/20_flex_basis_override_structural_report.sdn` |
| `21_flex_wrap_basic` | pass | 0 | `build/chrome_html_compat_geometry_flex_fraction_evidence/21_flex_wrap_basic_chrome_geometry.json` | `build/chrome_html_compat_geometry_flex_fraction_evidence/21_flex_wrap_basic_structural_report.sdn` |
| `22_flex_align_items_baseline` | pass | 0 | `build/chrome_html_compat_geometry_flex_fraction_evidence/22_flex_align_items_baseline_chrome_geometry.json` | `build/chrome_html_compat_geometry_flex_fraction_evidence/22_flex_align_items_baseline_structural_report.sdn` |
| `23_flex_wrap_align_content_center` | pass | 0 | `build/chrome_html_compat_geometry_flex_fraction_evidence/23_flex_wrap_align_content_center_chrome_geometry.json` | `build/chrome_html_compat_geometry_flex_fraction_evidence/23_flex_wrap_align_content_center_structural_report.sdn` |
| `24_flex_wrap_reverse_basic` | pass | 0 | `build/chrome_html_compat_geometry_flex_fraction_evidence/24_flex_wrap_reverse_basic_chrome_geometry.json` | `build/chrome_html_compat_geometry_flex_fraction_evidence/24_flex_wrap_reverse_basic_structural_report.sdn` |

## Subpixel Diagnostics

Fractional boxes are Chrome boxes whose captured client rect has a
non-integer left, top, width, or height. Max fractional residue is
the largest distance from an integer CSS pixel among those fields.

| Fixture | Fractional boxes | Max fractional residue | Labels |
|---------|-----------------:|-----------------------:|--------|
| `18_flex_grow_weights` | 2 | 0.328 | `grow_one,grow_two` |
| `19_flex_shrink_weights` | 0 | 0.000 | `` |
| `20_flex_basis_override` | 0 | 0.000 | `` |
| `21_flex_wrap_basic` | 0 | 0.000 | `` |
| `22_flex_align_items_baseline` | 2 | 0.328 | `baseline_big,baseline_small` |
| `23_flex_wrap_align_content_center` | 0 | 0.000 | `` |
| `24_flex_wrap_reverse_basic` | 0 | 0.000 | `` |
