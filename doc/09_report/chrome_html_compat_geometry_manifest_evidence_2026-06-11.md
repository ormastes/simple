# Chrome HTML Compat Geometry Manifest Evidence

- status: pass
- fixtures: 24
- pass count: 24
- fail count: 0
- viewport: 320x240
- build dir: `build/chrome_manifest_full`
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
| `02_block_boxes` | pass | 0 | `build/chrome_manifest_full/02_block_boxes_chrome_geometry.json` | `build/chrome_manifest_full/02_block_boxes_structural_report.sdn` |
| `03_list` | pass | 0 | `build/chrome_manifest_full/03_list_chrome_geometry.json` | `build/chrome_manifest_full/03_list_structural_report.sdn` |
| `04_button` | pass | 0 | `build/chrome_manifest_full/04_button_chrome_geometry.json` | `build/chrome_manifest_full/04_button_structural_report.sdn` |
| `05_text_input` | pass | 0 | `build/chrome_manifest_full/05_text_input_chrome_geometry.json` | `build/chrome_manifest_full/05_text_input_structural_report.sdn` |
| `06_card_panel` | pass | 0 | `build/chrome_manifest_full/06_card_panel_chrome_geometry.json` | `build/chrome_manifest_full/06_card_panel_structural_report.sdn` |
| `07_scrollable_list` | pass | 0 | `build/chrome_manifest_full/07_scrollable_list_chrome_geometry.json` | `build/chrome_manifest_full/07_scrollable_list_structural_report.sdn` |
| `10_colors` | pass | 0 | `build/chrome_manifest_full/10_colors_chrome_geometry.json` | `build/chrome_manifest_full/10_colors_structural_report.sdn` |
| `11_font_size` | pass | 0 | `build/chrome_manifest_full/11_font_size_chrome_geometry.json` | `build/chrome_manifest_full/11_font_size_structural_report.sdn` |
| `12_padding` | pass | 0 | `build/chrome_manifest_full/12_padding_chrome_geometry.json` | `build/chrome_manifest_full/12_padding_structural_report.sdn` |
| `13_margin` | pass | 0 | `build/chrome_manifest_full/13_margin_chrome_geometry.json` | `build/chrome_manifest_full/13_margin_structural_report.sdn` |
| `14_border` | pass | 0 | `build/chrome_manifest_full/14_border_chrome_geometry.json` | `build/chrome_manifest_full/14_border_structural_report.sdn` |
| `15_background` | pass | 0 | `build/chrome_manifest_full/15_background_chrome_geometry.json` | `build/chrome_manifest_full/15_background_structural_report.sdn` |
| `16_flex_row` | pass | 0 | `build/chrome_manifest_full/16_flex_row_chrome_geometry.json` | `build/chrome_manifest_full/16_flex_row_structural_report.sdn` |
| `17_flex_col` | pass | 0 | `build/chrome_manifest_full/17_flex_col_chrome_geometry.json` | `build/chrome_manifest_full/17_flex_col_structural_report.sdn` |
| `18_flex_grow_weights` | pass | 0 | `build/chrome_manifest_full/18_flex_grow_weights_chrome_geometry.json` | `build/chrome_manifest_full/18_flex_grow_weights_structural_report.sdn` |
| `19_flex_shrink_weights` | pass | 0 | `build/chrome_manifest_full/19_flex_shrink_weights_chrome_geometry.json` | `build/chrome_manifest_full/19_flex_shrink_weights_structural_report.sdn` |
| `20_flex_basis_override` | pass | 0 | `build/chrome_manifest_full/20_flex_basis_override_chrome_geometry.json` | `build/chrome_manifest_full/20_flex_basis_override_structural_report.sdn` |
| `21_flex_wrap_basic` | pass | 0 | `build/chrome_manifest_full/21_flex_wrap_basic_chrome_geometry.json` | `build/chrome_manifest_full/21_flex_wrap_basic_structural_report.sdn` |
| `22_flex_align_items_baseline` | pass | 0 | `build/chrome_manifest_full/22_flex_align_items_baseline_chrome_geometry.json` | `build/chrome_manifest_full/22_flex_align_items_baseline_structural_report.sdn` |
| `23_flex_wrap_align_content_center` | pass | 0 | `build/chrome_manifest_full/23_flex_wrap_align_content_center_chrome_geometry.json` | `build/chrome_manifest_full/23_flex_wrap_align_content_center_structural_report.sdn` |
| `24_flex_wrap_reverse_basic` | pass | 0 | `build/chrome_manifest_full/24_flex_wrap_reverse_basic_chrome_geometry.json` | `build/chrome_manifest_full/24_flex_wrap_reverse_basic_structural_report.sdn` |
| `25_flex_justify_space_between` | pass | 0 | `build/chrome_manifest_full/25_flex_justify_space_between_chrome_geometry.json` | `build/chrome_manifest_full/25_flex_justify_space_between_structural_report.sdn` |
| `26_flex_gap_basic` | pass | 0 | `build/chrome_manifest_full/26_flex_gap_basic_chrome_geometry.json` | `build/chrome_manifest_full/26_flex_gap_basic_structural_report.sdn` |
| `27_absolute_position_basic` | pass | 0 | `build/chrome_manifest_full/27_absolute_position_basic_chrome_geometry.json` | `build/chrome_manifest_full/27_absolute_position_basic_structural_report.sdn` |

## Subpixel Diagnostics

Fractional boxes are Chrome boxes whose captured client rect has a
non-integer left, top, width, or height. Max fractional residue is
the largest distance from an integer CSS pixel among those fields.

| Fixture | Fractional boxes | Max fractional residue | Labels |
|---------|-----------------:|-----------------------:|--------|
| `02_block_boxes` | 0 | 0.000 | `` |
| `03_list` | 0 | 0.000 | `` |
| `04_button` | 0 | 0.000 | `` |
| `05_text_input` | 0 | 0.000 | `` |
| `06_card_panel` | 0 | 0.000 | `` |
| `07_scrollable_list` | 0 | 0.000 | `` |
| `10_colors` | 0 | 0.000 | `` |
| `11_font_size` | 0 | 0.000 | `` |
| `12_padding` | 0 | 0.000 | `` |
| `13_margin` | 0 | 0.000 | `` |
| `14_border` | 0 | 0.000 | `` |
| `15_background` | 0 | 0.000 | `` |
| `16_flex_row` | 0 | 0.000 | `` |
| `17_flex_col` | 0 | 0.000 | `` |
| `18_flex_grow_weights` | 2 | 0.328 | `grow_one,grow_two` |
| `19_flex_shrink_weights` | 0 | 0.000 | `` |
| `20_flex_basis_override` | 0 | 0.000 | `` |
| `21_flex_wrap_basic` | 0 | 0.000 | `` |
| `22_flex_align_items_baseline` | 2 | 0.328 | `baseline_big,baseline_small` |
| `23_flex_wrap_align_content_center` | 0 | 0.000 | `` |
| `24_flex_wrap_reverse_basic` | 0 | 0.000 | `` |
| `25_flex_justify_space_between` | 0 | 0.000 | `` |
| `26_flex_gap_basic` | 0 | 0.000 | `` |
| `27_absolute_position_basic` | 0 | 0.000 | `` |
