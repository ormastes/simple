# Chrome HTML Compat Geometry Manifest Evidence

- status: pass
- fixtures: 21
- pass count: 21
- fail count: 0
- viewport: 320x240
- build dir: `build/chrome_manifest_full`
- blur/tolerance used: false

This wrapper captures real Chrome headless geometry for each listed
html_compat fixture and compares it against Simple structural boxes.
It compares exact border-box geometry plus computed padding, border
widths, and background color. It does not use blur, downscaling,
pixel tolerance, copied Chromium pixels, or text antialiasing
normalization.

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
