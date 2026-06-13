# Chrome HTML Compat Geometry Manifest Evidence

- status: pass
- fixtures: 100
- pass count: 100
- fail count: 0
- viewport: 320x240
- build dir: `build/chrome_html_compat_geometry_manifest_101_rebased_full`
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
| `00_text_only` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/00_text_only_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/00_text_only_structural_report.sdn` |
| `01_inline_text` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/01_inline_text_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/01_inline_text_structural_report.sdn` |
| `02_block_boxes` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/02_block_boxes_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/02_block_boxes_structural_report.sdn` |
| `03_list` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/03_list_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/03_list_structural_report.sdn` |
| `04_button` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/04_button_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/04_button_structural_report.sdn` |
| `05_text_input` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/05_text_input_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/05_text_input_structural_report.sdn` |
| `06_card_panel` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/06_card_panel_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/06_card_panel_structural_report.sdn` |
| `07_scrollable_list` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/07_scrollable_list_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/07_scrollable_list_structural_report.sdn` |
| `08_inline_siblings` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/08_inline_siblings_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/08_inline_siblings_structural_report.sdn` |
| `10_colors` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/10_colors_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/10_colors_structural_report.sdn` |
| `11_font_size` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/11_font_size_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/11_font_size_structural_report.sdn` |
| `12_padding` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/12_padding_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/12_padding_structural_report.sdn` |
| `13_margin` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/13_margin_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/13_margin_structural_report.sdn` |
| `14_border` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/14_border_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/14_border_structural_report.sdn` |
| `15_background` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/15_background_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/15_background_structural_report.sdn` |
| `16_flex_row` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/16_flex_row_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/16_flex_row_structural_report.sdn` |
| `17_flex_col` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/17_flex_col_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/17_flex_col_structural_report.sdn` |
| `18_flex_grow_weights` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/18_flex_grow_weights_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/18_flex_grow_weights_structural_report.sdn` |
| `19_flex_shrink_weights` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/19_flex_shrink_weights_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/19_flex_shrink_weights_structural_report.sdn` |
| `20_flex_basis_override` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/20_flex_basis_override_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/20_flex_basis_override_structural_report.sdn` |
| `21_flex_wrap_basic` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/21_flex_wrap_basic_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/21_flex_wrap_basic_structural_report.sdn` |
| `22_flex_align_items_baseline` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/22_flex_align_items_baseline_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/22_flex_align_items_baseline_structural_report.sdn` |
| `23_flex_wrap_align_content_center` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/23_flex_wrap_align_content_center_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/23_flex_wrap_align_content_center_structural_report.sdn` |
| `24_flex_wrap_reverse_basic` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/24_flex_wrap_reverse_basic_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/24_flex_wrap_reverse_basic_structural_report.sdn` |
| `25_flex_justify_space_between` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/25_flex_justify_space_between_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/25_flex_justify_space_between_structural_report.sdn` |
| `26_flex_gap_basic` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/26_flex_gap_basic_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/26_flex_gap_basic_structural_report.sdn` |
| `27_absolute_position_basic` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/27_absolute_position_basic_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/27_absolute_position_basic_structural_report.sdn` |
| `28_display_contents_basic` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/28_display_contents_basic_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/28_display_contents_basic_structural_report.sdn` |
| `29_box_sizing_border_box` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/29_box_sizing_border_box_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/29_box_sizing_border_box_structural_report.sdn` |
| `30_min_max_width_basic` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/30_min_max_width_basic_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/30_min_max_width_basic_structural_report.sdn` |
| `31_flex_align_items_center` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/31_flex_align_items_center_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/31_flex_align_items_center_structural_report.sdn` |
| `32_flex_align_items_flex_end` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/32_flex_align_items_flex_end_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/32_flex_align_items_flex_end_structural_report.sdn` |
| `33_flex_justify_flex_end` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/33_flex_justify_flex_end_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/33_flex_justify_flex_end_structural_report.sdn` |
| `34_flex_justify_center` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/34_flex_justify_center_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/34_flex_justify_center_structural_report.sdn` |
| `35_flex_align_items_stretch` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/35_flex_align_items_stretch_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/35_flex_align_items_stretch_structural_report.sdn` |
| `36_flex_align_self_flex_end` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/36_flex_align_self_flex_end_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/36_flex_align_self_flex_end_structural_report.sdn` |
| `37_flex_gap_justify_center` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/37_flex_gap_justify_center_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/37_flex_gap_justify_center_structural_report.sdn` |
| `38_flex_gap_space_between` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/38_flex_gap_space_between_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/38_flex_gap_space_between_structural_report.sdn` |
| `39_flex_gap_flex_end` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/39_flex_gap_flex_end_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/39_flex_gap_flex_end_structural_report.sdn` |
| `40_flex_column_gap_justify_center` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/40_flex_column_gap_justify_center_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/40_flex_column_gap_justify_center_structural_report.sdn` |
| `41_flex_column_gap_space_between` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/41_flex_column_gap_space_between_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/41_flex_column_gap_space_between_structural_report.sdn` |
| `42_flex_column_gap_flex_end` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/42_flex_column_gap_flex_end_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/42_flex_column_gap_flex_end_structural_report.sdn` |
| `43_flex_column_align_items_center` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/43_flex_column_align_items_center_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/43_flex_column_align_items_center_structural_report.sdn` |
| `44_flex_column_align_items_flex_end` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/44_flex_column_align_items_flex_end_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/44_flex_column_align_items_flex_end_structural_report.sdn` |
| `45_flex_column_align_self_flex_end` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/45_flex_column_align_self_flex_end_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/45_flex_column_align_self_flex_end_structural_report.sdn` |
| `46_flex_column_align_items_stretch` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/46_flex_column_align_items_stretch_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/46_flex_column_align_items_stretch_structural_report.sdn` |
| `47_flex_column_align_self_center` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/47_flex_column_align_self_center_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/47_flex_column_align_self_center_structural_report.sdn` |
| `48_flex_column_align_self_stretch` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/48_flex_column_align_self_stretch_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/48_flex_column_align_self_stretch_structural_report.sdn` |
| `49_flex_column_justify_space_around` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/49_flex_column_justify_space_around_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/49_flex_column_justify_space_around_structural_report.sdn` |
| `50_flex_row_justify_space_around` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/50_flex_row_justify_space_around_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/50_flex_row_justify_space_around_structural_report.sdn` |
| `51_flex_row_justify_space_evenly` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/51_flex_row_justify_space_evenly_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/51_flex_row_justify_space_evenly_structural_report.sdn` |
| `52_flex_column_justify_space_evenly` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/52_flex_column_justify_space_evenly_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/52_flex_column_justify_space_evenly_structural_report.sdn` |
| `53_flex_wrap_align_content_flex_end` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/53_flex_wrap_align_content_flex_end_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/53_flex_wrap_align_content_flex_end_structural_report.sdn` |
| `54_flex_wrap_align_content_space_between` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/54_flex_wrap_align_content_space_between_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/54_flex_wrap_align_content_space_between_structural_report.sdn` |
| `55_flex_wrap_align_content_space_around` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/55_flex_wrap_align_content_space_around_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/55_flex_wrap_align_content_space_around_structural_report.sdn` |
| `56_flex_wrap_align_content_space_evenly` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/56_flex_wrap_align_content_space_evenly_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/56_flex_wrap_align_content_space_evenly_structural_report.sdn` |
| `57_flex_wrap_gap_basic` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/57_flex_wrap_gap_basic_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/57_flex_wrap_gap_basic_structural_report.sdn` |
| `58_flex_wrap_axis_gap_basic` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/58_flex_wrap_axis_gap_basic_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/58_flex_wrap_axis_gap_basic_structural_report.sdn` |
| `59_flex_column_axis_gap_basic` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/59_flex_column_axis_gap_basic_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/59_flex_column_axis_gap_basic_structural_report.sdn` |
| `60_flex_align_self_mixed_overrides` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/60_flex_align_self_mixed_overrides_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/60_flex_align_self_mixed_overrides_structural_report.sdn` |
| `61_flex_gap_space_around` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/61_flex_gap_space_around_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/61_flex_gap_space_around_structural_report.sdn` |
| `62_flex_column_gap_space_around` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/62_flex_column_gap_space_around_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/62_flex_column_gap_space_around_structural_report.sdn` |
| `63_flex_wrap_gap_align_content_space_between` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/63_flex_wrap_gap_align_content_space_between_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/63_flex_wrap_gap_align_content_space_between_structural_report.sdn` |
| `64_flex_wrap_gap_align_content_space_around` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/64_flex_wrap_gap_align_content_space_around_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/64_flex_wrap_gap_align_content_space_around_structural_report.sdn` |
| `65_flex_wrap_gap_align_content_space_evenly` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/65_flex_wrap_gap_align_content_space_evenly_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/65_flex_wrap_gap_align_content_space_evenly_structural_report.sdn` |
| `66_flex_wrap_gap_align_content_flex_end` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/66_flex_wrap_gap_align_content_flex_end_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/66_flex_wrap_gap_align_content_flex_end_structural_report.sdn` |
| `67_flex_wrap_gap_align_content_center` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/67_flex_wrap_gap_align_content_center_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/67_flex_wrap_gap_align_content_center_structural_report.sdn` |
| `68_flex_wrap_gap_align_content_stretch` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/68_flex_wrap_gap_align_content_stretch_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/68_flex_wrap_gap_align_content_stretch_structural_report.sdn` |
| `69_flex_wrap_gap_align_content_flex_start` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/69_flex_wrap_gap_align_content_flex_start_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/69_flex_wrap_gap_align_content_flex_start_structural_report.sdn` |
| `70_flex_wrap_gap_align_content_normal` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/70_flex_wrap_gap_align_content_normal_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/70_flex_wrap_gap_align_content_normal_structural_report.sdn` |
| `71_flex_wrap_gap_align_content_end` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/71_flex_wrap_gap_align_content_end_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/71_flex_wrap_gap_align_content_end_structural_report.sdn` |
| `72_flex_wrap_gap_align_content_start` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/72_flex_wrap_gap_align_content_start_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/72_flex_wrap_gap_align_content_start_structural_report.sdn` |
| `73_flex_wrap_gap_align_content_unsafe_center` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/73_flex_wrap_gap_align_content_unsafe_center_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/73_flex_wrap_gap_align_content_unsafe_center_structural_report.sdn` |
| `74_flex_gap_justify_unsafe_center` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/74_flex_gap_justify_unsafe_center_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/74_flex_gap_justify_unsafe_center_structural_report.sdn` |
| `75_flex_gap_justify_unsafe_center_overflow` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/75_flex_gap_justify_unsafe_center_overflow_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/75_flex_gap_justify_unsafe_center_overflow_structural_report.sdn` |
| `76_flex_gap_justify_unsafe_center_no_shrink_overflow` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/76_flex_gap_justify_unsafe_center_no_shrink_overflow_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/76_flex_gap_justify_unsafe_center_no_shrink_overflow_structural_report.sdn` |
| `77_flex_gap_justify_safe_center_no_shrink_overflow` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/77_flex_gap_justify_safe_center_no_shrink_overflow_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/77_flex_gap_justify_safe_center_no_shrink_overflow_structural_report.sdn` |
| `78_flex_column_gap_justify_unsafe_center_no_shrink_overflow` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/78_flex_column_gap_justify_unsafe_center_no_shrink_overflow_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/78_flex_column_gap_justify_unsafe_center_no_shrink_overflow_structural_report.sdn` |
| `79_flex_column_gap_justify_safe_center_no_shrink_overflow` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/79_flex_column_gap_justify_safe_center_no_shrink_overflow_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/79_flex_column_gap_justify_safe_center_no_shrink_overflow_structural_report.sdn` |
| `80_flex_gap_justify_end` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/80_flex_gap_justify_end_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/80_flex_gap_justify_end_structural_report.sdn` |
| `81_flex_column_gap_justify_end` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/81_flex_column_gap_justify_end_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/81_flex_column_gap_justify_end_structural_report.sdn` |
| `82_flex_gap_align_items_end` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/82_flex_gap_align_items_end_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/82_flex_gap_align_items_end_structural_report.sdn` |
| `83_flex_auto_margin_align_center` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/83_flex_auto_margin_align_center_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/83_flex_auto_margin_align_center_structural_report.sdn` |
| `84_flex_column_auto_margin_align_center` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/84_flex_column_auto_margin_align_center_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/84_flex_column_auto_margin_align_center_structural_report.sdn` |
| `85_flex_cross_auto_margin_top` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/85_flex_cross_auto_margin_top_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/85_flex_cross_auto_margin_top_structural_report.sdn` |
| `86_flex_row_cross_auto_margin_align_center` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/86_flex_row_cross_auto_margin_align_center_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/86_flex_row_cross_auto_margin_align_center_structural_report.sdn` |
| `87_flex_row_cross_auto_margin_both_override_end` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/87_flex_row_cross_auto_margin_both_override_end_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/87_flex_row_cross_auto_margin_both_override_end_structural_report.sdn` |
| `88_flex_order_basic` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/88_flex_order_basic_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/88_flex_order_basic_structural_report.sdn` |
| `89_percent_content_box_padding` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/89_percent_content_box_padding_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/89_percent_content_box_padding_structural_report.sdn` |
| `90_absolute_inset_stretch` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/90_absolute_inset_stretch_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/90_absolute_inset_stretch_structural_report.sdn` |
| `91_percent_margin_basic` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/91_percent_margin_basic_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/91_percent_margin_basic_structural_report.sdn` |
| `92_percent_height_definite_parent` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/92_percent_height_definite_parent_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/92_percent_height_definite_parent_structural_report.sdn` |
| `93_flex_percent_height_cross_axis` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/93_flex_percent_height_cross_axis_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/93_flex_percent_height_cross_axis_structural_report.sdn` |
| `94_flex_column_percent_height_main_axis` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/94_flex_column_percent_height_main_axis_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/94_flex_column_percent_height_main_axis_structural_report.sdn` |
| `95_absolute_percent_height_basic` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/95_absolute_percent_height_basic_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/95_absolute_percent_height_basic_structural_report.sdn` |
| `96_absolute_percent_height_bottom` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/96_absolute_percent_height_bottom_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/96_absolute_percent_height_bottom_structural_report.sdn` |
| `97_min_height_definite_parent` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/97_min_height_definite_parent_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/97_min_height_definite_parent_structural_report.sdn` |
| `98_absolute_percent_width_right` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/98_absolute_percent_width_right_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/98_absolute_percent_width_right_structural_report.sdn` |
| `100_relative_offset_basic` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/100_relative_offset_basic_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/100_relative_offset_basic_structural_report.sdn` |
| `101_max_height_basic` | pass | 0 | `build/chrome_html_compat_geometry_manifest_101_rebased_full/101_max_height_basic_chrome_geometry.json` | `build/chrome_html_compat_geometry_manifest_101_rebased_full/101_max_height_basic_structural_report.sdn` |

## Subpixel Diagnostics

Fractional boxes are Chrome boxes whose captured client rect has a
non-integer left, top, width, or height. Max fractional residue is
the largest distance from an integer CSS pixel among those fields.

| Fixture | Fractional boxes | Max fractional residue | Labels |
|---------|-----------------:|-----------------------:|--------|
| `00_text_only` | 0 | 0.000 | `` |
| `01_inline_text` | 1 | 0.328 | `inline_span` |
| `02_block_boxes` | 0 | 0.000 | `` |
| `03_list` | 0 | 0.000 | `` |
| `04_button` | 0 | 0.000 | `` |
| `05_text_input` | 0 | 0.000 | `` |
| `06_card_panel` | 0 | 0.000 | `` |
| `07_scrollable_list` | 0 | 0.000 | `` |
| `08_inline_siblings` | 2 | 0.344 | `inline_siblings_first,inline_siblings_second` |
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
| `28_display_contents_basic` | 0 | 0.000 | `` |
| `29_box_sizing_border_box` | 0 | 0.000 | `` |
| `30_min_max_width_basic` | 0 | 0.000 | `` |
| `31_flex_align_items_center` | 0 | 0.000 | `` |
| `32_flex_align_items_flex_end` | 0 | 0.000 | `` |
| `33_flex_justify_flex_end` | 0 | 0.000 | `` |
| `34_flex_justify_center` | 0 | 0.000 | `` |
| `35_flex_align_items_stretch` | 0 | 0.000 | `` |
| `36_flex_align_self_flex_end` | 0 | 0.000 | `` |
| `37_flex_gap_justify_center` | 0 | 0.000 | `` |
| `38_flex_gap_space_between` | 0 | 0.000 | `` |
| `39_flex_gap_flex_end` | 0 | 0.000 | `` |
| `40_flex_column_gap_justify_center` | 0 | 0.000 | `` |
| `41_flex_column_gap_space_between` | 0 | 0.000 | `` |
| `42_flex_column_gap_flex_end` | 0 | 0.000 | `` |
| `43_flex_column_align_items_center` | 0 | 0.000 | `` |
| `44_flex_column_align_items_flex_end` | 0 | 0.000 | `` |
| `45_flex_column_align_self_flex_end` | 0 | 0.000 | `` |
| `46_flex_column_align_items_stretch` | 0 | 0.000 | `` |
| `47_flex_column_align_self_center` | 0 | 0.000 | `` |
| `48_flex_column_align_self_stretch` | 0 | 0.000 | `` |
| `49_flex_column_justify_space_around` | 0 | 0.000 | `` |
| `50_flex_row_justify_space_around` | 0 | 0.000 | `` |
| `51_flex_row_justify_space_evenly` | 0 | 0.000 | `` |
| `52_flex_column_justify_space_evenly` | 0 | 0.000 | `` |
| `53_flex_wrap_align_content_flex_end` | 0 | 0.000 | `` |
| `54_flex_wrap_align_content_space_between` | 0 | 0.000 | `` |
| `55_flex_wrap_align_content_space_around` | 0 | 0.000 | `` |
| `56_flex_wrap_align_content_space_evenly` | 0 | 0.000 | `` |
| `57_flex_wrap_gap_basic` | 0 | 0.000 | `` |
| `58_flex_wrap_axis_gap_basic` | 0 | 0.000 | `` |
| `59_flex_column_axis_gap_basic` | 0 | 0.000 | `` |
| `60_flex_align_self_mixed_overrides` | 0 | 0.000 | `` |
| `61_flex_gap_space_around` | 0 | 0.000 | `` |
| `62_flex_column_gap_space_around` | 0 | 0.000 | `` |
| `63_flex_wrap_gap_align_content_space_between` | 0 | 0.000 | `` |
| `64_flex_wrap_gap_align_content_space_around` | 0 | 0.000 | `` |
| `65_flex_wrap_gap_align_content_space_evenly` | 0 | 0.000 | `` |
| `66_flex_wrap_gap_align_content_flex_end` | 0 | 0.000 | `` |
| `67_flex_wrap_gap_align_content_center` | 0 | 0.000 | `` |
| `68_flex_wrap_gap_align_content_stretch` | 0 | 0.000 | `` |
| `69_flex_wrap_gap_align_content_flex_start` | 0 | 0.000 | `` |
| `70_flex_wrap_gap_align_content_normal` | 0 | 0.000 | `` |
| `71_flex_wrap_gap_align_content_end` | 0 | 0.000 | `` |
| `72_flex_wrap_gap_align_content_start` | 0 | 0.000 | `` |
| `73_flex_wrap_gap_align_content_unsafe_center` | 0 | 0.000 | `` |
| `74_flex_gap_justify_unsafe_center` | 0 | 0.000 | `` |
| `75_flex_gap_justify_unsafe_center_overflow` | 3 | 0.422 | `gap_unsafe_center_overflow_a,gap_unsafe_center_overflow_b,gap_unsafe_center_overflow_c` |
| `76_flex_gap_justify_unsafe_center_no_shrink_overflow` | 0 | 0.000 | `` |
| `77_flex_gap_justify_safe_center_no_shrink_overflow` | 0 | 0.000 | `` |
| `78_flex_column_gap_justify_unsafe_center_no_shrink_overflow` | 0 | 0.000 | `` |
| `79_flex_column_gap_justify_safe_center_no_shrink_overflow` | 0 | 0.000 | `` |
| `80_flex_gap_justify_end` | 0 | 0.000 | `` |
| `81_flex_column_gap_justify_end` | 0 | 0.000 | `` |
| `82_flex_gap_align_items_end` | 0 | 0.000 | `` |
| `83_flex_auto_margin_align_center` | 0 | 0.000 | `` |
| `84_flex_column_auto_margin_align_center` | 0 | 0.000 | `` |
| `85_flex_cross_auto_margin_top` | 0 | 0.000 | `` |
| `86_flex_row_cross_auto_margin_align_center` | 0 | 0.000 | `` |
| `87_flex_row_cross_auto_margin_both_override_end` | 0 | 0.000 | `` |
| `88_flex_order_basic` | 0 | 0.000 | `` |
| `89_percent_content_box_padding` | 0 | 0.000 | `` |
| `90_absolute_inset_stretch` | 0 | 0.000 | `` |
| `91_percent_margin_basic` | 0 | 0.000 | `` |
| `92_percent_height_definite_parent` | 0 | 0.000 | `` |
| `93_flex_percent_height_cross_axis` | 0 | 0.000 | `` |
| `94_flex_column_percent_height_main_axis` | 0 | 0.000 | `` |
| `95_absolute_percent_height_basic` | 0 | 0.000 | `` |
| `96_absolute_percent_height_bottom` | 0 | 0.000 | `` |
| `97_min_height_definite_parent` | 0 | 0.000 | `` |
| `98_absolute_percent_width_right` | 0 | 0.000 | `` |
| `100_relative_offset_basic` | 0 | 0.000 | `` |
| `101_max_height_basic` | 0 | 0.000 | `` |
