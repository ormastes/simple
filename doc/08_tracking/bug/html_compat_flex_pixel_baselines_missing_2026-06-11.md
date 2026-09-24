# HTML Compat Flex Pixel Baselines Missing

## Closed 2026-09-13 — baselines 18-21, 23-25 now exist; only fixture 22 lacks one

- **measured** `ls test/09_baselines/html_compat/` lists `18_flex_grow_weights`,
  `19_flex_shrink_weights`, `20_flex_basis_override`, `21_flex_wrap_basic`,
  `23_flex_wrap_align_content_center`, `24_flex_wrap_reverse_basic`, `25_flex_justify_space_between`
  — the entry's claim that the tree "stops at 17_flex_col" is no longer true.
- **measured** `18_flex_grow_weights/` contains all three required artifacts:
  `chrome.ppm`, `simple.ppm`, `report.sdn`.
- **measured** Residual, recorded not hidden: `test/fixtures/html_compat/22_flex_align_items_baseline.html`
  exists with no matching baseline directory — a one-fixture gap, not the seven filed here.


Date: 2026-06-11
Status: closed 2026-09-13 (was: Status: Open)

## Summary

The structural geometry path covers flex fixtures `18_flex_grow_weights`
through `24_flex_wrap_reverse_basic`, and the Chrome geometry manifest report
shows all seven rows passing with exact border-box/style comparison. The older
pixel baseline tree under `test/09_baselines/html_compat/` still stops at
`17_flex_col`.

## Evidence

- Present fixtures: `test/fixtures/html_compat/18_flex_grow_weights.html`
  through `test/fixtures/html_compat/24_flex_wrap_reverse_basic.html`
- Missing pixel baseline directories:
  `test/09_baselines/html_compat/18_flex_grow_weights` through
  `test/09_baselines/html_compat/24_flex_wrap_reverse_basic`
- Existing structural pass:
  `doc/09_report/chrome_html_compat_geometry_manifest_evidence_2026-06-11.md`
  records `pass_count=21`, `fail_count=0`, and `blur_or_tolerance_used=false`.
- Focused Electron evidence for fixture 18:
  `doc/09_report/electron_html_compat_geometry_evidence_18_flex_grow_weights_2026-06-11.md`
  records `report_status=layout_match` and `mismatch_count=0`.

## Impact

Structural layout parity for these flex rows is stronger than the older pixel
baseline manifest, but the baseline tree is inconsistent. A future pixel
baseline update should either add exact `chrome.ppm`, `simple.ppm`, and
`report.sdn` rows for 18-24, or explicitly document why flex rows are
structural-only until text/raster parity improves.
