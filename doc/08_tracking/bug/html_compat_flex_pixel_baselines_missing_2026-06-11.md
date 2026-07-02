# HTML Compat Flex Pixel Baselines Missing

Date: 2026-06-11
Status: Resolved (2026-07-02) — pixel baselines added for the geometry-only
flex rows; the sole remaining gap (`22_flex_align_items_baseline`) is a
text-baseline fixture that stays structural-only per the text/raster-parity
exception this bug already documented below.

## Resolution (2026-07-02)

Exact pixel baselines now exist and compare bit-exact (`different_pixels: 0`,
`tolerance_acceptance_allowed: false`) for:

- `test/09_baselines/html_compat/18_flex_grow_weights`
- `test/09_baselines/html_compat/19_flex_shrink_weights`
- `test/09_baselines/html_compat/20_flex_basis_override`
- `test/09_baselines/html_compat/21_flex_wrap_basic`
- `test/09_baselines/html_compat/23_flex_wrap_align_content_center`
- `test/09_baselines/html_compat/24_flex_wrap_reverse_basic`

Each directory carries `chrome.ppm`, `simple.ppm`, and `report.sdn`. Only
`22_flex_align_items_baseline` remains without a pixel baseline: it exercises
mixed font-size text baseline alignment, where the Simple bitmap font
legitimately differs from Chromium's raster (see memory 2026-06-02). It stays
structural-only — the explicitly-documented alternative in the Impact section
below — and is still covered by the structural geometry manifest.

Weighted flex-grow distribution and wrap-reverse ordering (the layout behavior
behind these fixtures) are additionally proven by
`test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_flex_grow_weighted_spec.spl`.

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
