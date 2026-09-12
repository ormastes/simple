# HTML Compat Flex Pixel Baselines Missing

Date: 2026-06-11
Status: Open -> CLOSED-STALE (2026-09-12: not re-verified this pass)

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

## Triage 2026-09-12
Missing-baseline-artifact gap, not a logic bug; not re-run in this pass. Older than 45 days; closing per age policy. Evidence: seed binary /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
