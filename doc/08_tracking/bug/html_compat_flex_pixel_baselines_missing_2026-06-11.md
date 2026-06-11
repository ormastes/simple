# HTML Compat Flex Pixel Baselines Missing

Date: 2026-06-11
Status: Open, partially mitigated

## Summary

The structural geometry path covers flex fixtures `18_flex_grow_weights`
through `24_flex_wrap_reverse_basic`, and the Chrome geometry manifest report
shows all seven rows passing with exact border-box/style comparison. The older
pixel baseline tree under `test/09_baselines/html_compat/` still stops at
`17_flex_col`.

The pixel catalog now lists fixtures 18-24, and the wrapper
`src/app/wm_compare/html_compat.spl` dispatches to the real CLI body and
returns a nonzero status when the harness blocks. Fixture 18 still cannot
produce checked-in `chrome.ppm` / `simple.ppm` pixel baselines on the current
Linux host: under `xvfb-run`, source A fails because the legacy Electron
screenshot path `tools/electron-shell/screenshot.js` is missing, and source B
reports a timeout while rendering the Simple browser-engine capture.

## Evidence

- Present fixtures: `test/fixtures/html_compat/18_flex_grow_weights.html`
  through `test/fixtures/html_compat/24_flex_wrap_reverse_basic.html`
- Missing checked-in pixel baseline artifacts:
  `test/09_baselines/html_compat/18_flex_grow_weights` through
  `test/09_baselines/html_compat/24_flex_wrap_reverse_basic` still do not
  contain committed `chrome.ppm`, `simple.ppm`, and exact comparison
  `report.sdn` rows.
- Pixel catalog coverage:
  `src/app/wm_compare/html_compat_part1.spl` now includes fixture IDs 18-24,
  and `test/03_system/gui/wm_compare/html_compat_spec.spl` asserts
  `catalog.len() == 23`.
- Current focused pixel attempt:
  `xvfb-run ... simple run src/app/wm_compare/html_compat.spl
  --only=18_flex_grow_weights --update-baseline --simple-timeout-ms=1000`
  reaches the fixture and exits `2`, then fails source A on the missing
  Electron screenshot app path and source B on timeout. A longer
  `--simple-timeout-ms=90000` attempt showed the same source-A missing-app
  blocker and source-B timeout.
- Existing structural pass:
  `doc/09_report/chrome_html_compat_geometry_manifest_evidence_2026-06-11.md`
  records `pass_count=21`, `fail_count=0`, and `blur_or_tolerance_used=false`.
- Focused Electron evidence for fixture 18:
  `doc/09_report/electron_html_compat_geometry_evidence_18_flex_grow_weights_2026-06-11.md`
  records `report_status=layout_match` and `mismatch_count=0`.

## Impact

Structural layout parity for these flex rows is stronger than the older pixel
baseline manifest, but the baseline tree is inconsistent. A future pixel
baseline update should either migrate the pixel harness to the maintained
Chrome/Electron live-bitmap capture path, then add exact `chrome.ppm`,
`simple.ppm`, and `report.sdn` rows for 18-24, or explicitly document why flex
rows are structural-only until text/raster parity improves.
