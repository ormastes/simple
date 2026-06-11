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
returns a nonzero status when the harness blocks. The source-A capture path has
been moved off the missing legacy `tools/electron-shell/screenshot.js` app and
onto the maintained `tools/electron-live-bitmap/capture_html_argb.js` plus
`tools/pixel_compare/argb_json_to_ppm.js` conversion path. Fixture 18 can now
write a checked-in Chromium `chrome.ppm` by copying the maintained renderer
output PPM directly instead of re-encoding it through the slow interpreter text
PPM fallback. The current Linux host still cannot produce a complete fixture-18
pixel parity row because the source-B Simple browser-engine capture times out
before writing `simple.ppm`.

## Evidence

- Present fixtures: `test/fixtures/html_compat/18_flex_grow_weights.html`
  through `test/fixtures/html_compat/24_flex_wrap_reverse_basic.html`
- Missing checked-in pixel baseline artifacts:
  `test/09_baselines/html_compat/18_flex_grow_weights` now contains a real
  Chromium `chrome.ppm` and a failure `report.sdn`, but still lacks
  `simple.ppm` and an exact accepted comparison row. Fixtures 19-24 still do
  not contain committed `chrome.ppm`, `simple.ppm`, and exact comparison
  `report.sdn` rows.
- Pixel catalog coverage:
  `src/app/wm_compare/html_compat_part1.spl` now includes fixture IDs 18-24,
  and `test/03_system/gui/wm_compare/html_compat_spec.spl` asserts
  `catalog.len() == 23`.
- Current focused pixel attempt:
  `xvfb-run ... simple run src/app/wm_compare/html_compat.spl
  --only=18_flex_grow_weights --update-baseline --skip-simple
  --simple-timeout-ms=1000` now reaches fixture 18, source A reports
  `ok pixels=76800`, writes
  `test/09_baselines/html_compat/18_flex_grow_weights/chrome.ppm`, and exits
  0. A non-skip run with the same fixture writes the same Chromium PPM, then
  fails closed with exit 2 because source B times out after 1000 ms while
  rendering in the child process.
- Existing structural pass:
  `doc/09_report/chrome_html_compat_geometry_manifest_evidence_2026-06-11.md`
  records `pass_count=21`, `fail_count=0`, and `blur_or_tolerance_used=false`.
- Focused Electron evidence for fixture 18:
  `doc/09_report/electron_html_compat_geometry_evidence_18_flex_grow_weights_2026-06-11.md`
  records `report_status=layout_match` and `mismatch_count=0`.

## Impact

Structural layout parity for these flex rows is stronger than the older pixel
baseline manifest, but the baseline tree is still incomplete. A future pixel
baseline update should finish source-B capture for fixture 18, then add exact
`chrome.ppm`, `simple.ppm`, and accepted `report.sdn` rows for 19-24, or
explicitly document why flex rows remain structural-only until text/raster
parity improves.
