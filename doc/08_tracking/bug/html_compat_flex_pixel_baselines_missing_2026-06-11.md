# HTML Compat Flex Pixel Baselines Missing

Date: 2026-06-11
Status: Open, fixture 18 pixel row complete

## Summary

The structural geometry path covers flex fixtures `18_flex_grow_weights`
through `24_flex_wrap_reverse_basic`, and the Chrome geometry manifest report
shows all seven rows passing with exact border-box/style comparison. The older
pixel baseline tree under `test/09_baselines/html_compat/` now includes a
complete exact fixture-18 pair, while fixtures 19-24 still lack pixel rows.

The pixel catalog now lists fixtures 18-24, and the wrapper
`src/app/wm_compare/html_compat.spl` dispatches to the real CLI body and
returns a nonzero status when the harness blocks. The source-A capture path has
been moved off the missing legacy `tools/electron-shell/screenshot.js` app and
onto the maintained `tools/electron-live-bitmap/capture_html_argb.js` plus
`tools/pixel_compare/argb_json_to_ppm.js` conversion path. Fixture 18 now writes
both checked-in `chrome.ppm` and `simple.ppm` rows and the report records exact
pixel equality. The source-B worker writes Simple-rendered pixels as binary P6
instead of re-serializing 76,800 pixels through the slow interpreter text-P3
fallback, and the harness resolves `SIMPLE_BINARY` / `SIMPLE_BIN` before
falling back to worktree-local wrappers.

## Evidence

- Present fixtures: `test/fixtures/html_compat/18_flex_grow_weights.html`
  through `test/fixtures/html_compat/24_flex_wrap_reverse_basic.html`
- Missing checked-in pixel baseline artifacts:
  `test/09_baselines/html_compat/18_flex_grow_weights` now contains real
  Chromium and Simple `chrome.ppm` / `simple.ppm` files plus an accepted
  exact `report.sdn` row. Fixtures 19-24 still do not contain committed
  `chrome.ppm`, `simple.ppm`, and exact comparison `report.sdn` rows.
- Pixel catalog coverage:
  `src/app/wm_compare/html_compat_part1.spl` now includes fixture IDs 18-24,
  and `test/03_system/gui/wm_compare/html_compat_spec.spl` asserts
  `catalog.len() == 23`.
- Current focused pixel attempt:
  `xvfb-run ... simple run src/app/wm_compare/html_compat.spl
  --only=18_flex_grow_weights --update-baseline --simple-timeout-ms=1000`
  with `SIMPLE_BINARY` pointing at the current release runtime now reaches
  fixture 18, source A reports `ok pixels=76800`, source B reports
  `ok pixels=76800`, writes both PPMs, and exits 0 with `RESULT: EXACT match`.
  `cmp` reports the two PPMs are byte-identical and both files hash to
  `d8ecff6351645da0337e97a11c705bb1e83e5d11d08a2859b4c146646b7fc62f`.
- Existing structural pass:
  `doc/09_report/chrome_html_compat_geometry_manifest_evidence_2026-06-11.md`
  records `pass_count=21`, `fail_count=0`, and `blur_or_tolerance_used=false`.
- Focused Electron evidence for fixture 18:
  `doc/09_report/electron_html_compat_geometry_evidence_18_flex_grow_weights_2026-06-11.md`
  records `report_status=layout_match` and `mismatch_count=0`.

## Impact

Structural layout parity for these flex rows remains stronger than the older
pixel baseline manifest, and fixture 18 now also has exact pixel evidence. A
future pixel baseline update should extend the same real Chrome/Simple capture
path to fixtures 19-24, or explicitly document why any remaining flex rows stay
structural-only until text/raster parity improves.
