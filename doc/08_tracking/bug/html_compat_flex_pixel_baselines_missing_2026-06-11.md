# HTML Compat Flex Pixel Baselines Missing

Date: 2026-06-11
Status: Open, fixture 22 text raster row blocked

## Summary

The structural geometry path covers flex fixtures `18_flex_grow_weights`
through `24_flex_wrap_reverse_basic`, and the Chrome geometry manifest report
shows all seven rows passing with exact border-box/style comparison. The older
pixel baseline tree under `test/09_baselines/html_compat/` now includes exact
Chrome/Simple pixel rows for fixtures 18-21 and 23-24. Fixture 22 remains
blocked by real text glyph raster/default-font differences.

The pixel catalog now lists fixtures 18-24, and the wrapper
`src/app/wm_compare/html_compat.spl` dispatches to the real CLI body and
returns a nonzero status when the harness blocks. The source-A capture path has
been moved off the missing legacy `tools/electron-shell/screenshot.js` app and
onto the maintained `tools/electron-live-bitmap/capture_html_argb.js` plus
`tools/pixel_compare/argb_json_to_ppm.js` conversion path. Fixtures 18-21 and
23-24 now write checked-in `chrome.ppm` and `simple.ppm` rows and their reports
record exact pixel equality. The source-B worker writes Simple-rendered pixels
as binary P6 instead of re-serializing 76,800 pixels through the slow
interpreter text-P3 fallback, and the harness resolves `SIMPLE_BINARY` /
`SIMPLE_BIN` before falling back to worktree-local wrappers.

## Evidence

- Present fixtures: `test/fixtures/html_compat/18_flex_grow_weights.html`
  through `test/fixtures/html_compat/24_flex_wrap_reverse_basic.html`
- Missing checked-in pixel baseline artifacts:
  `test/09_baselines/html_compat/18_flex_grow_weights`,
  `19_flex_shrink_weights`, `20_flex_basis_override`,
  `21_flex_wrap_basic`, `23_flex_wrap_align_content_center`, and
  `24_flex_wrap_reverse_basic` contain real Chromium and Simple
  `chrome.ppm` / `simple.ppm` files plus accepted exact `report.sdn` rows.
  Fixture `22_flex_align_items_baseline` is not committed as a pixel baseline
  row because its text glyph pixels still diverge.
- Pixel catalog coverage:
  `src/app/wm_compare/html_compat_part1.spl` now includes fixture IDs 18-24,
  and `test/03_system/gui/wm_compare/html_compat_spec.spl` asserts
  `catalog.len() == 23`.
- Current focused pixel attempts:
  `xvfb-run ... simple run src/app/wm_compare/html_compat.spl
  --only=18_flex_grow_weights --update-baseline --simple-timeout-ms=1000`
  with `SIMPLE_BINARY` pointing at the current release runtime now reaches
  fixture 18, source A reports `ok pixels=76800`, source B reports
  `ok pixels=76800`, writes both PPMs, and exits 0 with `RESULT: EXACT match`.
  `cmp` reports the two PPMs are byte-identical and both files hash to
  `d8ecff6351645da0337e97a11c705bb1e83e5d11d08a2859b4c146646b7fc62f`.
  The same real capture path also reports exact matches for fixtures 19, 20,
  21, 23, and 24; `cmp` returns 0 for each Chrome/Simple PPM pair.
- Fixture 22 blocked attempt:
  `--only=22_flex_align_items_baseline --update-baseline
  --simple-timeout-ms=1000` writes both PPMs but reports
  `different_pixels=507`, `match_pct_10000=9933`, and
  `max_channel_diff=250`. The diff bounding box is `(15,21)-(49,48)`, matching
  the `A`/`B` text glyph area in the fixture. The failure is not accepted with
  blur, tolerance, downscaling, or copied browser pixels.
- Existing structural pass:
  `doc/09_report/chrome_html_compat_geometry_manifest_evidence_2026-06-11.md`
  records `pass_count=21`, `fail_count=0`, and `blur_or_tolerance_used=false`.
- Focused Electron evidence for fixture 18:
  `doc/09_report/electron_html_compat_geometry_evidence_18_flex_grow_weights_2026-06-11.md`
  records `report_status=layout_match` and `mismatch_count=0`.

## Impact

Structural layout parity for all seven flex rows remains stronger than the
older pixel baseline manifest, and six of seven rows now also have exact pixel
evidence. The remaining pixel blocker is fixture 22's browser font metrics,
glyph rasterization, default text color, and antialiasing gap. Big ways forward:
implement a browser-like font metric/raster/compositing path in Simple, or
route text paint through a real font stack before requiring exact text pixels.
