# Bug: bitmap-parity gate never exercises the blink render lane

Date: 2026-08-11
Status: FIXED (2026-11-11, lane ne7) — gate now dispatches through render_lane and honors SIMPLE_BROWSER_RENDER_LANE; mechanism verified on 2026-11-11 seed.

## Summary

`scripts/check/check-electron-simple-web-layout-bitmap-evidence.shs` is the
last open exit criterion (6) for flipping `BROWSER_RENDER_LANE_DEFAULT` in
`src/app/browser/render_lane.spl` from `live` to `blink`. As written, the
gate cannot ever measure blink: its generated "expected" fixture
(`$BUILD_DIR/simple_web_layout_expected.spl`) imports
`gc_async_mut.gpu.browser_engine.simple_web_renderer
.simple_web_render_html_to_pixels` directly, not
`render_lane.browser_render_html_to_pixel_array`. It never reads
`SIMPLE_BROWSER_RENDER_LANE` and never references `render_lane.spl` or
`src/lib/blink/**` anywhere (`grep -n "render_lane\|blink"
scripts/check/check-electron-simple-web-layout-bitmap-evidence.shs` — zero
hits).

## Evidence

Ran the gate twice against the same binary
(`release/x86_64-unknown-linux-gnu/simple`), once with
`SIMPLE_BROWSER_RENDER_LANE` unset and once with
`SIMPLE_BROWSER_RENDER_LANE=blink`:

```
diff <(grep -E "status=|reason=|exit_code=" live.log) \
     <(grep -E "status=|reason=|exit_code=" blink.log)
# (empty diff — byte-identical, including the crash)
```

Both runs: `electron_simple_web_layout_status=unavailable`,
`electron_simple_web_layout_reason=simple-layout-render-failed`,
`electron_simple_web_layout_simple_expected_exit_code=139` (SIGSEGV in the
live renderer, before blink code would ever run either way).

## Fix needed

Before criterion 6 can mean anything, the gate's generated fixture must
dispatch through `render_lane.browser_render_html_to_pixel_array` (or
otherwise honour `SIMPLE_BROWSER_RENDER_LANE`) so that setting the env var
actually changes what gets rendered. Separately, this machine had no working
self-hosted `bin/simple` tonight to even run the live-lane baseline
successfully (exit 139) — see
`doc/03_plan/os/simpleos/wm_render_lane_runnable_plan_2026-08-11.md` for the
25 prior failed bootstrap attempts. Both must be resolved before this gate
can close exit criterion 6.

## Triage addendum (2026-11-11, lane ne7)

**Status: FIXED — the gate defect named here is repaired on release/1.0.0 tip
and the repair is runtime-verified on the 2026-11-11 seed.**

Source state (branch work/p3-ne7-20261111), `scripts/check/check-electron-simple-web-layout-bitmap-evidence.shs`:

- The generated fixture now imports
  `app.browser.render_lane.{browser_render_html_to_pixel_array, browser_render_lane_selected}`
  (script line 228) and renders via `browser_render_html_to_pixel_array`
  (line 377) — the exact fix this bug demanded. The old direct
  `simple_web_render_html_to_pixels` import is gone.
- The gate reads `SIMPLE_BROWSER_RENDER_LANE` (line 78:
  `RENDER_LANE="${SIMPLE_BROWSER_RENDER_LANE:-}"`), records
  `electron_simple_web_layout_requested_render_lane` /
  `_selected_render_lane` (lines 136-137), and fails closed:
  any selected lane outside `live|blink|vulkan` or a mismatch with the
  requested lane emits `simple-render-lane-mismatch-failed` (lines 425-430).
  The byte-identical-live-and-blink evidence pattern from this report is
  therefore no longer producible by construction.

Verification actually run (seed-smoke, fresh seed 46fe8f6b6def): a probe
rendering an 8x6 red-page through `browser_render_html_to_pixel_array`
reported `lane=vulkan px0=4294901760 (0xFFFF0000, exact) len=48`; with
`SIMPLE_BROWSER_RENDER_LANE=live` the same probe reported `lane=live` with
identical pixels — the env var now genuinely changes what renders, which the
bug proved was impossible on 2026-08-11.

Out of scope / unchanged: the full gate run (electron + Xvfb + release
binary parity) is Linux-only and was not executed on this Windows lane; the
historical live-lane SIGSEGV baseline and exit criterion 6 for flipping
`BROWSER_RENDER_LANE_DEFAULT` remain separate gates (per the 2026-10-27 v3
freeze: "qualify explicit lanes with a working admitted baseline").
