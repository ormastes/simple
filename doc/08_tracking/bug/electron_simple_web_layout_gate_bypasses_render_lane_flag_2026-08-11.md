# Bug: bitmap-parity gate never exercises the blink render lane

Date: 2026-08-11
Status: OPEN

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
