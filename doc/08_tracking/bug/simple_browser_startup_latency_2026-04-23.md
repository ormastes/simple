# Simple Browser Startup Latency

Date: 2026-04-23

## Symptom

Launching the Simple-rendered browser through Electron succeeds, but first paint
is slow. A captured launch with:

```sh
SIMPLE_BROWSER_URL=https://example.com SIMPLE_THEME=light \
SIMPLE_ELECTRON_CAPTURE_PATH=build/ui_snapshots/simple_browser_live.png \
SIMPLE_ELECTRON_CAPTURE_QUIT=1 \
timeout 110 tools/electron-shell/launch.shs examples/ui/simple_browser.spl
```

logged `window ready-to-show` at `06:04:24` and the first parsed
`paint_canvas` at `06:06:04`.

## Impact

The browser now renders correctly once the frame arrives, but interactive launch
feels stalled for roughly 100 seconds on this machine.

## Follow-Up

Profile the `examples/ui/simple_browser.spl` startup path and reduce cold import
or compile latency for the `std.common.web.simple_browser_page` and
`std.gc_async_mut.gpu.browser_engine` graph.

## Verification Update

Date: 2026-04-24

Re-ran the hosted browser smoke with:

```sh
SIMPLE_THEME=light \
SIMPLE_BROWSER_URL=https://example.com \
SIMPLE_ELECTRON_CAPTURE_PATH=build/ui_snapshots/simple_browser_live.png \
SIMPLE_ELECTRON_CAPTURE_QUIT=1 \
tools/electron-shell/launch.shs examples/ui/simple_browser.spl
```

Observed result from `/tmp/simple-ui-captures/electron-shell-debug.log`:

- `spawned simple ... args=run examples/ui/simple_browser.spl` at `2026-04-23T22:55:22.751Z`
- first `ipc message type=paint_canvas` at `2026-04-23T22:55:24.001Z`
- `captured paint canvas to build/ui_snapshots/simple_browser_live.png` at `2026-04-23T22:55:24.795Z`

This puts first paint at about `1.25s` after spawn on this run, so the earlier
`~100s` first-paint regression did not reproduce. The capture artifact was
written to `build/ui_snapshots/simple_browser_live.png` and remained non-blank
(`333045` bytes, `2720x1680`, `905` unique colors).
