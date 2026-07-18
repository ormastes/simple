# Web Render Backend — TL;DR

One `WebRenderBackend` interface, two engines for the **same** HTML:
`pure_simple` (Simple layout → Engine2D raster, winit window) and `chromium`
(live interactive Electron `BrowserWindow`). `render_html_to_pixels()` gives a
comparable buffer from both (used by the bit-exact gate); `show_live_window()`
opens chromium's live DOM window (pure_simple returns false → present pixels).

Run: `scripts/gui/macos-gui-run.shs examples/06_io/ui/web_render_backend_gui.spl <pure_simple|chromium> [WxH] [page.html]`.
`WxH` = CSS viewport (downscaled to window); chromium ignores it (live window).

Invariant: chromium is a peer **shell**, never a draw-lane flag. Compare only via
two independently produced artifacts + an absolute oracle — never memorized pixels.

```sdn
web_render_backend:
  interface: { render_html_to_pixels: "[u32] both engines (compare)",
               show_live_window: "chromium live DOM; pure_simple -> false" }
  engines:
    pure_simple: { layout: simple, raster: engine2d.auto, window: winit, live: false }
    chromium:    { engine: real-chromium(electron), window: BrowserWindow, live: true }
  gate: check-electron-simple-web-engine2d-bitmap-evidence.shs  # mismatch=0
  overflow_axis: exact scene simple-web-layout-overflow-axis-matrix; mixed
                 overflow-x hidden / overflow-y visible paints vertical scrollbar.
  perf: pure_simple interpreted+canvas-bound; keep viewport small; binary must
        carry the in-place array-write fix (2d4579a0) or every pixel write clones.
  8k: retain a doc/09_report or doc/10_metrics row with viewport, backend,
      binary/source revision, readback, p50/p95, RSS/memory, fallback state,
      checksum proof; otherwise record an explicit 8K blocker.
  metal: macOS raw Metal readback only; non-macOS records metal-requires-macos.
```

Full guide: [web_render_backend.md](web_render_backend.md)
