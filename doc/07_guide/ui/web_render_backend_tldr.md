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
    pure_simple: { layout: simple, raster: engine2d.cpu_simd, window: winit, live: false }
    chromium:    { engine: real-chromium(electron), window: BrowserWindow, live: true }
  gate: check-electron-simple-web-engine2d-bitmap-evidence.shs  # mismatch=0
  perf: pure_simple interpreted+canvas-bound; keep viewport small; binary must
        carry the in-place array-write fix (2d4579a0) or every pixel write clones.
```

Full guide: [web_render_backend.md](web_render_backend.md)
