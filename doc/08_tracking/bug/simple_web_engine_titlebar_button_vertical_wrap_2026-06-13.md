# Bug: pure-Simple browser engine wraps titlebar widget button label vertically

Status: Open

**Date:** 2026-06-13
**Area:** `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl` (software HTML layout)
**Severity:** Medium (visual fidelity; pure-Simple/SimpleOS render path only — Electron/Tauri backends are correct)

## Summary

When the shared titlebar fragment from `src/lib/common/ui/html_window.spl`
(`.simple-titlebar-widget` button) is rendered through the pure-Simple software
browser engine (`simple_web_layout_render_html_software_pixels`), the button is
laid out far narrower than its content and the label wraps one character per line
("Run" → R / u / n). The button box also overflows the 35px titlebar band.

Both production web backends render the identical markup correctly:

| Engine | Button box | Label |
|--------|-----------|-------|
| Chromium (real Electron) | 43 × 24 | "Run" horizontal |
| WebKit (real WKWebView, = Tauri/macOS) | 43 × 24 | "Run" horizontal |
| **pure-Simple software engine** | **33 × 60** | **"Run" wrapped vertically** |

Root cause is in the software engine, not the CSS: the button's intrinsic
shrink-to-fit width is under-computed and `white-space:nowrap` is not honored for
the inline form-control, so the layout collapses the button to ~1 glyph wide and
grows it tall to fit the wrapped text.

## Reproduction

```sh
# Emit the shared titlebar fragment as a standalone HTML document
bin/simple run src/app/ui_shared_mdi/titlebar_fixture_emit.spl > /tmp/tb.html
# Render through the pure-Simple software engine
bin/simple run src/app/wm_compare/simple_html_capture_worker.spl \
    --html=/tmp/tb.html --out=/tmp/tb.ppm --width=600 --height=120
# Inspect /tmp/tb.ppm: the .simple-titlebar-widget button (bg rgb(18,58,52),
# border rgb(52,211,153)) measures ~33w x ~60h with the label stacked vertically.
```

Cross-engine reference capture (browsers render 43x24):
`scripts/check/check-titlebar-cross-engine-parity.shs`.

## Notes

This is independent of the 2026-06-13 titlebar CSS hardening (the pre-hardening
markup wraps identically). The CSS pins only measured Chromium/WebKit divergences
and deliberately does not add a workaround `width`/`min-width` to mask this engine
bug. Fix belongs in the software layout engine's intrinsic-width / nowrap handling
for replaced/form-control inline boxes.
