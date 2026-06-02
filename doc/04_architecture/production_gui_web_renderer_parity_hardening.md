# Production GUI Web Renderer Parity Hardening Architecture

## Slice Architecture

This slice adds a production parity harness in `app.wm_compare`:

- `common.ui.builder` builds marker-free widget trees.
- `app.ui.render.widgets.render_html_tree` converts the tree into real widget
  HTML.
- `simple_web_engine2d_render_html_pixels` detects generated widget HTML and
  routes it to `simple_web_layout_render_html_pixels`.
- `simple_web_html_layout_renderer` parses, lays out, and paints text, image,
  and button elements into a framebuffer.
- `app.wm_compare.html_compat.compare_exact` compares software, CPU SIMD, and
  Metal-backed framebuffers.

## Production Boundary

Generated widget HTML is identified by stable renderer output markers such as
`widget-*`, `layout-*`, `panel-content`, and `data-action`. These are not sample
fixtures; they are the real GUI HTML contract. Legacy sample markers remain
available only for existing fixture/corpus gates.

## Open Architecture Work

`scripts/check-electron-generated-gui-web-parity-evidence.shs` now provides the
first live Electron generated-GUI capture lane. It writes generated GUI HTML and
Simple CPU SIMD expected ARGB, asks Electron to render the HTML directly, then
captures Electron ARGB and records exact mismatch evidence. Later slices must
promote this into a canonical manifest covering more fixtures, then extend
parity reports with CPU SIMD counter proof and Metal GPU-readback provenance.
