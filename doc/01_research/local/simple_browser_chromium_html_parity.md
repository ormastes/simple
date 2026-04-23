# Simple Browser Chromium HTML Parity - Local Research

Feature: `simple_browser_chromium_html_parity`

The existing renderer stack already has the required comparison pieces:
`src/app/wm_compare/html_compat.spl` owns HTML fixture capture and PPM/report output, `test/baselines/html_compat/<scene>/` stores Chromium/Simple/diff artifacts, and `src/lib/gc_async_mut/gpu/browser_engine/` owns DOM parsing, CSS style-block processing, layout, paint, and render-scene execution.

Findings:

- `html_compat.spl` had a source-B gate that returned `TODO(phase-2-blocked)` by default. That prevented Simple pixels from participating in the parity gate.
- `BrowserRenderer.render_html_to_pixels` used a path that could pull Engine2D backend initialization into pure HTML rendering. The parity gate only needs the deterministic software render-scene path.
- `layout.spl` had a local `layout_text` helper whose name could collide with shared text layout APIs. It now uses `layout_text_node`.
- Browser layout and paint pulled `FontRenderer` into the interpreter path for text measurement/wrapping. The parity path now uses stable monospace metrics and emits render-scene text commands.
- Existing checked-in Chromium PPMs and report locations match the target artifact structure.

Implemented scope builds on `doc/04_architecture/drawing_stack.md` and `doc/04_architecture/cross_platform_wm.md` rather than replacing them.
