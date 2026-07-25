# LLM Caret GUI Backends — Local Research

The existing Caret browser surface is owned by `src/app/llm_caret/main.spl` and
`gui.spl`; provider dispatch already has a deterministic `dummy` backend.

The canonical Electron host is `src/app/ui.electron/bridge.js`. It accepts
`--url`, creates a real `BrowserWindow`, and loads the supplied Simple-owned
HTTP surface. Electron remains a host transport; Caret owns application state
and provider requests.

The canonical pure-Simple Web/2D path is:

`HTML -> simple_web_layout_render_html_draw_ir -> DrawIrComposition ->
simple_web_render_html_to_readback_with_engine2d_backend(..., "metal") ->
Engine2D Metal -> winit presentation`.

Existing examples `web_engine2d_metal_gui.spl` and
`widget_interact_metal_gui.spl` prove the renderer, strict GPU readback, and
winit input patterns. Caret has no adapter for either Electron or this Metal
surface today.

The active WM/theme worktree changes are a separate agent lane and must not be
included in this feature's commit.
