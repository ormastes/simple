# `test/01_unit/lib/gc_async_mut/gpu/browser_engine/`

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-WEBRENDER-002"></a>FR-WEBRENDER-002 | Pixel-level test coverage for the generic layout path | The new generic-HTML branch (`simple_web_layout_render_html_pixels`) is only exercised indirectly. Add a focused spec that feeds generic document HTML (heading + paragraph + a colored block, none of the heuristic markers) and asserts: the p | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
