# Web Renderer Vulkan 4K Showcase Hardening — Local Research

- The catalog routes `web_standards_showcase` to `examples/06_io/ui/web_standards_showcase_gui.spl`, but readiness is deliberately false and the installed `/sys/apps` launch is not accepted.
- The entry imports `run_web_standards_showcase`, `showcase_resolution_dims`, and `showcase_dpi`; the current `web_render_file_gui.spl` defines none of them and contains undefined receipt variables while hard-coding an 80×60 CPU-SIMD render.
- The current page is a hand-authored common-elements sample with no accessible tab model and no inventory linkage.
- `check-html-css-rendering-manifest-traceability.shs` passes rows by textual `<tag` / `property:` occurrence. It does not prove style, layout, Draw IR, device execution, or pixel change.
- Its embedded implemented-CSS set has 284 rows while existing executable/manual assertions still require 131. Several claimed rows have no production browser-engine reference.
- Existing Vulkan readback evidence is 24×20 or lavapipe presentation; existing Chrome runners explicitly use synthetic timing/hash data. No source-bound 3840×2160 first-frame/RSS/tab comparison receipt exists.
- Reusable owners are the production HTML layout renderer modules, Draw IR/Engine2D backend session and readback contracts, showcase catalog, HTML/CSS traceability checkers, Chrome component renderer harness, and retained-host serialization behavior.

See `.spipe/web_renderer_vulkan_4k_showcase_hardening/state.md` for acceptance mapping and exact evidence boundaries.

