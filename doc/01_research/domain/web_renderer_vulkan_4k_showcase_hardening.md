# Web Renderer Vulkan 4K Showcase Hardening — Domain Research

- “First complete frame” must include process launch, document parsing, style, layout, paint, GPU/backend initialization, submission, and presentation; measuring only a render function is not startup evidence.
- A fair Chrome comparison needs the same immutable fixture, viewport/device scale, cold/warm classification, capture points, backend admission, and RSS definition. Browser startup and renderer-only timings must remain separately labeled.
- Vulkan proof requires physical-adapter/driver identity and device-derived submission/readback or presentation evidence. API selection, lavapipe, a Vulkan-capable browser binary, or a screenshot alone is insufficient.
- HTML elements include metadata/non-rendered semantics as well as painted elements. Inventory rows therefore need explicit `renderable`, `partial`, `nonpaint`, or `unsupported` status instead of treating lexical presence as pixels.
- CSS support is property-and-value-family specific. A property name appearing in a fixture does not prove parsing, computed value, layout/paint effect, animation lifecycle, or compositing support.
- Accessible tabs require tablist/tab/tabpanel semantics, one selected tab, managed focus, Arrow/Home/End keyboard navigation, Enter/Space activation where selection is manual, and pointer parity.
- Representative performance must preserve deterministic visual evidence and fail closed on missing tab captures, fallback, stale cache, or mismatched viewport.

Existing domain baselines: `doc/01_research/domain/unified_surface_draw_ir_and_html_css_conformance.md` and `doc/01_research/domain/chromium_web_renderer_primitive_differential.md`.

