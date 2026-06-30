# HTML/CSS Full Rendering Goal Status - Logical Inset Slice

Date: 2026-06-27

## Scope

This slice moves the default horizontal writing-mode logical inset properties
into implemented Simple Web CSS:

- `inset`
- `inset-block`
- `inset-block-start`
- `inset-block-end`
- `inset-inline`
- `inset-inline-start`
- `inset-inline-end`

The renderer maps these properties onto the existing physical
`top`/`right`/`bottom`/`left` positioning fields and preserves declaration-order
precedence against the physical forms. This does not claim vertical
`writing-mode` remapping.

## Evidence

- Focused renderer SSpec:
  `release/x86_64-unknown-linux-gnu/simple test test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer_spec.spl --mode=interpreter`
  - PASS, 73 scenarios.
- CSS inventory SSpec:
  `release/x86_64-unknown-linux-gnu/simple test test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_css_inventory_traceability_spec.spl --mode=interpreter`
  - PASS, 2 scenarios.
- Manifest traceability:
  `BUILD_DIR=build/html-css-manifest-logical-inset REPORT_PATH=build/html-css-manifest-logical-inset/report.md sh scripts/check/check-html-css-rendering-manifest-traceability.shs`
  - PASS, implemented CSS covered `160/160`.
- Full CSS goal status:
  `BUILD_DIR=build/html-css-full-rendering-logical-inset REPORT_PATH=build/html-css-full-rendering-logical-inset/report.md HTML_CSS_RENDERING_MANIFEST_FETCH=0 sh scripts/check/check-html-css-full-rendering-goal-status.shs`
  - Expected incomplete, implemented CSS `160/160`, full CSS `160/394`,
    unrendered CSS `234`, unsupported inventory `241`.
- Full rendering goal SSpec:
  `release/x86_64-unknown-linux-gnu/simple test test/03_system/check/html_css_full_rendering_goal_status_spec.spl --mode=interpreter`
  - PASS, 2 scenarios.
- Renderer source check:
  `release/x86_64-unknown-linux-gnu/simple check src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`
  - PASS.

## Completion Boundary

This is a narrow web-renderer hardening slice. The overall GUI/Web/2D goal
remains incomplete until full CSS, Linux Vulkan RenderDoc, macOS Metal,
Windows D3D12, production GUI/Web parity, and retained 4K/8K performance gates
all have fresh passing evidence.
