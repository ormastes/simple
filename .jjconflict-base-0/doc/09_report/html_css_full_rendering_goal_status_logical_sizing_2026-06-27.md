# HTML/CSS Full Rendering Goal Status - Logical Sizing Slice

Date: 2026-06-27

## Scope

This slice moves the default horizontal writing-mode logical sizing properties
into implemented Simple Web CSS:

- `inline-size`
- `block-size`
- `min-inline-size`
- `max-inline-size`
- `min-block-size`
- `max-block-size`

The renderer maps these properties onto the existing physical
`width`/`height` and min/max size fields, preserving declaration-order
precedence against the physical forms. This does not claim vertical
`writing-mode` remapping.

## Evidence

- Focused renderer SSpec:
  `release/x86_64-unknown-linux-gnu/simple test test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer_spec.spl --mode=interpreter`
  - PASS, 72 scenarios.
- CSS inventory SSpec:
  `release/x86_64-unknown-linux-gnu/simple test test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_css_inventory_traceability_spec.spl --mode=interpreter`
  - PASS, 2 scenarios.
- Manifest traceability:
  `BUILD_DIR=build/html-css-manifest-logical-sizing REPORT_PATH=build/html-css-manifest-logical-sizing/report.md sh scripts/check/check-html-css-rendering-manifest-traceability.shs`
  - PASS, implemented CSS covered `153/153`.
- Full CSS goal status:
  `BUILD_DIR=build/html-css-full-rendering-logical-sizing REPORT_PATH=build/html-css-full-rendering-logical-sizing/report.md HTML_CSS_RENDERING_MANIFEST_FETCH=0 sh scripts/check/check-html-css-full-rendering-goal-status.shs`
  - Expected incomplete, implemented CSS `153/153`, full CSS `153/394`,
    unrendered CSS `241`, unsupported inventory `248`.
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
