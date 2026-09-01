# Canonical Draw IR text route

Executable companion: `test/03_system/check/draw_ir_web_renderer_text_contract_spec.spl`.

Requirement: AC-4.

## Scenario

`step("Render text through canonical Draw IR")` invokes
`expect_canonical_text_route`.

The vector producer must emit one durable Draw IR `TEXT` command with a
`font-identity` and advances. The bitmap-default producer deliberately emits
no vector identity or advances. Neither representation carries transient glyph
atlas or cache pixels.

The executor forwards `TEXT` through `eng.draw_text(...)`. Engine2D then owns
the vector decision and the transient `FontRenderer` / `FontRenderBatch`
material (`draw_text_configured`, `ensure_font_renderer`, and
`stage_text_configured`). The retained 5x7 and Metal atlas routes are backend
compatibility details, not producer implementations.

## Producer boundary

The Web layout painter, shared widget Draw IR producer, UI browser backend, and
hosted browser renderer must not call private glyph rasterizers, glyph-atlas
blits, or carry `FontRenderer`, `FontRenderBatch`, or `atlas_pixels` material.
The executable check fails if any of those producer-owned files introduces the
forbidden paths.

## Evidence

The companion SSpec is the release-blocking source and behavior contract. This
manual mirrors its frozen step/helper names; it does not replace executable
coverage.
