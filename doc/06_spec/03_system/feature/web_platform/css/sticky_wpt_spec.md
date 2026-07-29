# CSS Sticky Positioning Gap

> Records the current truthful static-position fallback at two document scroll

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CSS Sticky Positioning Gap

Records the current truthful static-position fallback at two document scroll

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/css/sticky_wpt_spec.spl` |
| Updated | 2026-07-29 |
| Generator | `simple spipe-docgen` (Simple) |

Records the current truthful static-position fallback at two document scroll
offsets through Web layout, canonical Draw IR, and exact expected-color
Engine2D coverage/count. Sticky pinning and containing-block constraints remain
RED because `position: sticky` has no admitted style/layout representation.

## Scenarios

### REQ-WEB-BROWSER-003/004: CSS sticky positioning gap

#### should expose static fallback at two offsets while sticky pinning remains RED

- Resolve the sticky declaration through the current static layout
   - Artifact capture: after_step
- Lower the unscrolled and document-scrolled fallback to Draw IR
   - Artifact capture: after_step
- html, 16, 12, 0, 0, browser text input overlay empty
   - Artifact capture: after_step
- html, 16, 12, 0, 6, browser text input overlay empty
   - Artifact capture: after_step
   - Evidence: artifact verified by 2 expected checks
   - Expected: zero.resolved_scroll_y equals `0`
   - Expected: scrolled.resolved_scroll_y equals `6`
- Execute both truthful fallback frames through Engine2D
   - Artifact capture: after_step
- raster shutdown
   - Artifact capture: after_step
   - Evidence: artifact verified by 2 expected checks
   - Expected: zero_frame.skipped_command_count equals `0`
   - Expected: scrolled_frame.skipped_command_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 74 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = _sticky_html()

step("Resolve the sticky declaration through the current static layout")
expect(simple_web_layout_debug_layout_by_id(
    html, 16, 12, "sticky", "y"
)).to_equal("4")
expect(simple_web_layout_debug_layout_by_id(
    html, 16, 12, "sticky", "w"
)).to_equal("4")
expect(simple_web_layout_debug_layout_by_id(
    html, 16, 12, "sticky", "h"
)).to_equal("4")

step("Lower the unscrolled and document-scrolled fallback to Draw IR")
val zero =
    simple_web_layout_render_html_draw_ir_result_with_overlay_at_scroll_time(
        html, 16, 12, 0, 0, browser_text_input_overlay_empty()
    )
val scrolled =
    simple_web_layout_render_html_draw_ir_result_with_overlay_at_scroll_time(
        html, 16, 12, 0, 6, browser_text_input_overlay_empty()
    )
expect(zero.resolved_scroll_y).to_equal(0)
expect(scrolled.resolved_scroll_y).to_equal(6)
expect(zero.composition.batches[0].source.source_kind).to_equal(
    "html_ast"
)
val zero_index = _sticky_command_index(
    zero.composition.batches[0].commands, "sticky"
)
val scrolled_index = _sticky_command_index(
    scrolled.composition.batches[0].commands, "sticky"
)
expect(zero_index).to_be_greater_than(-1)
expect(scrolled_index).to_be_greater_than(-1)
if zero_index >= 0:
    val zero_command =
        zero.composition.batches[0].commands[zero_index]
    expect([
        zero_command.x, zero_command.y,
        zero_command.width, zero_command.height
    ]).to_equal([0, 4, 4, 4])
if scrolled_index >= 0:
    val scrolled_command =
        scrolled.composition.batches[0].commands[scrolled_index]
    expect([
        scrolled_command.x, scrolled_command.y,
        scrolled_command.width, scrolled_command.height
    ]).to_equal([0, -2, 4, 4])
    expect([
        scrolled_command.clip_rect.x, scrolled_command.clip_rect.y,
        scrolled_command.clip_rect.width,
        scrolled_command.clip_rect.height
    ]).to_equal([0, 0, 16, 12])

step("Execute both truthful fallback frames through Engine2D")
val raster = Engine2dCompositorBackend.create_named(
    16, 12, "software"
)
val zero_frame = raster.render_draw_ir_composition(
    zero.composition, []
)
val scrolled_frame = raster.render_draw_ir_composition(
    scrolled.composition, []
)
raster.shutdown()
expect(zero_frame.skipped_command_count).to_equal(0)
expect(scrolled_frame.skipped_command_count).to_equal(0)
expect(_sticky_color_count(
    zero_frame.pixels, 0xFF2563EBu32
)).to_equal(16)
expect(_sticky_color_count(
    scrolled_frame.pixels, 0xFF2563EBu32
)).to_equal(8)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
