# CSS Replaced-Image Object Fit

> Proves contain and cover against admitted image resources through Web style and

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CSS Replaced-Image Object Fit

Proves contain and cover against admitted image resources through Web style and

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/css/object_fit_wpt_spec.spl` |
| Updated | 2026-07-29 |
| Generator | `simple spipe-docgen` (Simple) |

Proves contain and cover against admitted image resources through Web style and
layout, canonical image Draw IR geometry and clipping, and exact expected-color
Engine2D coverage/count. Intrinsic sizing without authored dimensions remains
outside this slice.

## Scenarios

### REQ-WEB-BROWSER-003/004: CSS object-fit

#### should contain a wide image and retain the content-box clip

- Resolve contain through Web style and layout semantics
   - Artifact capture: after_step
- Lower the admitted image through canonical clipped Draw IR
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: composition.batches[0].source.source_kind equals `html_ast`
- Execute the clipped image through Engine2D
   - Artifact capture: after_step
- raster shutdown
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: rendered.skipped_command_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 46 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve contain through Web style and layout semantics")
val html = _object_fit_html("contain")
expect(simple_web_layout_debug_layout_by_id(
    html, 8, 8, "photo", "w"
)).to_equal("6")
expect(simple_web_layout_debug_layout_by_id(
    html, 8, 8, "photo", "h"
)).to_equal("6")

step("Lower the admitted image through canonical clipped Draw IR")
val image = _object_fit_resource(0xFFDC2626u32)
val composition = simple_web_layout_render_html_draw_ir_with_images(
    html, 8, 8, [image]
)
val commands = composition.batches[0].commands
val image_index = _object_fit_command_index(
    commands, "photo_image"
)
expect(composition.batches[0].source.source_kind).to_equal("html_ast")
expect(image_index).to_be_greater_than(-1)
if image_index >= 0:
    val command = commands[image_index]
    expect([
        command.x, command.y, command.width, command.height
    ]).to_equal([0, 1, 6, 3])
    expect([
        command.clip_rect.x, command.clip_rect.y,
        command.clip_rect.width, command.clip_rect.height
    ]).to_equal([0, 0, 6, 6])
    expect(_object_fit_style(
        command, "object-fit"
    )).to_equal("contain")
    expect(_object_fit_style(
        command, "object-position"
    )).to_equal("50% 50%")

step("Execute the clipped image through Engine2D")
val raster = Engine2dCompositorBackend.create_named(8, 8, "software")
val rendered = raster.render_draw_ir_composition(
    composition, [image]
)
raster.shutdown()
expect(rendered.skipped_command_count).to_equal(0)
expect(_object_fit_color_count(
    rendered.pixels, 0xFFDC2626u32
)).to_equal(18)
```

</details>

#### should cover the image box and clip both horizontal edges

- Resolve cover through Web style and layout semantics
   - Artifact capture: after_step
- Lower the over-wide image through canonical clipped Draw IR
   - Artifact capture: after_step
- Execute the clipped cover image through Engine2D
   - Artifact capture: after_step
- raster shutdown
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: rendered.skipped_command_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve cover through Web style and layout semantics")
val html = _object_fit_html("cover")
expect(simple_web_layout_debug_layout_by_id(
    html, 8, 8, "photo", "w"
)).to_equal("6")
expect(simple_web_layout_debug_layout_by_id(
    html, 8, 8, "photo", "h"
)).to_equal("6")

step("Lower the over-wide image through canonical clipped Draw IR")
val image = _object_fit_resource(0xFF2563EBu32)
val composition = simple_web_layout_render_html_draw_ir_with_images(
    html, 8, 8, [image]
)
val commands = composition.batches[0].commands
val image_index = _object_fit_command_index(
    commands, "photo_image"
)
expect(image_index).to_be_greater_than(-1)
if image_index >= 0:
    val command = commands[image_index]
    expect([
        command.x, command.y, command.width, command.height
    ]).to_equal([-3, 0, 12, 6])
    expect([
        command.clip_rect.x, command.clip_rect.y,
        command.clip_rect.width, command.clip_rect.height
    ]).to_equal([0, 0, 6, 6])
    expect(_object_fit_style(
        command, "object-fit"
    )).to_equal("cover")

step("Execute the clipped cover image through Engine2D")
val raster = Engine2dCompositorBackend.create_named(8, 8, "software")
val rendered = raster.render_draw_ir_composition(
    composition, [image]
)
raster.shutdown()
expect(rendered.skipped_command_count).to_equal(0)
expect(_object_fit_color_count(
    rendered.pixels, 0xFF2563EBu32
)).to_equal(36)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
