# Fractional CSS Subtree Opacity

> Proves one fractional-opacity subtree is rendered into one canonical Draw IR

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fractional CSS Subtree Opacity

Proves one fractional-opacity subtree is rendered into one canonical Draw IR

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/css/fractional_subtree_opacity_spec.spl` |
| Updated | 2026-07-29 |
| Generator | `simple spipe-docgen` (Simple) |

Proves one fractional-opacity subtree is rendered into one canonical Draw IR
surface and composited once through Engine2D.

## Scenarios

### WPT-derived fractional subtree opacity

#### should composite overlapping descendants once as one Draw IR surface

- Lower one fractional subtree through canonical Draw IR
   - Artifact capture: after_step
   - Evidence: artifact verified by 7 expected checks
   - Expected: opacity_batches equals `1`
   - Expected: group_surface == "" is false
   - Expected: group_component equals `group`
   - Expected: group_width equals `16`
   - Expected: group_height equals `8`
   - Expected: group_has_red is true
   - Expected: group_has_blue is true
- Read absolute pixels from the canonical Engine2D execution
   - Artifact capture: after_step
   - Evidence: artifact verified by 6 expected checks
   - Expected: pixels.len() equals `16 * 8`
   - Expected: pixels[2] equals `0xFFFF8080u32`
   - Expected: pixels[6] equals `0xFF8080FFu32`
   - Expected: pixels[10] equals `0xFF8080FFu32`
   - Expected: pixels[14] equals `0xFFFFFFFFu32`
   - Expected: pixels[6] == 0xFF8040C0u32 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Lower one fractional subtree through canonical Draw IR")
val composition = simple_web_layout_render_html_draw_ir(
    FRACTIONAL_SUBTREE_HTML, 16, 8
)
var opacity_batches = 0
var group_has_red = false
var group_has_blue = false
var group_surface = ""
var group_component = ""
var group_width = 0
var group_height = 0
for batch in composition.batches:
    if batch.embedding.opacity_milli == 500:
        opacity_batches = opacity_batches + 1
        group_surface = batch.embedding.surface_id
        group_component = batch.embedding.component_id
        group_width = batch.embedding.width
        group_height = batch.embedding.height
        for command in batch.commands:
            if command.component_id == "red":
                group_has_red = true
            elif command.component_id == "blue":
                group_has_blue = true
expect(opacity_batches).to_equal(1)
expect(group_surface == "").to_equal(false)
expect(group_component).to_equal("group")
expect(group_width).to_equal(16)
expect(group_height).to_equal(8)
expect(group_has_red).to_equal(true)
expect(group_has_blue).to_equal(true)

step("Read absolute pixels from the canonical Engine2D execution")
val result = simple_web_layout_render_html_readback_engine2d_result(
    FRACTIONAL_SUBTREE_HTML, 16, 8, "software"
)
val pixels = result.readback.pixels
expect(pixels.len()).to_equal(16 * 8)
expect(pixels[2]).to_equal(0xFFFF8080u32)
expect(pixels[6]).to_equal(0xFF8080FFu32)
expect(pixels[10]).to_equal(0xFF8080FFu32)
expect(pixels[14]).to_equal(0xFFFFFFFFu32)
expect(pixels[6] == 0xFF8040C0u32).to_equal(false)
```

</details>

#### should keep descendants deeper than 64 levels in the opacity surface

- Lower every deep descendant into the same opacity batch
   - Artifact capture: after_step
- command component id starts with
   - Artifact capture: after_step
   - Evidence: artifact verified by 3 expected checks
   - Expected: opacity_batches equals `1`
   - Expected: descendant_commands equals `72`
   - Expected: deep_red_in_group is true
- Composite the deepest opaque pixel exactly once over white
   - Artifact capture: after_step
   - Evidence: artifact verified by 2 expected checks
   - Expected: result.readback.pixels.len() equals `16 * 8`
   - Expected: result.readback.pixels[2] equals `0xFFFF8080u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = _deep_fractional_subtree_html()

step("Lower every deep descendant into the same opacity batch")
val composition = simple_web_layout_render_html_draw_ir(html, 16, 8)
var opacity_batches = 0
var descendant_commands = 0
var deep_red_in_group = false
for batch in composition.batches:
    if batch.embedding.opacity_milli == 500:
        opacity_batches = opacity_batches + 1
        for command in batch.commands:
            if (
                command.component_id == "deep-group" or
                command.component_id.starts_with("layer-") or
                command.component_id == "deep-red"
            ):
                descendant_commands = descendant_commands + 1
            if command.component_id == "deep-red":
                deep_red_in_group = true
expect(opacity_batches).to_equal(1)
expect(descendant_commands).to_equal(72)
expect(deep_red_in_group).to_equal(true)

step("Composite the deepest opaque pixel exactly once over white")
val result = simple_web_layout_render_html_readback_engine2d_result(
    html, 16, 8, "software"
)
expect(result.readback.pixels.len()).to_equal(16 * 8)
expect(result.readback.pixels[2]).to_equal(0xFFFF8080u32)
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
