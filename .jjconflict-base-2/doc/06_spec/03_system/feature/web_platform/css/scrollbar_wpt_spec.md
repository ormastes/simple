# CSS Overflow Scrollbar

> Proves `overflow:auto`, `overflow:scroll`, and `overflow-y:auto` scrollports

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CSS Overflow Scrollbar

Proves `overflow:auto`, `overflow:scroll`, and `overflow-y:auto` scrollports

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/css/scrollbar_wpt_spec.spl` |
| Updated | 2026-07-29 |
| Generator | `simple spipe-docgen` (Simple) |

Proves `overflow:auto`, `overflow:scroll`, and `overflow-y:auto` scrollports
through Web style/layout, owner-ordered rectangle Draw IR, and exact
expected-color Engine2D pixels. Nested overflow clipping, later stacking/glass,
and one fractional-opacity subtree are covered. Interactive local scroll
offsets and scrollbar input remain outside this bounded slice.

## Scenarios

### REQ-WEB-BROWSER-003/004: CSS overflow scrollbar

#### should lower ordinary overflow-y auto track and proportional thumb

- Resolve the ordinary scrollport and overflowing child geometry
   - Artifact capture: after_step
- Lower track and proportional thumb through canonical Draw IR
   - Artifact capture: after_step
   - Evidence: artifact verified by 5 expected checks
   - Expected: composition.batches[0].source.source_kind equals `html_ast`
   - Expected: track.parent_id equals `scrollport`
   - Expected: track.color equals `0xFFD1D5DBu32`
   - Expected: thumb.parent_id equals `scrollport`
   - Expected: thumb.color equals `0xFFDC2626u32`
- Execute the owner-ordered chrome above its content
   - Artifact capture: after_step
- raster shutdown
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: rendered.skipped_command_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 65 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = _scrollbar_html()

step("Resolve the ordinary scrollport and overflowing child geometry")
expect(simple_web_layout_debug_layout_by_id(
    html, 40, 36, "scrollport", "w"
)).to_equal("32")
expect(simple_web_layout_debug_layout_by_id(
    html, 40, 36, "scrollport", "h"
)).to_equal("32")
expect(simple_web_layout_debug_layout_by_id(
    html, 40, 36, "content", "h"
)).to_equal("64")

step("Lower track and proportional thumb through canonical Draw IR")
val composition = simple_web_layout_render_html_draw_ir(
    html, 40, 36
)
val commands = composition.batches[0].commands
val track_index = _scrollbar_command_index(
    commands, "scrollport_scrollbar_track"
)
val thumb_index = _scrollbar_command_index(
    commands, "scrollport_scrollbar_thumb"
)
expect(composition.batches[0].source.source_kind).to_equal("html_ast")
expect(track_index).to_be_greater_than(-1)
expect(thumb_index).to_be_greater_than(-1)
if track_index >= 0:
    val track = commands[track_index]
    expect(track.parent_id).to_equal("scrollport")
    expect([track.x, track.y, track.width, track.height]).to_equal(
        [17, 0, 15, 32]
    )
    expect([
        track.clip_rect.x, track.clip_rect.y,
        track.clip_rect.width, track.clip_rect.height
    ]).to_equal([0, 0, 32, 32])
    expect(_scrollbar_style(
        track, "scrollbar-part"
    )).to_equal("track")
    expect(track.color).to_equal(0xFFD1D5DBu32)
if thumb_index >= 0:
    val thumb = commands[thumb_index]
    expect(thumb.parent_id).to_equal("scrollport")
    expect([thumb.x, thumb.y, thumb.width, thumb.height]).to_equal(
        [17, 0, 15, 16]
    )
    expect(_scrollbar_style(
        thumb, "scrollbar-part"
    )).to_equal("thumb")
    expect(thumb.color).to_equal(0xFFDC2626u32)

step("Execute the owner-ordered chrome above its content")
val raster = Engine2dCompositorBackend.create_named(
    40, 36, "software"
)
val rendered = raster.render_draw_ir_composition(composition, [])
raster.shutdown()
expect(rendered.skipped_command_count).to_equal(0)
expect(_scrollbar_color_count(
    rendered.pixels, 0xFFDC2626u32
)).to_equal(240)
expect(_scrollbar_color_count(
    rendered.pixels, 0xFFD1D5DBu32
)).to_equal(240)
```

</details>

#### should retain overflow scroll chrome when content fits

- Resolve fitting content inside an always-scroll scrollport
   - Artifact capture: after_step
- Execute the full-height fitting thumb
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
val html = (
    "<style>html,body{margin:0}#scrollport{width:32px;height:32px;" +
    "overflow:scroll;scrollbar-color:#dc2626 #d1d5db}" +
    "#content{height:16px;background:#ffffff}</style>" +
    "<div id='scrollport'><div id='content'></div></div>"
)

step("Resolve fitting content inside an always-scroll scrollport")
expect(simple_web_layout_debug_layout_by_id(
    html, 40, 36, "content", "h"
)).to_equal("16")
val composition = simple_web_layout_render_html_draw_ir(
    html, 40, 36
)
val commands = composition.batches[0].commands
val track_index = _scrollbar_command_index(
    commands, "scrollport_scrollbar_track"
)
val thumb_index = _scrollbar_command_index(
    commands, "scrollport_scrollbar_thumb"
)
expect(track_index).to_be_greater_than(-1)
expect(thumb_index).to_be_greater_than(-1)
if thumb_index >= 0:
    val thumb = commands[thumb_index]
    expect([thumb.x, thumb.y, thumb.width, thumb.height]).to_equal(
        [17, 0, 15, 32]
    )

step("Execute the full-height fitting thumb")
val raster = Engine2dCompositorBackend.create_named(
    40, 36, "software"
)
val rendered = raster.render_draw_ir_composition(composition, [])
raster.shutdown()
expect(rendered.skipped_command_count).to_equal(0)
expect(_scrollbar_color_count(
    rendered.pixels, 0xFFDC2626u32
)).to_equal(480)
expect(_scrollbar_color_count(
    rendered.pixels, 0xFFD1D5DBu32
)).to_equal(0)
```

</details>

#### should stop ancestor extent propagation at a nested clipping box

- Resolve tall content behind the nested clipping boundary
   - Artifact capture: after_step
- Execute the same composition without leaked ancestor chrome
   - Artifact capture: after_step
- raster shutdown
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: rendered.skipped_command_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = (
    "<style>html,body{margin:0}#outer{width:32px;height:32px;" +
    "overflow-y:auto;scrollbar-color:#dc2626 #d1d5db}" +
    "#inner{height:32px;overflow:hidden}" +
    "#tall{height:64px;background:#ffffff}</style>" +
    "<div id='outer'><div id='inner'><div id='tall'></div></div></div>"
)

step("Resolve tall content behind the nested clipping boundary")
expect(simple_web_layout_debug_layout_by_id(
    html, 40, 36, "inner", "h"
)).to_equal("32")
expect(simple_web_layout_debug_layout_by_id(
    html, 40, 36, "tall", "h"
)).to_equal("64")
val composition = simple_web_layout_render_html_draw_ir(
    html, 40, 36
)
val commands = composition.batches[0].commands
expect(_scrollbar_command_index(
    commands, "outer_scrollbar_track"
)).to_equal(-1)
expect(_scrollbar_command_index(
    commands, "outer_scrollbar_thumb"
)).to_equal(-1)

step("Execute the same composition without leaked ancestor chrome")
val raster = Engine2dCompositorBackend.create_named(
    40, 36, "software"
)
val rendered = raster.render_draw_ir_composition(composition, [])
raster.shutdown()
expect(rendered.skipped_command_count).to_equal(0)
expect(_scrollbar_color_count(
    rendered.pixels, 0xFFDC2626u32
)).to_equal(0)
expect(_scrollbar_color_count(
    rendered.pixels, 0xFFD1D5DBu32
)).to_equal(0)
```

</details>

#### should keep later stacking and glass fallback above earlier chrome

- "z-index:1;background:#16a34a;backdrop-filter:blur
   - Artifact capture: after_step
- Lower the scrollport before the later stacking/glass fallback
   - Artifact capture: after_step
- Execute the same composition with the later cover on top
   - Artifact capture: after_step
- raster shutdown
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: rendered.skipped_command_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = (
    "<style>html,body{margin:0}#scrollport{width:32px;height:32px;" +
    "overflow:auto;scrollbar-color:#dc2626 #d1d5db}" +
    "#content{height:64px;background:#ffffff}" +
    "#cover{position:absolute;left:17px;top:0;width:15px;height:32px;" +
    "z-index:1;background:#16a34a;backdrop-filter:blur(2px)}</style>" +
    "<div id='scrollport'><div id='content'></div></div>" +
    "<div id='cover'></div>"
)

step("Lower the scrollport before the later stacking/glass fallback")
val composition = simple_web_layout_render_html_draw_ir(
    html, 40, 36
)
val commands = composition.batches[0].commands
val thumb_index = _scrollbar_command_index(
    commands, "scrollport_scrollbar_thumb"
)
val cover_index = _scrollbar_command_index(commands, "cover")
expect(thumb_index).to_be_greater_than(-1)
expect(cover_index).to_be_greater_than(-1)
if thumb_index >= 0 and cover_index >= 0:
    expect(thumb_index).to_be_less_than(cover_index)
    expect(_scrollbar_style(
        commands[cover_index], "backdrop-filter"
    )).to_equal("blur(2px)")

step("Execute the same composition with the later cover on top")
val raster = Engine2dCompositorBackend.create_named(
    40, 36, "software"
)
val rendered = raster.render_draw_ir_composition(composition, [])
raster.shutdown()
expect(rendered.skipped_command_count).to_equal(0)
expect(_scrollbar_color_count(
    rendered.pixels, 0xFF16A34Au32
)).to_equal(480)
expect(_scrollbar_color_count(
    rendered.pixels, 0xFFDC2626u32
)).to_equal(0)
expect(_scrollbar_color_count(
    rendered.pixels, 0xFFD1D5DBu32
)).to_equal(0)
```

</details>

#### should keep scrollbar commands inside one fractional opacity surface

- Keep owner chrome contiguous inside the opacity batch
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: opacity_batches equals `1`
- Execute opacity chrome and the later sibling in one composition
   - Artifact capture: after_step
- raster shutdown
   - Artifact capture: after_step
   - Evidence: artifact verified by 2 expected checks
   - Expected: rendered.skipped_command_count equals `0`
   - Expected: rendered.pixels.len() equals `36 * 32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 47 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = (
    "<style>html,body{margin:0}#scrollport{width:32px;height:32px;" +
    "overflow-y:auto;opacity:.5;scrollbar-color:#ff0000 #0000ff}" +
    "#content{height:64px;background:#ffffff}" +
    "#later{position:absolute;left:32px;top:0;width:4px;height:32px;" +
    "z-index:1;background:#16a34a}</style>" +
    "<div id='scrollport'><div id='content'></div></div>" +
    "<div id='later'></div>"
)

step("Keep owner chrome contiguous inside the opacity batch")
val composition = simple_web_layout_render_html_draw_ir(
    html, 36, 32
)
var opacity_batches = 0
var opacity_has_track = false
var opacity_has_thumb = false
for batch in composition.batches:
    if batch.embedding.opacity_milli == 500:
        opacity_batches = opacity_batches + 1
        for command in batch.commands:
            if command.component_id == "scrollport_scrollbar_track":
                opacity_has_track = true
            elif command.component_id == "scrollport_scrollbar_thumb":
                opacity_has_thumb = true
expect(opacity_batches).to_equal(1)
expect(opacity_has_track).to_be(true)
expect(opacity_has_thumb).to_be(true)

step("Execute opacity chrome and the later sibling in one composition")
val raster = Engine2dCompositorBackend.create_named(
    36, 32, "software"
)
val rendered = raster.render_draw_ir_composition(composition, [])
raster.shutdown()
expect(rendered.skipped_command_count).to_equal(0)
expect(rendered.pixels.len()).to_equal(36 * 32)
if rendered.pixels.len() == 36 * 32:
    expect(rendered.pixels[4 * 36 + 20]).to_equal(
        0xFFFF8080u32
    )
    expect(rendered.pixels[24 * 36 + 20]).to_equal(
        0xFF8080FFu32
    )
    expect(rendered.pixels[4 * 36 + 33]).to_equal(
        0xFF16A34Au32
    )
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
