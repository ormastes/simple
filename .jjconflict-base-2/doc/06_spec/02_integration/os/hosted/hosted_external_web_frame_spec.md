# Hosted External Web Frame Specification

> Tests covering hosted external browser frames.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hosted External Web Frame Specification

## Scenarios

### hosted external browser frames

#### keeps positive-owner content out of the in-process renderer

- "<script>document body setAttribute
- 1, 0, COMP CREATE WINDOW to i64
- local pure simple pixel buffer
- local raster shutdown
- 1, 77, COMP CREATE WINDOW to i64
- remote pure simple pixel buffer
- remote raster shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hostile = (
    "<style>body{background-color:#ef4444}</style>" +
    "<script>document.body.setAttribute('data-ran','yes')</script>"
)
var local = HostCompositor.new_headless(Size(
    width: 160u64, height: 120u64
))
local.apply_bridge_request(
    1, 0, COMP_CREATE_WINDOW.to_i64(), 0, "Local",
    8, 8, 100, 80, hostile, 1, "hosted-web-event"
)
expect(local.requires_external_web_frame(1)).to_be(false)
val local_raster = Engine2dCompositorBackend.create_named(
    160, 120, "software"
)
expect(local.render_frame_engine2d(local_raster)).to_be(true)
expect(count_color(
    local.pure_simple_pixel_buffer(), 0xFFEF4444u32
)).to_be_greater_than(0)
local_raster.shutdown()

var remote = HostCompositor.new_headless(Size(
    width: 160u64, height: 120u64
))
remote.apply_bridge_request(
    1, 77, COMP_CREATE_WINDOW.to_i64(), 0, "Remote",
    8, 8, 100, 80, hostile, 77, "hosted-web-event"
)
expect(remote.requires_external_web_frame(1)).to_be(true)
val remote_raster = Engine2dCompositorBackend.create_named(
    160, 120, "software"
)
expect(remote.render_frame_engine2d(remote_raster)).to_be(false)
expect(count_color(
    remote.pure_simple_pixel_buffer(), 0xFFEF4444u32
)).to_equal(0)
remote_raster.shutdown()
```

</details>

#### keeps trusted frames isolated by window through close

- Open two browser compositor windows
- 1, 1, COMP CREATE WINDOW to i64
- 2, 2, COMP CREATE WINDOW to i64
- Attach distinct trusted external frames
- Close one window without releasing the other frame
- comp destroy window
   - Expected: comp.external_web_window_ids.len() equals `1`
   - Expected: comp.external_web_frames.len() equals `1`
   - Expected: comp.external_web_window_ids[0] equals `2`
   - Expected: comp.external_web_frames[0].window_id equals `2`
- comp pure simple pixel buffer
- comp pure simple pixel buffer
- raster shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 52 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Open two browser compositor windows")
val first_body = "<div>first parent body</div>"
val second_body = "<div>second parent body</div>"
var comp = HostCompositor.new_headless(Size(
    width: 260u64, height: 220u64
))
comp.apply_bridge_request(
    1, 1, COMP_CREATE_WINDOW.to_i64(), 0, "First",
    8, 8, 112, 160, first_body, 1, "browser"
)
comp.apply_bridge_request(
    2, 2, COMP_CREATE_WINDOW.to_i64(), 0, "Second",
    140, 8, 112, 160, second_body, 2, "browser"
)
expect(comp.require_external_web_frame(1)).to_be(true)
expect(comp.require_external_web_frame(2)).to_be(true)

step("Attach distinct trusted external frames")
val theme = default_theme_id()
val first_revision = simple_web_content_revision_with_theme(
    theme, "First", first_body, 104, 80, 0
)
val second_revision = simple_web_content_revision_with_theme(
    theme, "Second", second_body, 104, 80, 0
)
val first = trusted_frame("1", first_revision, 0xFF123456u32)
val second = trusted_frame("2", second_revision, 0xFFABCDEFu32)
expect(comp.set_external_web_frame(1, first)).to_be(true)
expect(comp.set_external_web_frame(2, second)).to_be(true)
val raster = Engine2dCompositorBackend.create_named(
    260, 220, "software"
)
expect(comp.render_frame_engine2d(raster)).to_be(true)
val both_pixels = comp.pure_simple_pixel_buffer()
expect(count_color(both_pixels, 0xFF123456u32)).to_be_greater_than(5000)
expect(count_color(both_pixels, 0xFFABCDEFu32)).to_be_greater_than(5000)

step("Close one window without releasing the other frame")
comp.destroy_window(1)
expect(comp.external_web_window_ids.len()).to_equal(1)
expect(comp.external_web_frames.len()).to_equal(1)
expect(comp.external_web_window_ids[0]).to_equal(2)
expect(comp.external_web_frames[0].window_id).to_equal("2")
expect(comp.set_external_web_frame(1, first)).to_be(false)
expect(comp.render_frame_engine2d(raster)).to_be(true)
expect(count_color(
    comp.pure_simple_pixel_buffer(), 0xFF123456u32
)).to_equal(0)
expect(count_color(
    comp.pure_simple_pixel_buffer(), 0xFFABCDEFu32
)).to_be_greater_than(5000)
raster.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/os/hosted/hosted_external_web_frame_spec.spl` |
| Updated | 2026-07-29 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering hosted external browser frames.
- hosted external browser frames

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
