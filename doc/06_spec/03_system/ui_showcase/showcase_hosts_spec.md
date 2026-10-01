# ScreenHost host adapters — 2d / gui / web / wm

> Four `ScreenHost` implementations share one showcase reducer, so the only thing that can differ between targets is the adapter. This spec exercises the parts of those adapters that can actually be wrong WITHOUT a display, a window manager or a listening socket:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ScreenHost host adapters — 2d / gui / web / wm

Four `ScreenHost` implementations share one showcase reducer, so the only thing that can differ between targets is the adapter. This spec exercises the parts of those adapters that can actually be wrong WITHOUT a display, a window manager or a listening socket:

The exact Engine2D adapter additionally admits only `software`, `cpu`,
`cpu_simd`, and `metal`. It rejects fallback, requires native SIMD hit
advancement for `cpu_simd`, and requires device readback plus positive device
identity for Metal.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/os/simpleos/screens/ws_b_screenhost_showcase_detail.md |
| Design | doc/05_design/os/desktop/screen_backend_selection_and_shared_showcase.md |
| Research | N/A |
| Source | `test/03_system/ui_showcase/showcase_hosts_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Four `ScreenHost` implementations share one showcase reducer, so the only
thing that can differ between targets is the adapter. This spec exercises
the parts of those adapters that can actually be wrong WITHOUT a display, a
window manager or a listening socket:

- the 2d host end-to-end through `showcase_run` (script -> ingress queue ->
  reducer -> rasterized frame), which is the one target that is fully
  exercisable in a headless CI;
- every host's ingress translator (`gui_event_to_host`, `web_read_event_at`
  /`wm_read_event_at` via the shared WmFsAppEvent wire form), because that is
  the only real logic a thin adapter carries;
- the web host's scene -> HTML projection;
- the shared DrawIrV3 -> ARGB rasterizer, including that a blank surface is
  reported as blank rather than passed off as a frame.

Deliberately NOT asserted here: that a real window appeared, that a browser
posted an event, or that a WM consumed a frame. Those need a display / server
/ WM and are captured as artifacts elsewhere; claiming them from a headless
spec would be exactly the vacuous evidence this lane is trying to avoid.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** doc/03_plan/os/simpleos/screens/ws_b_screenhost_showcase_detail.md

## Design

**Design:** doc/05_design/os/desktop/screen_backend_selection_and_shared_showcase.md

## Research

**Research:** N/A

## Examples

A scripted click and two keystrokes on the 2d host produce a report with
clicks=1 and typed="ab" and a frame whose command count is nonzero; a
GuiRenderer mouse-button event becomes a `Pointer` with HOST_BTN_LEFT.

## Scenarios

### Exact Engine2D showcase backend admission

#### admits only software CPU SIMD and Metal showcase backends

- The allowlist accepts `software`, `cpu`, `cpu_simd`, and `metal`.
- `vulkan` remains owned by the strict Vulkan host; `auto` is rejected because
  it cannot attest an exact requested backend.

#### keeps Metal and CPU SIMD receipts fail closed

- The production host checks exact `engine.backend_name()` selection.
- Metal requires `device_readback`, backend handle, and device identity.
- CPU SIMD requires the native SIMD hit counter to advance.
- The launcher reports blocked/fail rather than relabeling fallback as PASS.

### 2d host — script ingress

#### expands a scripted click into a down/up pair and a type into one key each

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- expands a scripted click into a down/up pair and a type into one key each
- Parse a two-step script
   - Expected: q.len() equals `4`
   - Expected: ev_tag(q[0]) equals `pointer`
   - Expected: ev_pressed(q[0]) is true
   - Expected: ev_button(q[0]) equals `HOST_BTN_LEFT`
   - Expected: ev_pressed(q[1]) is false
   - Expected: ev_tag(q[2]) equals `key`
   - Expected: ev_tag(q[3]) equals `key`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("expands a scripted click into a down/up pair and a type into one key each")
step("Parse a two-step script")
val q = screen_2d_parse_script("click 20,10;type ab")

expect(q.len()).to_equal(4)
expect(ev_tag(q[0])).to_equal("pointer")
expect(ev_pressed(q[0])).to_equal(true)
expect(ev_button(q[0])).to_equal(HOST_BTN_LEFT)
expect(ev_pressed(q[1])).to_equal(false)
expect(ev_tag(q[2])).to_equal("key")
expect(ev_tag(q[3])).to_equal("key")
```

</details>

#### parses wheel and resize steps and drops an unknown verb

- parses wheel and resize steps and drops an unknown verb
- Parse a script mixing known and unknown verbs
   - Expected: q.len() equals `2`
   - Expected: ev_wheel(q[0]) equals `3`
   - Expected: ev_tag(q[1]) equals `resize`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses wheel and resize steps and drops an unknown verb")
step("Parse a script mixing known and unknown verbs")
val q = screen_2d_parse_script("wheel 5,6,3;frobnicate 1,2;resize 320,240")

expect(q.len()).to_equal(2)
expect(ev_wheel(q[0])).to_equal(3)
expect(ev_tag(q[1])).to_equal("resize")
```

</details>

#### drains its queue exactly once and then reports nil

- drains its queue exactly once and then reports nil
- Open a 2d host over a one-click script and drain it
   - Expected: drained equals `2`
   - Expected: host.cursor equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("drains its queue exactly once and then reports nil")
step("Open a 2d host over a one-click script and drain it")
val host = Screen2dHost.open(64, 48, "click 5,5")
var drained = 0
var ev = host.poll_input()
while ev != nil:
    drained = drained + 1
    ev = host.poll_input()

expect(drained).to_equal(2)
expect(host.cursor).to_equal(2)
```

</details>

### 2d host — end to end through showcase_run

#### reports the scripted click and typed characters and paints a real frame

- reports the scripted click and typed characters and paints a real frame
- Run the shared loop on the 2d host with a scripted click + keys
   - Expected: report.host_name equals `2d`
   - Expected: report.frames equals `2`
   - Expected: report.clicks equals `1`
   - Expected: report.typed_text equals `ab`
   - Expected: host.last_painted_commands > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports the scripted click and typed characters and paints a real frame")
step("Run the shared loop on the 2d host with a scripted click + keys")
val host = Screen2dHost.open(160, 120, "click 20,10;type ab")
val report = showcase_run(host, "spec2d_e2e", 2)

expect(report.host_name).to_equal("2d")
expect(report.frames).to_equal(2)
expect(report.clicks).to_equal(1)
expect(report.typed_text).to_equal("ab")
# A frame that painted nothing would have ended the loop at frames=0,
# so a nonzero painted-command count is what makes frames=2 real.
expect(host.last_painted_commands > 0).to_equal(true)
```

</details>

#### produces a nonblank capture with more than one distinct pixel value

- produces a nonblank capture with more than one distinct pixel value
- Rasterize the showcase into a 2d host surface and inspect pixels
   - Expected: px.len() equals `96 * 72`
   - Expected: raster_distinct_pixel_count(px, 4) >= 2 is true
   - Expected: raster_to_ppm_bytes(px, 96, 72).len() > 96 * 72 * 3 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("produces a nonblank capture with more than one distinct pixel value")
step("Rasterize the showcase into a 2d host surface and inspect pixels")
val host = Screen2dHost.open(96, 72, "")
showcase_run(host, "spec2d_cap", 1)
val px = host.pixels()

expect(px.len()).to_equal(96 * 72)
expect(raster_distinct_pixel_count(px, 4) >= 2).to_equal(true)
# P6 header plus 3 bytes per pixel.
expect(raster_to_ppm_bytes(px, 96, 72).len() > 96 * 72 * 3).to_equal(true)
```

</details>

### scene rasterizer

#### reports zero painted commands for an empty scene and leaves it blank

- reports zero painted commands for an empty scene and leaves it blank
- Paint an empty scene onto a fresh surface
   - Expected: painted equals `0`
   - Expected: raster_distinct_pixel_count(surface.pixels, 4) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports zero painted commands for an empty scene and leaves it blank")
step("Paint an empty scene onto a fresh surface")
val surface = RasterSurface.new(8, 8, RASTER_BG)
val painted = raster_scene_into(surface, draw_ir_v3_empty_scene(1u32, 1u32))

expect(painted).to_equal(0)
expect(raster_distinct_pixel_count(surface.pixels, 4)).to_equal(1)
```

</details>

#### paints a nonzero command count for a real showcase scene

- paints a nonzero command count for a real showcase scene
- Build the showcase scene and paint it
   - Expected: painted > 0 is true
   - Expected: raster_distinct_pixel_count(surface.pixels, 4) >= 2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("paints a nonzero command count for a real showcase scene")
step("Build the showcase scene and paint it")
val st = showcase_build("spec_raster")
val surface = RasterSurface.new(120, 90, RASTER_BG)
val painted = raster_scene_into(surface, showcase_scene(st, 120, 90))

expect(painted > 0).to_equal(true)
expect(raster_distinct_pixel_count(surface.pixels, 4) >= 2).to_equal(true)
```

</details>

### gui host — event translation

#### maps GuiRenderer button codes onto HOST_BTN_* and refuses to guess

- maps GuiRenderer button codes onto HOST_BTN_* and refuses to guess
- Translate each known button code plus an unknown one
   - Expected: gui_button_to_host(0) equals `HOST_BTN_LEFT`
   - Expected: gui_button_to_host(1) equals `HOST_BTN_RIGHT`
   - Expected: gui_button_to_host(99) equals `HOST_BTN_NONE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps GuiRenderer button codes onto HOST_BTN_* and refuses to guess")
step("Translate each known button code plus an unknown one")

expect(gui_button_to_host(0)).to_equal(HOST_BTN_LEFT)
expect(gui_button_to_host(1)).to_equal(HOST_BTN_RIGHT)
expect(gui_button_to_host(99)).to_equal(HOST_BTN_NONE)
```

</details>

#### turns a mouse press into a pressed Pointer at truncated coordinates

- turns a mouse press into a pressed Pointer at truncated coordinates
- Translate a left press at (12.9, 7.1)
   - Expected: ev != nil is true
   - Expected: ev_tag(ev!) equals `pointer`
   - Expected: ev_x(ev!) equals `12`
   - Expected: ev_button(ev!) equals `HOST_BTN_LEFT`
   - Expected: ev_pressed(ev!) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("turns a mouse press into a pressed Pointer at truncated coordinates")
step("Translate a left press at (12.9, 7.1)")
val ev = gui_event_to_host(gui_ev(GUI_EVT_MOUSE_BUTTON, 0, 0, true, 12.9, 7.1))

expect(ev != nil).to_equal(true)
expect(ev_tag(ev!)).to_equal("pointer")
expect(ev_x(ev!)).to_equal(12)
expect(ev_button(ev!)).to_equal(HOST_BTN_LEFT)
expect(ev_pressed(ev!)).to_equal(true)
```

</details>

#### preserves a GUI drag sequence as move and release events

- preserves a GUI drag sequence as move and release events
- Translate press, move, and release without losing coordinates
   - Expected: ev_button(down!) equals `HOST_BTN_LEFT`
   - Expected: ev_pressed(down!) is true
   - Expected: ev_x(move!) equals `31`
   - Expected: ev_y(move!) equals `19`
   - Expected: ev_button(move!) equals `HOST_BTN_NONE`
   - Expected: ev_pressed(up!) is false
   - Expected: ev_x(up!) equals `31`
   - Expected: ev_y(up!) equals `19`
   - Expected: ev_button(up!) equals `HOST_BTN_LEFT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserves a GUI drag sequence as move and release events")
step("Translate press, move, and release without losing coordinates")
val down = gui_event_to_host(gui_ev(
    GUI_EVT_MOUSE_BUTTON, 0, 0, true, 12.9, 7.1
))
val move = gui_event_to_host(gui_ev(
    GUI_EVT_MOUSE_MOVED, 0, 0, false, 31.8, 19.2
))
val up = gui_event_to_host(gui_ev(
    GUI_EVT_MOUSE_BUTTON, 0, 0, false, 31.8, 19.2
))

expect(ev_button(down!)).to_equal(HOST_BTN_LEFT)
expect(ev_pressed(down!)).to_equal(true)
expect(ev_x(move!)).to_equal(31)
expect(ev_y(move!)).to_equal(19)
expect(ev_button(move!)).to_equal(HOST_BTN_NONE)
expect(ev_pressed(up!)).to_equal(false)
expect(ev_x(up!)).to_equal(31)
expect(ev_y(up!)).to_equal(19)
expect(ev_button(up!)).to_equal(HOST_BTN_LEFT)
```

</details>

#### carries the keycode on a key press and the wheel delta on a wheel

- carries the keycode on a key press and the wheel delta on a wheel
- Translate a keyboard press and a wheel notch
   - Expected: ev_tag(key!) equals `key`
   - Expected: ev_code(key!) equals `65`
   - Expected: ev_wheel(wheel!) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("carries the keycode on a key press and the wheel delta on a wheel")
step("Translate a keyboard press and a wheel notch")
val key = gui_event_to_host(gui_ev(GUI_EVT_KEYBOARD, 65, 0, true, 0.0, 0.0))
val wheel = gui_event_to_host(gui_ev(GUI_EVT_MOUSE_WHEEL, 0, 0, false, 0.0, 3.0))

expect(ev_tag(key!)).to_equal("key")
expect(ev_code(key!)).to_equal(65)
expect(ev_wheel(wheel!)).to_equal(3)
```

</details>

#### treats idle and close as non-events rather than fabricating input

- treats idle and close as non-events rather than fabricating input
- Translate GUI_EVT_NONE and GUI_EVT_CLOSE
   - Expected: idle == nil is true
   - Expected: close == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("treats idle and close as non-events rather than fabricating input")
step("Translate GUI_EVT_NONE and GUI_EVT_CLOSE")
val idle = gui_event_to_host(gui_ev(GUI_EVT_NONE, 0, 0, false, 0.0, 0.0))
val close = gui_event_to_host(gui_ev(GUI_EVT_CLOSE, 0, 0, false, 0.0, 0.0))

expect(idle == nil).to_equal(true)
expect(close == nil).to_equal(true)
```

</details>

#### maps a resize to a Resize event

- maps a resize to a Resize event
- Translate GUI_EVT_RESIZED carrying the new extent in x/y
   - Expected: ev_tag(ev!) equals `resize`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps a resize to a Resize event")
step("Translate GUI_EVT_RESIZED carrying the new extent in x/y")
val ev = gui_event_to_host(gui_ev(GUI_EVT_RESIZED, 0, 0, false, 320.0, 240.0))

expect(ev_tag(ev!)).to_equal("resize")
```

</details>

### web host — scene projection

#### emits one positioned div per rect command with the paint colour

- emits one positioned div per rect command with the paint colour
- Project a real showcase scene to HTML
   - Expected: html contains `showcase-root`
   - Expected: html contains `position:absolute`
   - Expected: html contains `rgba(`
   - Expected: html contains `width:200px`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("emits one positioned div per rect command with the paint colour")
step("Project a real showcase scene to HTML")
val st = showcase_build("spec_web_html")
val html = web_scene_to_html(showcase_scene(st, 200, 150), 200, 150)

expect(html.contains("showcase-root")).to_equal(true)
expect(html.contains("position:absolute")).to_equal(true)
expect(html.contains("rgba(")).to_equal(true)
expect(html.contains("width:200px")).to_equal(true)
```

</details>

#### renders colour channels exactly and keeps a fully opaque alpha as 1

- renders colour channels exactly and keeps a fully opaque alpha as 1
- Convert 0xFF204060 (opaque) and 0x80204060 (half alpha) to CSS
   - Expected: web_color_css(4280303712u32) equals `rgba(32,64,96,1)`
   - Expected: web_color_css(2149597280u32) equals `rgba(32,64,96,0.501)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders colour channels exactly and keeps a fully opaque alpha as 1")
step("Convert 0xFF204060 (opaque) and 0x80204060 (half alpha) to CSS")

expect(web_color_css(4280303712u32)).to_equal("rgba(32,64,96,1)")
expect(web_color_css(2149597280u32)).to_equal("rgba(32,64,96,0.501)")
```

</details>

#### projects shared DrawIR text glyphs with pixel metrics and no unsupported receipt

- projects shared DrawIR text glyphs with pixel metrics and no unsupported receipt
- Project the showcase's canonical 5x7 text runs
   - Expected: html contains `data-glyph=`
   - Expected: html contains `background:rgba(`
   - Expected: web_scene_unsupported_count(showcase_scene(st, 200, 150)) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("projects shared DrawIR text glyphs with pixel metrics and no unsupported receipt")
step("Project the showcase's canonical 5x7 text runs")
val st = showcase_build("spec_web_text")
val html = web_scene_to_html(showcase_scene(st, 200, 150), 200, 150)

expect(html.contains("data-glyph=")).to_equal(true)
expect(html.contains("background:rgba(")).to_equal(true)
expect(web_scene_unsupported_count(showcase_scene(st, 200, 150))).to_equal(0)
```

</details>

#### projects a valid line path through the web host boundary

- projects a valid line path through the web host boundary
- Build a canonical v3 path and emit SVG
   - Expected: web_scene_unsupported_count(scene) equals `0`
   - Expected: web_scene_to_html(scene, 40, 30) contains `<svg`
   - Expected: host.present_scene(scene) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("projects a valid line path through the web host boundary")
step("Build a canonical v3 path and emit SVG")
var scene = draw_ir_v3_empty_scene(10u32, 1u32)
scene.paint = draw_ir_v3_paint_append(scene.paint, 4280303712u32, 4294967295u32, 1000, 1000, 0u16)
scene.path_points = draw_ir_v3_path_point_append(scene.path_points, 5, 5, DRAW_IR_V3_VERB_MOVE)
scene.path_points = draw_ir_v3_path_point_append(scene.path_points, 35, 5, DRAW_IR_V3_VERB_LINE)
scene.path_points = draw_ir_v3_path_point_append(scene.path_points, 35, 25, DRAW_IR_V3_VERB_LINE)
scene.path_points = draw_ir_v3_path_span_append(scene.path_points, 0u32, 3u32, 0u16)
val path_id = 0u32
scene.commands.push(draw_ir_v3_command(
    DRAW_IR_V3_KIND_PATH, DRAW_IR_V3_FLAG_NONE,
    0u32, 0u32, DRAW_IR_V3_NO_ID,
    DRAW_IR_V3_NO_ID, 0u32, DRAW_IR_V3_NO_ID,
    DRAW_IR_V3_NO_ID, path_id, DRAW_IR_V3_NO_ID,
    DRAW_IR_V3_NO_ID, DRAW_IR_V3_NO_ID
))

expect(web_scene_unsupported_count(scene)).to_equal(0)
expect(web_scene_to_html(scene, 40, 30).contains("<svg")).to_equal(true)
val host = ScreenWebHost.open(
    40, 30, "/tmp/showcase_spec_web_path.html", ""
)!
expect(host.present_scene(scene)).to_equal(true)
```

</details>

#### fails closed for a visible DrawIR command outside the web projection

- fails closed for a visible DrawIR command outside the web projection
- Expose the partial-document receipt and reject presentation
   - Expected: web_scene_unsupported_count(scene) equals `1`
   - Expected: host.present_scene(scene) is false
   - Expected: host.last_unsupported_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fails closed for a visible DrawIR command outside the web projection")
step("Expose the partial-document receipt and reject presentation")
var scene = draw_ir_v3_empty_scene(9u32, 1u32)
scene.commands.push(draw_ir_v3_command(
    DRAW_IR_V3_KIND_PATH, DRAW_IR_V3_FLAG_NONE,
    0u32, 0u32, DRAW_IR_V3_NO_ID,
    DRAW_IR_V3_NO_ID, DRAW_IR_V3_NO_ID, DRAW_IR_V3_NO_ID,
    DRAW_IR_V3_NO_ID, DRAW_IR_V3_NO_ID, DRAW_IR_V3_NO_ID,
    DRAW_IR_V3_NO_ID, DRAW_IR_V3_NO_ID
))
expect(web_scene_unsupported_count(scene)).to_equal(1)
expect(web_scene_to_html(scene, 40, 30).contains(
    "drawir-unsupported-count=1")).to_equal(true)
val host = ScreenWebHost.open(
    40, 30, "/tmp/showcase_spec_web_unsupported.html", "")!
expect(host.present_scene(scene)).to_equal(false)
expect(host.last_unsupported_count).to_equal(1)
```

</details>

#### reads a posted event off the shared WmFsAppEvent wire form

- reads a posted event off the shared WmFsAppEvent wire form
- Post an encoded click into a temp event dir and read it back
   - Expected: ev != nil is true
   - Expected: ev_tag(ev!) equals `pointer`
   - Expected: ev_x(ev!) equals `11`
   - Expected: web_read_event_at(dir, 2) == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reads a posted event off the shared WmFsAppEvent wire form")
step("Post an encoded click into a temp event dir and read it back")
val dir = "/tmp/showcase_spec_web_events"
mkdir_p(dir)
write_file(
    wm_fs_app_event_seq_path(dir + "/event", 1),
    wm_fs_app_event_encode(wm_fs_app_event(1, "mouse_down", 11, 22, HOST_BTN_LEFT, true))
)
val ev = web_read_event_at(dir, 1)

expect(ev != nil).to_equal(true)
expect(ev_tag(ev!)).to_equal("pointer")
expect(ev_x(ev!)).to_equal(11)
expect(web_read_event_at(dir, 2) == nil).to_equal(true)
```

</details>

#### refuses to open without a document path

- refuses to open without a document path
- Open the web host with an empty doc path
   - Expected: ScreenWebHost.open(100, 100, "", "") == nil is true
   - Expected: ScreenWebHost.open(100, 100, "/tmp/showcase_spec_web.html", "") != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("refuses to open without a document path")
step("Open the web host with an empty doc path")

expect(ScreenWebHost.open(100, 100, "", "") == nil).to_equal(true)
expect(ScreenWebHost.open(100, 100, "/tmp/showcase_spec_web.html", "") != nil).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/os/simpleos/screens/ws_b_screenhost_showcase_detail.md`
- **Design:** `doc/05_design/os/desktop/screen_backend_selection_and_shared_showcase.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `99ffaa503eb2bbd06f53c5c344a134e2b6973eb0164899e43ebc7a56c40ca3a4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `99ffaa503eb2bbd06f53c5c344a134e2b6973eb0164899e43ebc7a56c40ca3a4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `99ffaa503eb2bbd06f53c5c344a134e2b6973eb0164899e43ebc7a56c40ca3a4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/ui_showcase/showcase_hosts_spec.spl
mirror: doc/06_spec/03_system/ui_showcase/showcase_hosts_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/ui_showcase/showcase_hosts_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/ui_showcase/showcase_hosts_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/ui_showcase/showcase_hosts_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 21 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/ui_showcase/showcase_hosts_spec.spl:135:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'expands a scripted click into a down/up pair and a type into one key each' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/ui_showcase/showcase_hosts_spec.spl:149:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses wheel and resize steps and drops an unknown verb' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/ui_showcase/showcase_hosts_spec.spl:159:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'drains its queue exactly once and then reports nil' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
