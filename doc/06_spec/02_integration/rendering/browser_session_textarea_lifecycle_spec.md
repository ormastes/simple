# BrowserSession Textarea Lifecycle

> This scenario proves that BrowserSession orders textarea focus and editing events, defers change until blur, serializes the committed UTF-8 multiline value, and lowers the committed visual state through Draw IR and Engine2D.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# BrowserSession Textarea Lifecycle

This scenario proves that BrowserSession orders textarea focus and editing events, defers change until blur, serializes the committed UTF-8 multiline value, and lowers the committed visual state through Draw IR and Engine2D.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md |
| Plan | doc/03_plan/sys_test/html_css_spec_traceability.md |
| Design | doc/05_design/simple_web_browser_engine_production_hardening.md |
| Research | doc/01_research/local/simple_web_browser_engine_production_hardening.md |
| Source | `test/02_integration/rendering/browser_session_textarea_lifecycle_spec.spl` |
| Updated | 2026-07-30 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This scenario proves that BrowserSession orders textarea focus and editing
events, defers change until blur, serializes the committed UTF-8 multiline
value, and lowers the committed visual state through Draw IR and Engine2D.

## Examples

The displayed flow edits `Ada 한` plus a second line, then requires exact event
order, URL-encoded form data, and the committed component's blue pixel area.

## Reproduction Context

The generated scenario-body excerpt uses these source-module imports:

```simple
use std.spec.*
use std.gc_async_mut.web.browser_session.{BrowserSession}
use std.gc_async_mut.web.browser_session_runtime.*
use std.gc_async_mut.gpu.browser_engine.web_render_backend.{WebRenderBackend}
use os.compositor.compositor_engine2d.{Engine2dCompositorBackend}
```

## Scenarios

### BrowserSession textarea lifecycle

#### should commit UTF-8 multiline input in browser event order and pixels

- Focus the textarea
   - Artifact capture: after_step
   - Evidence: artifact verified by 2 expected checks
   - Expected: focused.default_action equals `focus-element`
   - Expected: session.current_title equals `events:focus>`
- Edit UTF-8 multiline text
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: session.current_title does not contain `change>`
- Blur and commit the value
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: session.blur_dom_text_input("note").is_ok() is true
- Render and serialize the committed state
   - Artifact capture: after_step
   - Evidence: artifact verified by 11 expected checks
   - Expected: submit.default_action equals `button-activate`
   - Expected: request.method equals `POST`
   - Expected: request_found is true
   - Expected: batch.source.source_kind equals `html_ast`
   - Expected: found is true
   - Expected: width equals `32`
   - Expected: height equals `24`
   - Expected: color equals `0xFF2563EBu32`
   - Expected: rendered.skipped_command_count equals `0`
   - Expected: inside_color_count equals `32 * 24`
   - Expected: outside_color_count equals `0`


<details>
<summary>Scenario Body</summary>

Scenario-body excerpt: 117 lines folded for review.
This excerpt runs only within the source module and imports listed above.

```simple
step("Focus the textarea")
var session = BrowserSession.new(
)
expect(session.open_html(
    "https://example.test/textarea",
    "<html><head><title>events:</title><style>" +
    "#commit-state{width:32px;height:24px;background-color:#ef4444}" +
    "#commit-state.committed{background-color:#2563eb}" +
    "</style></head><body><div id='commit-state'></div>" +
    "<form id='profile' action='/save' " +
    "method='post'><textarea id='note' name='note' " +
    "onfocus=\"document.title=document.title+'focus>'\" " +
    "onbeforeinput=\"document.title=document.title+'beforeinput>'\" " +
    "oninput=\"document.title=document.title+'input>'\" " +
    "onchange=\"document.title=document.title+'change>';" +
    "document.getElementById(" +
    "'commit-state').className='committed'\" " +
    "onblur=\"document.title=document.title+'blur>'\" " +
    "onfocusout=\"document.title=document.title+'focusout>'\">" +
    "</textarea><button id='save'>Save</button></form></body></html>"
).is_ok()).to_equal(true)
val focused = session.dispatch_dom_event(
    "note", "focus", false, false
)
expect(focused.default_action).to_equal("focus-element")
expect(session.current_title).to_equal("events:focus>")

step("Edit UTF-8 multiline text")
val edited_value = "Ada 한\nB & C"
expect(session.set_dom_text_input(
    "note", edited_value
).is_ok()).to_equal(true)
expect(session.current_title).to_equal(
    "events:focus>beforeinput>input>"
)
expect(session.current_title.contains("change>")).to_equal(false)

step("Blur and commit the value")
expect(session.blur_dom_text_input("note").is_ok()).to_equal(true)
expect(session.current_title).to_equal(
    "events:focus>beforeinput>input>change>blur>focusout>"
)
expect(session.render_html_document()).to_contain(
    "id=\"commit-state\" class=\"committed\""
)

step("Render and serialize the committed state")
val submit = session.dispatch_dom_event(
    "save", "click", true, true
)
expect(submit.default_action).to_equal("button-activate")
var request_found = false
if val request = session.take_pending_request():
    request_found = true
    expect(request.method).to_equal("POST")
    expect(request.url).to_equal(
        "https://example.test/save"
    )
    expect(request.body).to_equal(
        "note=Ada+%ED%95%9C%0D%0AB+%26+C"
    )
    expect(request.content_type).to_equal(
        "application/x-www-form-urlencoded"
    )
expect(request_found).to_equal(true)

val composition = WebRenderBackend.create(
    "pure_simple", 64, 64
).render_html_to_draw_ir(session.render_html_document())
var found = false
var x = 0
var y = 0
var width = 0
var height = 0
var color = 0u32
for batch in composition.batches:
    expect(batch.source.source_kind).to_equal("html_ast")
    for command in batch.commands:
        if command.component_id == "commit-state":
            found = true
            x = command.x
            y = command.y
            width = command.width
            height = command.height
            color = command.color
expect(found).to_equal(true)
expect(width).to_equal(32)
expect(height).to_equal(24)
expect(color).to_equal(0xFF2563EBu32)

val engine = Engine2dCompositorBackend.create_named(
    64, 64, "software"
)
val rendered = engine.render_draw_ir_composition_resources(
    composition, session.image_resources
)
engine.shutdown(
)
expect(rendered.skipped_command_count).to_equal(0)
var inside_color_count: i64 = 0
var outside_color_count: i64 = 0
var pixel_index = 0
while pixel_index < rendered.pixels.len():
    val pixel_x = pixel_index % 64
    val pixel_y = pixel_index / 64
    val inside = (
        pixel_x >= x and pixel_x < x + width and
        pixel_y >= y and pixel_y < y + height
    )
    if rendered.pixels[pixel_index] == color:
        if inside:
            inside_color_count = inside_color_count + 1
        else:
            outside_color_count = outside_color_count + 1
    pixel_index = pixel_index + 1
expect(inside_color_count).to_equal(32 * 24)
expect(outside_color_count).to_equal(0)
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


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md`
- **Plan:** `doc/03_plan/sys_test/html_css_spec_traceability.md`
- **Design:** `doc/05_design/simple_web_browser_engine_production_hardening.md`
- **Research:** `doc/01_research/local/simple_web_browser_engine_production_hardening.md`


</details>
