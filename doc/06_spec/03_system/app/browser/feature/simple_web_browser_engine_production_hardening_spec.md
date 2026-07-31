# Production Simple Browser User Flow

> Proves the installed browser uses canonical HTML, CSS, JavaScript, DOM-event, Draw IR, and Engine2D paths, then drives page controls and browser chrome through structured UI access. Helpers fail closed until production evidence exists.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Production Simple Browser User Flow

Proves the installed browser uses canonical HTML, CSS, JavaScript, DOM-event, Draw IR, and Engine2D paths, then drives page controls and browser chrome through structured UI access. Helpers fail closed until production evidence exists.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md |
| Plan | doc/03_plan/sys_test/simple_web_browser_engine_production_hardening.md |
| Design | doc/05_design/simple_web_browser_engine_production_hardening.md |
| Research | doc/01_research/local/simple_web_browser_engine_production_hardening.md |
| Source | `test/03_system/app/browser/feature/simple_web_browser_engine_production_hardening_spec.spl` |
| Updated | 2026-07-31 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Proves the installed browser uses canonical HTML, CSS, JavaScript, DOM-event,
Draw IR, and Engine2D paths, then drives page controls and browser chrome
through structured UI access. Helpers fail closed until production evidence
exists.

## Examples

The bookmark-title scenario admits a bounded renderer witness, commits it
through the parent profile owner, restarts both renderer and profile-backed
window, and lists the restored title or derived URL fallback.

## Scenarios

### Production Simple browser user flow

#### should anchor fixed CSS image backgrounds to the viewport

- Render HTML and CSS through canonical Draw IR
   - Artifact capture: after_step
- "background-color:#00ff00;background-image:url
   - Artifact capture: after_step
   - Evidence: artifact verified by 6 expected checks
   - Expected: fixed.x equals `3`
   - Expected: fixed.y equals `0`
   - Expected: fixed.width equals `4`
   - Expected: fixed.height equals `2`
   - Expected: fixed.clip_rect.x equals `3`
   - Expected: fixed.clip_rect.width equals `4`
- Scroll the document under the viewport-fixed tile
   - Artifact capture: after_step
- browser text input overlay empty
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: scrolled_fixed.resolved_scroll_y equals `1`
- browser text input overlay empty
   - Artifact capture: after_step
- Read back fixed repeat and no-repeat edge pixels
   - Artifact capture: after_step
   - Evidence: artifact verified by 3 expected checks
   - Expected: fixed_pixels[first_box_pixel] equals `0xFF0000FFu32`
   - Expected: scroll_pixels[first_box_pixel] equals `0xFFFF0000u32`
   - Expected: no_repeat_pixels[first_box_pixel] equals `0xFF00FF00u32`
- Keep local attachment outside the supported profile
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 106 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render HTML and CSS through canonical Draw IR")
val repeat_html = (
    "<html style='margin:0'><body style='margin:0'>" +
    "<div id='fixed' style='margin-left:3px;width:4px;height:2px;" +
    "background-color:#00ff00;background-image:url(image://stripe);" +
    "background-attachment:fixed;background-repeat:repeat;" +
    "background-position:left top'></div>" +
    "<div style='height:8px'></div></body></html>"
)
val scroll_html = repeat_html.replace(
    "background-attachment:fixed", "background-attachment:scroll"
)
val no_repeat_html = repeat_html.replace(
    "background-repeat:repeat", "background-repeat:no-repeat"
)
val local_html = repeat_html.replace(
    "background-attachment:fixed", "background-attachment:local"
)
val stripe = simpleos_host_gpu_image_resource(
    "image://stripe", 2, 1, [0xFFFF0000u32, 0xFF0000FFu32]
)
val images = [stripe]
val fixed_composition =
    simple_web_layout_render_html_draw_ir_with_images(
        repeat_html, 8, 4, images
    )
val fixed_commands = fixed_composition.batches[0].commands
val fixed_index = _browser_draw_ir_command_index(
    fixed_commands, "fixed_background_image"
)
expect(fixed_index).to_be_greater_than(-1)
val fixed = fixed_commands[fixed_index]
expect(fixed.x).to_equal(3)
expect(fixed.y).to_equal(0)
expect(fixed.width).to_equal(4)
expect(fixed.height).to_equal(2)
expect(fixed.clip_rect.x).to_equal(3)
expect(fixed.clip_rect.width).to_equal(4)
expect(_browser_draw_ir_style_value(
    fixed, "background-tile-x"
)).to_equal("0")
expect(_browser_draw_ir_style_value(
    fixed, "background-tile-y"
)).to_equal("0")

step("Scroll the document under the viewport-fixed tile")
val scrolled_fixed =
    simple_web_layout_render_html_draw_ir_result_with_overlay_at_scroll_time_with_images(
        repeat_html, 8, 4, 0, 1,
        browser_text_input_overlay_empty(), images
    )
expect(scrolled_fixed.resolved_scroll_y).to_equal(1)
val scrolled_fixed_commands =
    scrolled_fixed.composition.batches[0].commands
val scrolled_fixed_index = _browser_draw_ir_command_index(
    scrolled_fixed_commands, "fixed_background_image"
)
expect(scrolled_fixed_index).to_be_greater_than(-1)
val scrolled_fixed_command =
    scrolled_fixed_commands[scrolled_fixed_index]
expect(_browser_draw_ir_style_value(
    scrolled_fixed_command, "background-tile-y"
)).to_equal("0")
expect(_browser_draw_ir_style_value(
    scrolled_fixed_command, "background-shape-y"
)).to_equal("-1")
val scrolled_element =
    simple_web_layout_render_html_draw_ir_result_with_overlay_at_scroll_time_with_images(
        scroll_html, 8, 4, 0, 1,
        browser_text_input_overlay_empty(), images
    )
val scrolled_element_commands =
    scrolled_element.composition.batches[0].commands
val scrolled_element_index = _browser_draw_ir_command_index(
    scrolled_element_commands, "fixed_background_image"
)
expect(scrolled_element_index).to_be_greater_than(-1)
expect(_browser_draw_ir_style_value(
    scrolled_element_commands[scrolled_element_index],
    "background-tile-y"
)).to_equal("-1")

step("Read back fixed repeat and no-repeat edge pixels")
val renderer = BrowserRenderer.create(8, 4)
val fixed_pixels = renderer.render_html_to_pixels_with_images(
    repeat_html, images
).pixel_data
val scroll_pixels = renderer.render_html_to_pixels_with_images(
    scroll_html, images
).pixel_data
val no_repeat_pixels = renderer.render_html_to_pixels_with_images(
    no_repeat_html, images
).pixel_data
val first_box_pixel = fixed.y * 8 + fixed.x
expect(fixed_pixels[first_box_pixel]).to_equal(0xFF0000FFu32)
expect(scroll_pixels[first_box_pixel]).to_equal(0xFFFF0000u32)
expect(no_repeat_pixels[first_box_pixel]).to_equal(0xFF00FF00u32)

step("Keep local attachment outside the supported profile")
val local_commands =
    simple_web_layout_render_html_draw_ir_with_images(
        local_html, 8, 4, images
    ).batches[0].commands
expect(_browser_draw_ir_command_index(
    local_commands, "fixed_background_image"
)).to_equal(-1)
```

</details>

#### should admit two CSS URL backgrounds and lower both through canonical Draw IR

- Admit the bounded two URL CSS background profile
   - Artifact capture: after_step
- var session = BrowserSession new
   - Artifact capture: after_step
- "https://assets test/front png",  retained png hex
   - Artifact capture: after_step
- "https://assets test/back png",  retained png hex
   - Artifact capture: after_step
- "background-image:url
   - Artifact capture: after_step
- Ok
   - Artifact capture: after_step
-
   - Artifact capture: after_step
- Err
   - Artifact capture: after_step
- fail
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: session.image_resources.len() equals `2`
- Render HTML and CSS through canonical Draw IR
   - Artifact capture: after_step
- session render html document
   - Artifact capture: after_step
- Deny the whole pair when CSP denies image admission
   - Artifact capture: after_step
- var denied = BrowserSession new
   - Artifact capture: after_step
- "https://assets test/front png",  retained png hex
   - Artifact capture: after_step
- "https://assets test/back png",  retained png hex
   - Artifact capture: after_step
- "background-image:url
   - Artifact capture: after_step
- Ok
   - Artifact capture: after_step
-
   - Artifact capture: after_step
- Err
   - Artifact capture: after_step
- fail
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: denied.image_resources.len() equals `0`
- denied render html document
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 63 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Admit the bounded two URL CSS background profile")
var session = BrowserSession.new()
session.register_resource(
    "https://assets.test/front.png", _retained_png_hex(0xFFFF0000u32)
)
session.register_resource(
    "https://assets.test/back.png", _retained_png_hex(0xFF0000FFu32)
)
match session.open_html(
    "https://example.test/layers",
    "<style>#layers{width:4px;height:2px;background-color:#00ff00;" +
    "background-image:url(https://assets.test/front.png),url(https://assets.test/back.png);" +
    "background-repeat:no-repeat}</style><div id='layers'></div>"
):
    Ok(_):
        ()
    Err(reason):
        fail("two URL background fixture failed to open: {reason}")
expect(session.image_resources.len()).to_equal(2)

step("Render HTML and CSS through canonical Draw IR")
val composition = simple_web_layout_render_html_draw_ir_with_images(
    session.render_html_document(), 8, 4, session.image_resources
)
val commands = composition.batches[0].commands
expect(_browser_draw_ir_command_index(
    commands, "layers_background_image_1"
)).to_be_greater_than(-1)
expect(_browser_draw_ir_command_index(
    commands, "layers_background_image_0"
)).to_be_greater_than(_browser_draw_ir_command_index(
    commands, "layers_background_image_1"
))

step("Deny the whole pair when CSP denies image admission")
var denied = BrowserSession.new()
denied.register_resource(
    "https://assets.test/front.png", _retained_png_hex(0xFFFF0000u32)
)
denied.register_resource(
    "https://assets.test/back.png", _retained_png_hex(0xFF0000FFu32)
)
match denied.open_html(
    "https://example.test/layers-denied",
    "<meta http-equiv='Content-Security-Policy' content=\"img-src 'none'\">" +
    "<style>#layers{width:4px;height:2px;background-color:#00ff00;" +
    "background-image:url(https://assets.test/front.png),url(https://assets.test/back.png)}</style>" +
    "<div id='layers'></div>"
):
    Ok(_):
        ()
    Err(reason):
        fail("CSP two URL background fixture failed to open: {reason}")
expect(denied.image_resources.len()).to_equal(0)
val denied_commands = simple_web_layout_render_html_draw_ir_with_images(
    denied.render_html_document(), 8, 4, denied.image_resources
).batches[0].commands
expect(_browser_draw_ir_command_index(
    denied_commands, "layers_background_image_1"
)).to_equal(-1)
expect(_browser_draw_ir_command_index(
    denied_commands, "layers_background_image_0"
)).to_equal(-1)
```

</details>

#### should preserve semantic parentage clipping and stacking in canonical Draw IR

- Lower web semantic parentage and CSS stacking to canonical Draw IR
   - Protocol capture: after_step
- fail
   - Protocol capture: after_step
- Inspect stable IDs parent links clip geometry and paint order
   - Protocol capture: after_step
   - Evidence: protocol response verified by 8 expected checks
   - Expected: commands[clip_index].parent_id equals `page`
   - Expected: commands[bottom_index].parent_id equals `clip`
   - Expected: commands[middle_index].parent_id equals `clip`
   - Expected: commands[top_index].parent_id equals `clip`
   - Expected: commands[top_index].clip_rect.x equals `0`
   - Expected: commands[top_index].clip_rect.y equals `0`
   - Expected: commands[top_index].clip_rect.width equals `16`
   - Expected: commands[top_index].clip_rect.height equals `12`
- Round-trip semantic parent links through the hosted SBRF gate
   - Protocol capture: after_step
   - Evidence: protocol response verified by 1 expected check
   - Expected: wire.ok is true
- fail
   - Protocol capture: after_step
- browser renderer decoder new
   - Protocol capture: after_step
   - Evidence: protocol response verified by 2 expected checks
   - Expected: message.status equals `message`
   - Expected: hosted.ok is true
- fail
   - Protocol capture: after_step
- fail
   - Protocol capture: after_step
   - Evidence: protocol response verified by 1 expected check
   - Expected: hosted_commands[hosted_top_index].parent_id equals `clip`
- Replay the same canonical composition through Engine2D
   - Protocol capture: after_step
- raster shutdown
   - Protocol capture: after_step
   - Evidence: protocol response verified by 2 expected checks
   - Expected: rendered.skipped_command_count equals `0`
   - Expected: rendered.pixels.len() equals `32 * 24`


<details>
<summary>Executable SSpec</summary>

Runnable source: 78 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Lower web semantic parentage and CSS stacking to canonical Draw IR")
val html = (
    "<html style='margin:0'><body id='page' style='margin:0'>" +
    "<section id='clip' style='position:relative;overflow:hidden;" +
    "width:16px;height:12px'>" +
    "<div id='top' style='position:absolute;left:0;top:0;z-index:3;" +
    "width:24px;height:12px;background:#f59e0b'></div>" +
    "<div id='bottom' style='position:absolute;left:0;top:0;z-index:1;" +
    "width:24px;height:12px;background:#1d4ed8'></div>" +
    "<div id='middle' style='position:absolute;left:0;top:0;z-index:2;" +
    "width:24px;height:12px;background:#22c55e'></div>" +
    "</section></body></html>"
)
val composition = simple_web_layout_render_html_draw_ir_with_images(
    html, 32, 24, []
)
expect(composition.batches.len()).to_be_greater_than(0)
val commands = composition.batches[0].commands
val page_index = _browser_draw_ir_command_index(commands, "page")
val clip_index = _browser_draw_ir_command_index(commands, "clip")
val bottom_index = _browser_draw_ir_command_index(commands, "bottom")
val middle_index = _browser_draw_ir_command_index(commands, "middle")
val top_index = _browser_draw_ir_command_index(commands, "top")
if (page_index < 0 or clip_index < 0 or bottom_index < 0 or
    middle_index < 0 or top_index < 0):
    fail("REQ-WEB-BROWSER-004: semantic Draw IR command missing")

step("Inspect stable IDs parent links clip geometry and paint order")
expect(commands[clip_index].parent_id).to_equal("page")
expect(commands[bottom_index].parent_id).to_equal("clip")
expect(commands[middle_index].parent_id).to_equal("clip")
expect(commands[top_index].parent_id).to_equal("clip")
expect(commands[top_index].clip_rect.x).to_equal(0)
expect(commands[top_index].clip_rect.y).to_equal(0)
expect(commands[top_index].clip_rect.width).to_equal(16)
expect(commands[top_index].clip_rect.height).to_equal(12)
expect(_browser_draw_ir_style_value(
    commands[top_index], "z-index"
)).to_equal("3")
expect(bottom_index).to_be_less_than(middle_index)
expect(middle_index).to_be_less_than(top_index)

step("Round-trip semantic parent links through the hosted SBRF gate")
val wire = browser_renderer_frame_encode(composition, 7, 1)
expect(wire.ok).to_equal(true)
if not wire.ok:
    fail("REQ-WEB-BROWSER-004: hosted Draw IR encode rejected")
val message = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(7), wire.wire
)
expect(message.status).to_equal("message")
val hosted = browser_renderer_frame_decode(message.message, 32, 24)
expect(hosted.ok).to_equal(true)
if not hosted.ok:
    fail("REQ-WEB-BROWSER-004: hosted Draw IR decode rejected")
val hosted_commands = hosted.composition.batches[0].commands
val hosted_top_index = _browser_draw_ir_command_index(
    hosted_commands, "top"
)
if hosted_top_index < 0:
    fail("REQ-WEB-BROWSER-004: hosted semantic command missing")
expect(hosted_commands[hosted_top_index].parent_id).to_equal("clip")

step("Replay the same canonical composition through Engine2D")
val raster = Engine2dCompositorBackend.create_named(32, 24, "software")
val rendered = raster.render_draw_ir_composition(composition, [])
raster.shutdown()
expect(rendered.skipped_command_count).to_equal(0)
expect(rendered.pixels.len()).to_equal(32 * 24)
expect(_count_color(
    rendered.pixels, 0xFFF59E0Bu32
)).to_equal(16 * 12)
expect(_count_color(
    rendered.pixels, 0xFF1D4ED8u32
)).to_equal(0)
expect(_count_color(
    rendered.pixels, 0xFF22C55Eu32
)).to_equal(0)
```

</details>

#### should normalize split overflow axes before Draw IR clipping

- Resolve `overflow-x: hidden|auto|scroll` with omitted or explicit visible
  `overflow-y` after the final author/inline cascade.
- Preserve explicit `overflow-y:hidden`; suppress `scrollbar-width:none` at
  author, inline, author-important, and inline-important priority without
  disabling scrollport clipping.
- Resolve the two-value `overflow` shorthand into its final x/y winners.
- Verify the resulting scrollport clip and Engine2D pixel boundary.

<details>
<summary>Executable SSpec</summary>

Runnable source: `simple_web_browser_engine_production_hardening_spec.spl`.
The scenario uses author-class `overflow-x` plus inline `overflow-y` to prove
final-cascade normalization, then checks the single- and two-axis scrollbar
tracks, four priority-specific withheld owner tracks, a nested child track
under a hidden-scrollbar parent, their Draw IR clips, and Engine2D pixels.

</details>

#### should deliver retained callable listeners through one DOM event path

- Deliver JavaScript and Simple Script listeners on the live DOM
   - Text capture: after_step
- var session = BrowserSession new
   - Text capture: after_step
- Ok
   - Text capture: after_step
-
   - Text capture: after_step
- Err
   - Text capture: after_step
- fail
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: session.current_title equals `simple,`
- Dispatch capture target and bubble listeners through window and document
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: ordered.actions.len() equals `9`
- Cancel defaults and compact removed listeners
   - Text capture: after_step
   - Evidence: text output verified by 6 expected checks
   - Expected: canceled.default_action equals `navigate:/escaped`
   - Expected: canceled.event.default_prevented is true
   - Expected: canceled.default_action_allowed is false
   - Expected: session.pending_request_count() equals `0`
   - Expected: halted.actions.len() equals `3`
   - Expected: halted.event.immediate_propagation_stopped is true
- Expose modern Event receiver phase and mutation semantics
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: semantic.event.default_prevented is false
- Ok
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: value equals `true:true:2`
- Ok
   - Text capture: after_step
- fail
   - Text capture: after_step
- Err
   - Text capture: after_step
- fail
   - Text capture: after_step
- Ok
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: value is true
- Ok
   - Text capture: after_step
- fail
   - Text capture: after_step
- Err
   - Text capture: after_step
- fail
   - Text capture: after_step
   - Evidence: text output verified by 3 expected checks
   - Expected: mutation_first.actions.len() equals `2`
   - Expected: mutation_second.actions.len() equals `2`
   - Expected: session.dom_callback_count equals `23`
- Keep requestAnimationFrame alive beside DOM listener delivery
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: session.advance_time(16) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 81 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Deliver JavaScript and Simple Script listeners on the live DOM")
var session = BrowserSession.new()
match session.open_html(
    "https://example.test/events", CALLABLE_EVENT_HTML
):
    Ok(_):
        ()
    Err(reason):
        fail("event fixture failed to open: {reason}")
expect(session.current_title).to_equal("simple,")

step("Dispatch capture target and bubble listeners through window and document")
val ordered = session.dispatch_dom_event(
    "run", "click", true, true
)
expect(ordered.actions.len()).to_equal(9)
expect(session.current_title).to_equal(
    "simple," +
    "window-capture,document-capture,outer-capture," +
    "target-capture,inline,target-bubble,outer-bubble," +
    "document-bubble,window-bubble,"
)

step("Cancel defaults and compact removed listeners")
val canceled = session.dispatch_dom_event(
    "blocked", "click", true, true
)
expect(canceled.default_action).to_equal("navigate:/escaped")
expect(canceled.event.default_prevented).to_equal(true)
expect(canceled.default_action_allowed).to_equal(false)
expect(session.pending_request_count()).to_equal(0)
expect(session.current_title).to_end_with(
    "window-capture,document-capture,cancel,after-cancel," +
    "document-bubble,window-bubble,"
)
val halted = session.dispatch_dom_event(
    "halt", "click", true, true
)
expect(halted.actions.len()).to_equal(3)
expect(halted.event.immediate_propagation_stopped).to_equal(true)
expect(session.current_title).to_end_with(
    "window-capture,document-capture,halt-first,"
)
step("Expose modern Event receiver phase and mutation semantics")
val semantic = session.dispatch_dom_event(
    "probe", "probe", false, false
)
expect(semantic.event.default_prevented).to_equal(false)
match session.eval_script("semantic"):
    Ok(JsValue.String(value)):
        expect(value).to_equal("true:true:2")
    Ok(_):
        fail("event semantic probe returned a non-string")
    Err(reason):
        fail("event semantic probe failed: {reason}")
match session.eval_script(
    "lastEvent.currentTarget===null&&lastEvent.eventPhase===0"
):
    Ok(JsValue.Boolean(value)):
        expect(value).to_equal(true)
    Ok(_):
        fail("event reset probe returned a non-boolean")
    Err(reason):
        fail("event reset probe failed: {reason}")
val mutation_first = session.dispatch_dom_event(
    "mutate", "mutate", false, true
)
expect(mutation_first.actions.len()).to_equal(2)
expect(session.current_title).to_end_with("mutate,")
val mutation_second = session.dispatch_dom_event(
    "mutate", "mutate", false, true
)
expect(mutation_second.actions.len()).to_equal(2)
expect(session.current_title).to_end_with("mutate,mutate,added,")
expect(session.dom_callback_count).to_equal(23)

step("Keep requestAnimationFrame alive beside DOM listener delivery")
expect(session.advance_time(16)).to_equal(1)
expect(session.current_title).to_end_with(
    "mutate,mutate,added,raf,"
)
```

</details>

#### should fail closed for synchronous JavaScript-originated dispatchEvent

- var session = BrowserSession new
   - Text capture: after_step
- "window addEventListener
   - Text capture: after_step
- Ok
   - Text capture: after_step
-
   - Text capture: after_step
- Err
   - Text capture: after_step
- fail
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: session.current_title equals `unchanged`
- Ok
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: value is false
- Ok
   - Text capture: after_step
- fail
   - Text capture: after_step
- Err
   - Text capture: after_step
- fail
   - Text capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
match session.open_html(
    "https://example.test/script-dispatch",
    "<html><body><script>document.title='unchanged';" +
    "window.addEventListener('probe',function(event){" +
    "document.title='unexpected';});" +
    "window.__dispatchResult=window.dispatchEvent({" +
    "type:'probe',bubbles:true,cancelable:true});" +
    "</script></body></html>"
):
    Ok(_):
        ()
    Err(reason):
        fail("dispatchEvent fail-closed fixture failed: {reason}")
expect(session.current_title).to_equal("unchanged")
match session.eval_script("window.__dispatchResult"):
    Ok(JsValue.Boolean(value)):
        expect(value).to_equal(false)
    Ok(_):
        fail("dispatchEvent result probe returned a non-boolean")
    Err(reason):
        fail("dispatchEvent result probe failed: {reason}")
expect(session.warnings.join("|")).to_contain(
    "synchronous script dispatchEvent is unsupported"
)
```

</details>

#### should render the supported HTML and CSS profile through canonical Draw IR

-  production browser fixture
   - GUI capture: after_step (HTML preferred when available)
-  open conformance page
   - GUI capture: after_step (HTML preferred when available)
-  check canonical draw ir
   - GUI capture: after_step (HTML preferred when available)
-  require production browser evidence
   - GUI capture: after_step (HTML preferred when available)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_production_browser_fixture()
_open_conformance_page()
_check_canonical_draw_ir()
_require_production_browser_evidence()
```

</details>

#### should animate JavaScript timers requestAnimationFrame and CSS on one clock

-  production browser fixture
   - GUI capture: after_step (HTML preferred when available)
-  advance browser clock
   - GUI capture: after_step (HTML preferred when available)
-  check canonical draw ir
   - GUI capture: after_step (HTML preferred when available)
- fail
   - GUI capture: after_step (HTML preferred when available)
- file hash sha256
   - GUI capture: after_step (HTML preferred when available)
- fail
   - GUI capture: after_step (HTML preferred when available)
- var renderer = HostedBrowserRendererProcess create
   - GUI capture: after_step (HTML preferred when available)
- raster shutdown
   - GUI capture: after_step (HTML preferred when available)
- fail
   - GUI capture: after_step (HTML preferred when available)
-  close browser animation evidence
   - GUI capture: after_step (HTML preferred when available)
- fail
   - GUI capture: after_step (HTML preferred when available)
- Err
   - GUI capture: after_step (HTML preferred when available)
-  close browser animation evidence
   - GUI capture: after_step (HTML preferred when available)
- fail
   - GUI capture: after_step (HTML preferred when available)
- Ok
   - GUI capture: after_step (HTML preferred when available)
-  close browser animation evidence
   - GUI capture: after_step (HTML preferred when available)
- fail
   - GUI capture: after_step (HTML preferred when available)
- Some
   - GUI capture: after_step (HTML preferred when available)
-  close browser animation evidence
   - GUI capture: after_step (HTML preferred when available)
- fail
   - GUI capture: after_step (HTML preferred when available)
-  close browser animation evidence
   - GUI capture: after_step (HTML preferred when available)
- fail
   - GUI capture: after_step (HTML preferred when available)
-  close browser animation evidence
   - GUI capture: after_step (HTML preferred when available)
- initial composition batches[0] commands len
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 4 expected checks
   - Expected: first.pixels.len() equals `64 * 48`
   - Expected: second.pixels.len() equals `64 * 48`
   - Expected: changed is true
   - Expected: advanced.next_animation_ms equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 63 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_production_browser_fixture()
_advance_browser_clock()
_check_canonical_draw_ir()
val artifact = env_get("HOSTED_WM_ARTIFACT")
val expected_artifact_sha = env_get("HOSTED_WM_ARTIFACT_SHA256")
if artifact == "":
    fail("HOSTED_WM_ARTIFACT must name the hosted_entry native binary")
if expected_artifact_sha.len() != 64 or
    file_hash_sha256(artifact) != expected_artifact_sha:
    fail("HOSTED_WM_ARTIFACT does not match its admitted SHA-256")
var renderer = HostedBrowserRendererProcess.create(1, 64, 48)
val raster = Engine2dCompositorBackend.create_named(
    64, 48, "software"
)
val started = renderer.start(artifact, 2000)
if not started.ok:
    raster.shutdown()
    fail("browser renderer launch failed: {started.reason}")
val initial = renderer.render(
    "init", SUBPROCESS_ANIMATION_HTML, 2000
)
if not initial.ok:
    _close_browser_animation_evidence(renderer, raster)
    fail("browser renderer initial frame failed: {initial.reason}")
val first = raster.render_draw_ir_composition(
    initial.composition, []
)
match renderer.begin_advance(16, 2000):
    Err(reason):
        _close_browser_animation_evidence(renderer, raster)
        fail("browser renderer animation start failed: {reason}")
    Ok(started_advance):
        if not started_advance:
            _close_browser_animation_evidence(renderer, raster)
            fail("browser renderer animation did not start")
val advanced = match _await_browser_animation(renderer):
    Some(frame):
        frame
    nil:
        _close_browser_animation_evidence(renderer, raster)
        fail("browser renderer animation poll exhausted")
if not advanced.ok:
    _close_browser_animation_evidence(renderer, raster)
    fail("browser renderer animation frame failed: {advanced.reason}")
val second = raster.render_draw_ir_composition(
    advanced.composition, []
)
val initial_red = _count_color(first.pixels, 0xFFEF4444u32)
val advanced_blue = _count_color(second.pixels, 0xFF2563EBu32)
val changed = not _pixels_equal(first.pixels, second.pixels)
_close_browser_animation_evidence(renderer, raster)
expect(initial.composition.batches.len()).to_be_greater_than(0)
expect(
    initial.composition.batches[0].commands.len()
).to_be_greater_than(0)
expect(first.rendered_command_count).to_be_greater_than(0)
expect(first.pixels.len()).to_equal(64 * 48)
expect(initial_red).to_be_greater_than(0)
expect(second.rendered_command_count).to_be_greater_than(0)
expect(second.pixels.len()).to_equal(64 * 48)
expect(advanced_blue).to_be_greater_than(0)
expect(changed).to_equal(true)
expect(advanced.next_animation_ms).to_equal(-1)
```

</details>

#### should retain Simple Script callbacks on the canonical animation clock

- Register callbacks without invoking the denied ambient ScriptRunner
   - Text capture: after_step
- var session = BrowserSession new
   - Text capture: after_step
- Ok
   - Text capture: after_step
-
   - Text capture: after_step
- Err
   - Text capture: after_step
- fail
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: session.simple_script_callback_count() equals `0`
- Reuse one retained callback identity for rAF and timeout
   - Text capture: after_step
   - Evidence: text output verified by 4 expected checks
   - Expected: session.advance_time(5) equals `1`
   - Expected: session.current_title equals `frame`
   - Expected: session.advance_time(10) equals `2`
   - Expected: session.current_title equals `frame`
- Apply style from an interval and keep a canceled callback inert
   - Text capture: after_step
   - Evidence: text output verified by 5 expected checks
   - Expected: session.advance_time(15) equals `1`
   - Expected: session.advance_time(30) equals `1`
   - Expected: session.current_title equals `frame`
   - Expected: session.style_revision equals `applied_style_revision`
   - Expected: session.simple_script_callback_count() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Register callbacks without invoking the denied ambient ScriptRunner")
var session = BrowserSession.new()
match session.open_html(
    "https://example.test/simple-callbacks",
    RETAINED_SIMPLE_SCRIPT_CALLBACK_HTML
):
    Ok(_):
        ()
    Err(reason):
        fail("Simple Script callback fixture failed to open: {reason}")
expect(session.simple_script_callback_count()).to_equal(0)
expect(session.current_title).to_equal(
    "https://example.test/simple-callbacks"
)

step("Reuse one retained callback identity for rAF and timeout")
expect(session.advance_time(5)).to_equal(1)
expect(session.current_title).to_equal("frame")
expect(session.advance_time(10)).to_equal(2)
expect(session.current_title).to_equal("frame")
expect(session.current_body_html).to_contain("timeout")

step("Apply style from an interval and keep a canceled callback inert")
expect(session.advance_time(15)).to_equal(1)
expect(session.current_style_html).to_contain("#2563eb")
val styled = session.render_to_pixels(16, 16)
expect(_count_color(
    styled.pixels, 0xFF2563EBu32
)).to_be_greater_than(0)
val applied_style_revision = session.style_revision
expect(session.advance_time(30)).to_equal(1)
expect(session.current_title).to_equal("frame")
expect(session.style_revision).to_equal(applied_style_revision)
expect(session.simple_script_callback_count()).to_equal(5)
expect(session.warnings).to_contain(
    "simple script unsupported command: unsafe_eval title \"bypass\""
)
```

</details>

#### should reclaim retained Simple Script document owners on navigation and close

- Open retained Simple Script state and bind one document owner
   - Text capture: after_step
- var session = BrowserSession new
   - Text capture: after_step
- Ok
   - Text capture: after_step
-
   - Text capture: after_step
- Err
   - Text capture: after_step
- fail
   - Text capture: after_step
   - Evidence: text output verified by 3 expected checks
   - Expected: session.simple_script_executor.has_callback(41) is true
   - Expected: session.advance_time(5) equals `1`
   - Expected: session.simple_script_callback_count() equals `1`
- session simple script executor log
   - Text capture: after_step
- session simple script executor console buffer
   - Text capture: after_step
- Navigate to a fresh page and reset document-owned script state
   - Text capture: after_step
- Ok
   - Text capture: after_step
-
   - Text capture: after_step
- Err
   - Text capture: after_step
- fail
   - Text capture: after_step
- session simple script executor event loop
   - Text capture: after_step
- session simple script executor event loop
   - Text capture: after_step
   - Evidence: text output verified by 2 expected checks
   - Expected: session.simple_script_callback_count() equals `0`
   - Expected: session.simple_script_executor.has_callback(41) is false
- session simple script executor  callback sources len
   - Text capture: after_step
- session simple script executor console buffer
   - Text capture: after_step
- Retain fresh callback timer animation and console state
   - Text capture: after_step
- session simple script executor schedule timeout
   - Text capture: after_step
- session simple script executor schedule animation frame
   - Text capture: after_step
   - Evidence: text output verified by 3 expected checks
   - Expected: fresh_callbacks.len() equals `1`
   - Expected: fresh_callbacks[0] equals `title "fresh"`
   - Expected: session.simple_script_callback_count() equals `1`
- session simple script executor schedule animation frame
   - Text capture: after_step
- session simple script executor log
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: session.simple_script_executor.has_callback(91) is true
- session simple script executor event loop
   - Text capture: after_step
- session simple script executor event loop
   - Text capture: after_step
- session simple script executor console buffer
   - Text capture: after_step
- Close the page and reclaim browser resources
   - Text capture: after_step
- session close
   - Text capture: after_step
- session simple script executor event loop
   - Text capture: after_step
- session simple script executor event loop
   - Text capture: after_step
   - Evidence: text output verified by 3 expected checks
   - Expected: session.simple_script_callback_count() equals `0`
   - Expected: session.simple_script_executor.has_callback(41) is false
   - Expected: session.simple_script_executor.has_callback(91) is false
- session simple script executor  callback sources len
   - Text capture: after_step
- session simple script executor console buffer
   - Text capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 110 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Open retained Simple Script state and bind one document owner")
var session = BrowserSession.new()
val retained_executor = session.simple_script_executor
match session.open_html(
    "https://example.test/retained-close",
    RETAINED_SIMPLE_SCRIPT_CALLBACK_HTML
):
    Ok(_):
        ()
    Err(reason):
        fail("Simple Script close fixture failed to open: {reason}")
expect(
    session.simple_script_executor._runner.dom_root
).to_be(session.current_dom)
expect(session.simple_script_executor.has_callback(41)).to_equal(true)
expect(
    session.simple_script_executor._callback_sources
).to_contain("title \"frame\"")
expect(session.advance_time(5)).to_equal(1)
expect(session.simple_script_callback_count()).to_equal(1)
session.simple_script_executor.log("log", "document-owned", 0)
expect(
    session.simple_script_executor.console_buffer().entries().len()
).to_be_greater_than(0)

step("Navigate to a fresh page and reset document-owned script state")
match session.open_html(
    "https://example.test/replaced", "<main>replaced</main>"
):
    Ok(_):
        ()
    Err(reason):
        fail("Simple Script replacement fixture failed to open: {reason}")
expect(session.simple_script_executor).to_be(retained_executor)
expect(
    session.simple_script_executor._runner.dom_root
).to_be(session.current_dom)
expect(
    session.simple_script_executor._runner.event_loop
).to_be(session.simple_script_executor.event_loop())
expect(
    session.simple_script_executor.event_loop().pending_timer_count()
).to_equal(0)
expect(
    session.simple_script_executor.event_loop().pending_raf_count()
).to_equal(0)
expect(session.simple_script_callback_count()).to_equal(0)
expect(session.simple_script_executor.has_callback(41)).to_equal(false)
expect(
    session.simple_script_executor._callback_sources.len()
).to_equal(0)
expect(
    session.simple_script_executor.console_buffer().entries().len()
).to_equal(0)

step("Retain fresh callback timer animation and console state")
expect(
    session.simple_script_executor.register_callback(
        91, "title \"fresh\""
    )
).to_equal(true)
expect(
    session.simple_script_executor.schedule_timeout(91, 0, 1000)
).to_equal(1)
expect(
    session.simple_script_executor.schedule_animation_frame(91)
).to_equal(true)
val fresh_callbacks = session.simple_script_executor.tick(0)
expect(fresh_callbacks.len()).to_equal(1)
expect(fresh_callbacks[0]).to_equal("title \"fresh\"")
expect(session.simple_script_callback_count()).to_equal(1)
expect(
    session.simple_script_executor.schedule_animation_frame(91)
).to_equal(true)
session.simple_script_executor.log("log", "fresh-document-owned", 0)
expect(session.simple_script_executor.has_callback(91)).to_equal(true)
expect(
    session.simple_script_executor.event_loop().pending_timer_count()
).to_equal(1)
expect(
    session.simple_script_executor.event_loop().pending_raf_count()
).to_equal(1)
expect(
    session.simple_script_executor.console_buffer().entries().len()
).to_be_greater_than(0)

step("Close the page and reclaim browser resources")
session.close()
expect(session.simple_script_executor).to_be(retained_executor)
expect(
    session.simple_script_executor._runner.dom_root
).to_be(session.current_dom)
expect(
    session.simple_script_executor._runner.event_loop
).to_be(session.simple_script_executor.event_loop())
expect(
    session.simple_script_executor.event_loop().pending_timer_count()
).to_equal(0)
expect(
    session.simple_script_executor.event_loop().pending_raf_count()
).to_equal(0)
expect(session.simple_script_callback_count()).to_equal(0)
expect(session.simple_script_executor.has_callback(41)).to_equal(false)
expect(session.simple_script_executor.has_callback(91)).to_equal(false)
expect(
    session.simple_script_executor._callback_sources.len()
).to_equal(0)
expect(
    session.simple_script_executor.console_buffer().entries().len()
).to_equal(0)
```

</details>

#### should retain immediate Simple Script style through finalization

- var session = BrowserSession new
   - GUI capture: after_step (HTML preferred when available)
- Ok
   - GUI capture: after_step (HTML preferred when available)
-
   - GUI capture: after_step (HTML preferred when available)
- Err
   - GUI capture: after_step (HTML preferred when available)
- fail
   - GUI capture: after_step (HTML preferred when available)


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
match session.open_html(
    "https://example.test/simple-style",
    IMMEDIATE_SIMPLE_SCRIPT_STYLE_HTML
):
    Ok(_):
        ()
    Err(reason):
        fail("immediate Simple Script style failed to open: {reason}")
expect(session.current_style_html).to_contain(
    "background-color:#ef4444"
)
expect(session.current_style_html).to_end_with(
    "<style>#box{background-color:#2563eb}</style>"
)
expect(session.current_style_html.split(
    "<style>#box{background-color:#2563eb}</style>"
).len()).to_equal(2)
val styled = session.render_to_pixels(16, 16)
expect(_count_color(
    styled.pixels, 0xFF2563EBu32
)).to_be_greater_than(0)
expect(_count_color(
    styled.pixels, 0xFFEF4444u32
)).to_equal(0)
```

</details>

#### should reuse parsed layout work across unchanged animation frames

- Reuse parsed layout work across unchanged animation frames
   - Protocol capture: after_step
- var worker = HostedBrowserRendererWorkerSession create
   - Protocol capture: after_step
   - Evidence: protocol response verified by 15 expected checks
   - Expected: before_serialize equals `1`
   - Expected: before_parse equals `1`
   - Expected: before_css equals `1`
   - Expected: before_style equals `1`
   - Expected: before_layout equals `1`
   - Expected: before_paint equals `1`
   - Expected: before_reuse equals `0`
   - Expected: before_composition_revision equals `1`
   - Expected: after.serialize_count equals `before_serialize`
   - Expected: after.parse_count equals `before_parse`
   - Expected: after.css_count equals `before_css`
   - Expected: after.style_count equals `before_style`
   - Expected: after.layout_count equals `before_layout`
   - Expected: after.paint_count equals `before_paint`
   - Expected: after.reuse_count equals `before_reuse + 1`
- Close the page and reclaim browser resources
   - Protocol capture: after_step
- worker close
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 54 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reuse parsed layout work across unchanged animation frames")
var worker = HostedBrowserRendererWorkerSession.create(64, 48)
val initial = worker.handle(BrowserRendererMessage(
    kind: "init", generation: 7, request_id: 2,
    payload: "<main id='stable'>unchanged</main>"
))
expect(initial.ok).to_be(true)
val counters = worker.render_session.counters
val before_serialize = counters.serialize_count
val before_parse = counters.parse_count
val before_css = counters.css_count
val before_style = counters.style_count
val before_layout = counters.layout_count
val before_paint = counters.paint_count
val before_reuse = counters.reuse_count
val before_composition_revision = counters.composition_revision
expect(before_serialize).to_equal(1)
expect(before_parse).to_equal(1)
expect(before_css).to_equal(1)
expect(before_style).to_equal(1)
expect(before_layout).to_equal(1)
expect(before_paint).to_equal(1)
expect(before_reuse).to_equal(0)
expect(before_composition_revision).to_equal(1)

val unchanged = worker.handle(BrowserRendererMessage(
    kind: "advance", generation: 7, request_id: 3, payload: "16"
))
expect(unchanged.ok).to_be(true)
val after = worker.render_session.counters
expect(after.serialize_count).to_equal(before_serialize)
expect(after.parse_count).to_equal(before_parse)
expect(after.css_count).to_equal(before_css)
expect(after.style_count).to_equal(before_style)
expect(after.layout_count).to_equal(before_layout)
expect(after.paint_count).to_equal(before_paint)
expect(after.reuse_count).to_equal(before_reuse + 1)
expect(after.composition_revision).to_equal(
    before_composition_revision
)
step("Close the page and reclaim browser resources")
worker.close()
expect(
    worker.render_session.counters.retained_node_count
).to_equal(0)
expect(
    worker.render_session.counters.retained_style_count
).to_equal(0)
expect(
    worker.render_session.counters.retained_box_count
).to_equal(0)
expect(
    worker.render_session.counters.retained_command_count
).to_equal(0)
```

</details>

#### should retire cached frame resources before a site replacement is ready

- Render one retained browser frame through the shared compositor
  - Protocol capture: after_step
  - Expected: exactly one compositor render and a 16×16 frame.
- Route the retained generation through a cross-site replacement
  - Protocol capture: after_step
  - Expected: before the replacement can become ready, the old pending pixels,
    retained images, cached resources, and cached result are all empty.

<details>
<summary>Executable SSpec</summary>

```simple
step("Render one retained browser frame through the shared compositor")
var worker = HostedBrowserRendererWorkerSession.create(16, 16)
val initial = worker.handle(BrowserRendererMessage(
    kind: "init", generation: 81, request_id: 2,
    payload: "<main>lifecycle</main>"
))
val frame = browser_renderer_frame_decode(
    browser_renderer_decoder_feed(
        browser_renderer_decoder_new(81), initial.wire
    ).message,
    16, 16
)
expect(frame.ok).to_be(true)
var raster = Engine2dCompositorBackend.create_named(16, 16, "software")
val rendered = raster.render_draw_ir_composition_resources_revision(
    frame.composition, frame.image_resources, 81, frame.composition_revision
)
expect(rendered.pixels.len()).to_equal(16 * 16)
expect(raster.revision_render_count).to_equal(1)

step("Route the retained generation through a cross-site replacement")
var renderer = HostedBrowserRendererProcess.create(81, 16, 16)
renderer.state = "active"
renderer.navigation_permit = HostedBrowserNavigationPermit(
    active: true, url: "https://replacement.test/page", method: "GET",
    headers: "", body: "", content_type: "", redirect_count: 0
)
renderer.site_lock = "https://old.test"
renderer.site_swap_pending = true
renderer.site_swap_site = "https://replacement.test"
renderer.retained_image_resources = [simpleos_host_gpu_image_resource(
    "asset://lifecycle", 1, 1, [0xFF2563EBu32]
)]
var entry = HostedBrowserRendererEntry.create(81, renderer, raster, 0, "")
entry.ready = true
entry.pending_frame = WmContentFrame(
    window_id: "81", scene_revision: 1, content_revision: 1,
    origin_kind: "web", width: 16, height: 16, pixels: rendered.pixels,
    checksum: 1u64, parent_window_id: "", offset_x: 0, offset_y: 0
)
var registry = HostedBrowserRendererRegistry.create(
    "/bin/true", ""
)
registry.entries.push(entry)
val routed = registry._accept_polled_result(
    0,
    HostedBrowserRendererResult(
        ok: false, reason: HOSTED_BROWSER_SITE_SWAP_REQUIRED,
        next_animation_ms: -1, producer_generation: 81, composition_revision: 1,
        composition: frame.composition, image_resources: [],
        cpu_composited_count: 0, cpu_composited_sha256: "",
        solid_material_count: 0, solid_material_sha256: "", diagnostics: ""
    ),
    "", "", 0, 0
)
expect(routed).to_equal("none")
val retired = registry.entries[0]
expect(retired.ready).to_be(false)
expect(retired.renderer.state).to_equal("starting")
expect(retired.renderer_closed).to_be(false)
expect(retired.pending_frame.pixels.len()).to_equal(0)
expect(retired.renderer.retained_image_resources.len()).to_equal(0)
expect(retired.raster.revision_cache_resources.len()).to_equal(0)
expect(retired.raster.revision_cache_result).to_be_nil()
val _ = registry.close()
worker.close()
```

</details>

#### should invalidate only dirty retained browser render stages

- Invalidate document and title changes conservatively
   - Protocol capture: after_step
- var document worker = HostedBrowserRendererWorkerSession create
   - Protocol capture: after_step
- document worker render session composition checksum
   - Protocol capture: after_step
- document worker render session composition checksum
   - Protocol capture: after_step
- document worker render session composition checksum
   - Protocol capture: after_step
- Invalidate stylesheet and viewport stages
   - Protocol capture: after_step
- var style worker = HostedBrowserRendererWorkerSession create
   - Protocol capture: after_step
- style worker browser  advance style revision
   - Protocol capture: after_step
- browser renderer decoder new
   - Protocol capture: after_step
- Repaint changed image pixels without rebuilding semantic stages
   - Protocol capture: after_step
- var image worker = HostedBrowserRendererWorkerSession create
   - Protocol capture: after_step
-  retained png hex
   - Protocol capture: after_step
- image worker render session composition checksum
   - Protocol capture: after_step
- image worker browser  advance resource revision
   - Protocol capture: after_step
- image worker render session composition checksum
   - Protocol capture: after_step
- Reuse parsed layout work across unchanged animation frames
   - Protocol capture: after_step
- Render HTML and CSS through canonical Draw IR
   - Protocol capture: after_step
- var animation worker = HostedBrowserRendererWorkerSession create
   - Protocol capture: after_step
- animation worker render session composition checksum
   - Protocol capture: after_step
- animation worker render session composition checksum
   - Protocol capture: after_step
- var width worker = HostedBrowserRendererWorkerSession create
   - Protocol capture: after_step
- width worker render session current result unwrap
   - Protocol capture: after_step
- width worker render session composition checksum
   - Protocol capture: after_step
- width worker render session current result unwrap
   - Protocol capture: after_step
- width worker render session current result unwrap
   - Protocol capture: after_step
- width worker render session current result unwrap
   - Protocol capture: after_step
- width raster shutdown
   - Protocol capture: after_step
-  pixels equal
   - Protocol capture: after_step
- width worker render session composition checksum
   - Protocol capture: after_step
- Repaint scroll and caret overlays from retained raw layout
   - Protocol capture: after_step
- var scroll worker = HostedBrowserRendererWorkerSession create
   - Protocol capture: after_step
- scroll worker render session composition checksum
   - Protocol capture: after_step
- browser renderer decoder new
   - Protocol capture: after_step
- scroll worker render session composition checksum
   - Protocol capture: after_step
- var caret worker = HostedBrowserRendererWorkerSession create
   - Protocol capture: after_step
- caret worker render session composition checksum
   - Protocol capture: after_step
- caret worker render session composition checksum
   - Protocol capture: after_step
- Replace navigation state without retaining prior documents
   - Protocol capture: after_step
- HostedBrowserRendererWorkerSession create
   - Protocol capture: after_step
- payload:
   - Protocol capture: after_step
- Close the page and reclaim browser resources
   - Protocol capture: after_step
- navigation worker close
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 252 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Invalidate document and title changes conservatively")
var document_worker = HostedBrowserRendererWorkerSession.create(64, 48)
expect(document_worker.handle(BrowserRendererMessage(
    kind: "init", generation: 7, request_id: 2,
    payload: "<title>before</title><main>first</main>"
)).ok).to_be(true)
val initial_checksum = (
    document_worker.render_session.composition_checksum()
)
expect(document_worker.browser.eval_script(
    "document.title = 'after'"
).is_ok()).to_be(true)
expect(document_worker.handle(BrowserRendererMessage(
    kind: "advance", generation: 7, request_id: 3, payload: "16"
)).ok).to_be(true)
_expect_retained_stage_counts(
    document_worker.render_session.counters, 2, 2, 2, 2, 2, 2, 2
)
expect(
    document_worker.render_session.composition_checksum()
).to_equal(initial_checksum)
expect(document_worker.browser.eval_script(
    "document.body.innerHTML = '<main>second</main>'"
).is_ok()).to_be(true)
expect(document_worker.handle(BrowserRendererMessage(
    kind: "advance", generation: 7, request_id: 4, payload: "32"
)).ok).to_be(true)
_expect_retained_stage_counts(
    document_worker.render_session.counters, 3, 3, 3, 3, 3, 3, 3
)
expect(
    document_worker.render_session.composition_checksum() ==
    initial_checksum
).to_be(false)

step("Invalidate stylesheet and viewport stages")
var style_worker = HostedBrowserRendererWorkerSession.create(64, 48)
expect(style_worker.handle(BrowserRendererMessage(
    kind: "init", generation: 7, request_id: 2,
    payload: "<main style='width:32px;height:8px'>style</main>"
)).ok).to_be(true)
style_worker.browser.current_style_html = (
    "<style>main{color:#2563eb}</style>"
)
style_worker.browser._advance_style_revision()
expect(style_worker.handle(BrowserRendererMessage(
    kind: "advance", generation: 7, request_id: 3, payload: "16"
)).ok).to_be(true)
_expect_retained_stage_counts(
    style_worker.render_session.counters, 2, 2, 2, 2, 2, 2, 2
)
val resize = browser_renderer_resize_encode(7, 4, 96, 48)
expect(style_worker.handle(browser_renderer_decoder_feed(
    browser_renderer_decoder_new(7), resize.wire
).message).ok).to_be(true)
_expect_retained_stage_counts(
    style_worker.render_session.counters, 2, 2, 3, 3, 3, 3, 3
)

step("Repaint changed image pixels without rebuilding semantic stages")
var image_worker = HostedBrowserRendererWorkerSession.create(64, 48)
image_worker.browser.register_resource(
    "https://assets.test/pixel.png",
    _retained_png_hex(0xFF123456u32)
)
expect(image_worker.handle(BrowserRendererMessage(
    kind: "init", generation: 7, request_id: 2,
    payload: "<img src='https://assets.test/pixel.png'>"
)).ok).to_be(true)
val image_uri = image_worker.browser.image_resources[0].image_uri
val image_checksum = (
    image_worker.render_session.composition_checksum()
)
image_worker.browser.image_resources = [
    simpleos_host_gpu_image_resource(
        image_uri, 1, 1, [0xFFABCDEFu32]
    )
]
image_worker.browser._advance_resource_revision()
expect(image_worker.handle(BrowserRendererMessage(
    kind: "advance", generation: 7, request_id: 3, payload: "16"
)).ok).to_be(true)
_expect_retained_stage_counts(
    image_worker.render_session.counters, 1, 1, 1, 1, 1, 2, 2
)
expect(
    image_worker.render_session.composition_checksum()
).to_equal(image_checksum)

step("Reuse parsed layout work across unchanged animation frames")
step("Render HTML and CSS through canonical Draw IR")
var animation_worker = HostedBrowserRendererWorkerSession.create(64, 48)
expect(animation_worker.handle(BrowserRendererMessage(
    kind: "init", generation: 7, request_id: 2,
    payload: "<style>@keyframes pulse{from{background-color:#ef4444}to{background-color:#2563eb}}#stage{width:32px;height:24px;background-color:#ef4444;animation:pulse 1000ms linear forwards}</style><div id='stage'></div>"
)).ok).to_be(true)
val animation_checksum = (
    animation_worker.render_session.composition_checksum()
)
expect(animation_worker.handle(BrowserRendererMessage(
    kind: "advance", generation: 7, request_id: 3, payload: "500"
)).ok).to_be(true)
_expect_retained_stage_counts(
    animation_worker.render_session.counters, 1, 1, 1, 2, 1, 2, 2
)
expect(
    animation_worker.render_session.composition_checksum() ==
    animation_checksum
).to_be(false)

var width_worker = HostedBrowserRendererWorkerSession.create(64, 48)
expect(width_worker.handle(BrowserRendererMessage(
    kind: "init", generation: 7, request_id: 2,
    payload: "<style>@keyframes grow{from{width:8px}to{width:32px}}#stage{width:8px;height:24px;background-color:#2563eb;animation:grow 1000ms linear forwards}</style><div id='stage'></div>"
)).ok).to_be(true)
val width_raster = Engine2dCompositorBackend.create_named(
    64, 48, "software"
)
val width_before_pixels = width_raster.render_draw_ir_composition(
    width_worker.render_session.current_result.unwrap().composition,
    []
).pixels
val width_checksum = (
    width_worker.render_session.composition_checksum()
)
expect(simple_web_layout_hit_test_index(
    width_worker.render_session.current_result.unwrap().hit_index,
    20, 4
)).to_equal("path:")
expect(width_worker.handle(BrowserRendererMessage(
    kind: "advance", generation: 7, request_id: 3, payload: "500"
)).ok).to_be(true)
_expect_retained_stage_counts(
    width_worker.render_session.counters, 1, 1, 1, 2, 2, 2, 2
)
expect(simple_web_layout_hit_test_index(
    width_worker.render_session.current_result.unwrap().hit_index,
    20, 4
)).to_equal("id:stage")
val width_after_pixels = width_raster.render_draw_ir_composition(
    width_worker.render_session.current_result.unwrap().composition,
    []
).pixels
width_raster.shutdown()
expect(
    _pixels_equal(width_before_pixels, width_after_pixels)
).to_be(false)
expect(
    width_worker.render_session.composition_checksum() ==
    width_checksum
).to_be(false)

step("Repaint scroll and caret overlays from retained raw layout")
var scroll_worker = HostedBrowserRendererWorkerSession.create(64, 48)
expect(scroll_worker.handle(BrowserRendererMessage(
    kind: "init", generation: 7, request_id: 2,
    payload: "<main style='height:160px'>scroll</main>"
)).ok).to_be(true)
val scroll_checksum = (
    scroll_worker.render_session.composition_checksum()
)
val scroll = browser_renderer_scroll_encode(7, 3, 1, 16000)
expect(scroll_worker.handle(browser_renderer_decoder_feed(
    browser_renderer_decoder_new(7), scroll.wire
).message).ok).to_be(true)
_expect_retained_stage_counts(
    scroll_worker.render_session.counters, 1, 1, 1, 1, 1, 2, 2
)
expect(
    scroll_worker.render_session.composition_checksum() ==
    scroll_checksum
).to_be(false)
var caret_worker = HostedBrowserRendererWorkerSession.create(64, 48)
expect(caret_worker.handle(BrowserRendererMessage(
    kind: "init", generation: 7, request_id: 2,
    payload: "<input id='field' data-focused value='caret'>"
)).ok).to_be(true)
val caret_checksum = (
    caret_worker.render_session.composition_checksum()
)
expect(caret_worker.handle(BrowserRendererMessage(
    kind: "advance", generation: 7, request_id: 3, payload: "600"
)).ok).to_be(true)
_expect_retained_stage_counts(
    caret_worker.render_session.counters, 1, 1, 1, 1, 1, 2, 2
)
expect(
    caret_worker.render_session.composition_checksum() ==
    caret_checksum
).to_be(false)

step("Replace navigation state without retaining prior documents")
var navigation_worker = (
    HostedBrowserRendererWorkerSession.create(64, 48)
)
expect(navigation_worker.handle(BrowserRendererMessage(
    kind: "init", generation: 7, request_id: 2,
    payload: "<main id='page'>page-0</main>"
)).ok).to_be(true)
val retained_nodes = (
    navigation_worker.render_session.counters.retained_node_count
)
val retained_styles = (
    navigation_worker.render_session.counters.retained_style_count
)
val retained_boxes = (
    navigation_worker.render_session.counters.retained_box_count
)
val retained_commands = (
    navigation_worker.render_session.counters.retained_command_count
)
var replacement: i64 = 1
while replacement <= 4:
    expect(navigation_worker.browser.open_html(
        "simple-renderer://replacement-{replacement}",
        "<main id='page'>page-{replacement}</main>"
    ).is_ok()).to_be(true)
    expect(navigation_worker.handle(BrowserRendererMessage(
        kind: "advance", generation: 7,
        request_id: replacement + 2,
        payload: (replacement * 16).to_text()
    )).ok).to_be(true)
    expect(
        navigation_worker.render_session.counters.retained_node_count
    ).to_equal(retained_nodes)
    expect(
        navigation_worker.render_session.counters.retained_style_count
    ).to_equal(retained_styles)
    expect(
        navigation_worker.render_session.counters.retained_box_count
    ).to_equal(retained_boxes)
    expect(
        navigation_worker.render_session.counters.retained_command_count
    ).to_equal(retained_commands)
    replacement = replacement + 1
_expect_retained_stage_counts(
    navigation_worker.render_session.counters, 5, 5, 5, 5, 5, 5, 5
)
step("Close the page and reclaim browser resources")
navigation_worker.close()
expect(
    navigation_worker.render_session.counters.retained_node_count
).to_equal(0)
expect(
    navigation_worker.render_session.counters.retained_style_count
).to_equal(0)
expect(
    navigation_worker.render_session.counters.retained_box_count
).to_equal(0)
expect(
    navigation_worker.render_session.counters.retained_command_count
).to_equal(0)
```

</details>

#### should bound per-frame CSS animation property work

Runtime PASS is unclaimed. This manual records the executable SSpec contract
and the production diagnostic provenance for the current-source runner lane.

- Load the bounded browser fixture
   - Load the 16-property animation fixture through the retained renderer.
   - Require exact canonical `html_ast` Draw IR for the visible `bounded`
     rectangle and an independent full `64x48` software framebuffer oracle.
   - Record retained node, style, box, command, Draw IR checksum, and pixel
     checksum baselines.
- Exercise repeated navigation animation and events
   - Replace the document four times, alternating 32 and 16 animated
     properties, advance the browser animation clock, and dispatch the hidden
     event control.
   - After every full animation frame, force a retained resource-only paint at
     the same clock value. Require zero current-frame animation-property work,
     an unchanged full Draw IR checksum and framebuffer, and unchanged retained
     node, style, box, and command owners.
- Measure retained state and work growth
   - Require the legacy linear-search model to report exactly 376 comparisons
     for 16 properties and 1,520 for 32 properties.
   - Require production full-frame property-index work to remain exactly 32
     and 64 probes, respectively, and never exceed `2P`; require all four
     intervening paint-only frames to report exactly zero rather than a copied
     cumulative count.
- Prove stable Draw IR output within the resource ceiling
   - Recheck exact Draw IR geometry/color, every framebuffer pixel, and both
     checksums independently of the frame-local work counter. Non-animation
     retained CSS, resource, scroll, and caret modes also report zero work.
   - Require retained node, style, box, and command counts below 65,537, then
     close the worker and require all four retained owners plus the current
     result to be released.

<details>
<summary>Executable SSpec</summary>

The complete direct-assertion scenario and its bounded 16/32-property fixture
are maintained in
`test/03_system/app/browser/feature/simple_web_browser_engine_production_hardening_spec.spl`.

</details>

#### should serialize bounded replacements with stable Draw IR

- Load the bounded browser fixture
   - Protocol capture: after_step
- Exercise repeated layout navigation or animation
   - Protocol capture: after_step
- Measure retained state and work growth
   - Protocol capture: after_step
   - Expected: 4K retained nodes grow from 2K but remain below 3x
- Prove stable Draw IR output within the resource ceiling
   - Protocol capture: after_step
   - Expected: repeated 4K fixture emits `html_ast` Draw IR
   - Expected: `bounded` is an exact `(0, 0, 16, 16)` `#123456` rectangle
   - Expected: serialized DOM length matches the pinned 4K fixture formula
   - Expected: serialized DOM remains within the enforced 50 MiB ceiling
   - Expected: retained stage counts replace rather than accumulate
   - Expected: retained nodes, styles, boxes, and commands stay below 65,537


<details>
<summary>Executable SSpec</summary>

Runnable source: 96 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Load the bounded browser fixture")
val smaller = _bounded_serialization_fixture(2048)
val larger = _bounded_serialization_fixture(4096)
var worker = HostedBrowserRendererWorkerSession.create(64, 48)
expect(worker.handle(BrowserRendererMessage(
    kind: "init", generation: 91, request_id: 2, payload: smaller
)).ok).to_be(true)
val smaller_nodes = worker.render_session.counters.retained_node_count

step("Exercise repeated layout navigation or animation")
match worker.browser.open_html(
    "simple-renderer://document", larger
):
    Ok(_): ()
    Err(reason): fail("larger bounded fixture failed: {reason}")
expect(worker.handle(BrowserRendererMessage(
    kind: "advance", generation: 91, request_id: 3, payload: "16"
)).ok).to_be(true)
val retained_nodes = worker.render_session.counters.retained_node_count
val retained_styles = worker.render_session.counters.retained_style_count
val retained_boxes = worker.render_session.counters.retained_box_count
val retained_commands = worker.render_session.counters.retained_command_count
_expect_bounded_serialization_draw_ir(
    worker.render_session.current_result.unwrap().composition
)
val serialized_output_length = be_dom_serialize_html(
    worker.browser.current_dom
).len().to_i64()
expect(serialized_output_length).to_equal(
    _bounded_serialization_output_length(4096)
)
expect(serialized_output_length).to_be_less_than(
    BE_DOM_HTML_SERIALIZE_MAX_OUTPUT_LENGTH + 1
)
match worker.browser.open_html(
    "simple-renderer://document", larger
):
    Ok(_): ()
    Err(reason): fail("repeated bounded fixture failed: {reason}")
expect(worker.handle(BrowserRendererMessage(
    kind: "advance", generation: 91, request_id: 4, payload: "32"
)).ok).to_be(true)

step("Measure retained state and work growth")
expect(retained_nodes).to_be_greater_than(smaller_nodes)
expect(retained_nodes).to_be_less_than(smaller_nodes * 3)
expect(worker.render_session.counters.retained_node_count).to_equal(
    retained_nodes
)
expect(worker.render_session.counters.retained_style_count).to_equal(
    retained_styles
)
expect(worker.render_session.counters.retained_box_count).to_equal(
    retained_boxes
)
expect(worker.render_session.counters.retained_command_count).to_equal(
    retained_commands
)
_expect_retained_stage_counts(
    worker.render_session.counters, 3, 3, 3, 3, 3, 3, 3
)

step("Prove stable Draw IR output within the resource ceiling")
_expect_bounded_serialization_draw_ir(
    worker.render_session.current_result.unwrap().composition
)
expect(be_dom_serialize_html(
    worker.browser.current_dom
).len().to_i64()).to_equal(serialized_output_length)
expect(retained_nodes).to_be_greater_than(4096)
expect(retained_nodes).to_be_less_than(65537)
expect(retained_styles).to_be_greater_than(0)
expect(retained_styles).to_be_less_than(65537)
expect(retained_boxes).to_be_greater_than(0)
expect(retained_boxes).to_be_less_than(65537)
expect(retained_commands).to_be_greater_than(0)
expect(retained_commands).to_be_less_than(65537)
worker.close()
expect(worker.render_session.counters.retained_node_count).to_equal(0)
expect(worker.render_session.counters.retained_style_count).to_equal(0)
expect(worker.render_session.counters.retained_box_count).to_equal(0)
expect(worker.render_session.counters.retained_command_count).to_equal(0)
```

</details>

#### should route pointer keyboard focus text and form events in browser order

-  production browser fixture
   - GUI capture: after_step (HTML preferred when available)
-  operate page controls
   - GUI capture: after_step (HTML preferred when available)
- Verify semantic state event history and rendered output
   - GUI capture: after_step (HTML preferred when available)
-  require production browser evidence
   - GUI capture: after_step (HTML preferred when available)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_production_browser_fixture()
_operate_page_controls()
step("Verify semantic state event history and rendered output")
_require_production_browser_evidence()
```

</details>

<details>
<summary>Advanced: should cancel a default action after capture target and bubble dispatch</summary>

#### should cancel a default action after capture target and bubble dispatch

-  production browser fixture
- Cancel a default action after capture target and bubble dispatch
-  require production browser evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_production_browser_fixture()
step("Cancel a default action after capture target and bubble dispatch")
_require_production_browser_evidence()
```

</details>


</details>

#### should operate address back forward stop reload home bookmark and links

-  production browser fixture
   - GUI capture: after_step (HTML preferred when available)
-  operate browser navigation
   - GUI capture: after_step (HTML preferred when available)
- fail
   - GUI capture: after_step (HTML preferred when available)
- file hash sha256
   - GUI capture: after_step (HTML preferred when available)
- fail
   - GUI capture: after_step (HTML preferred when available)
- Cancel address editing and reject a stale cross-window release
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 8 expected checks
   - Expected: registry.address_text(81) equals `about:blank`
   - Expected: registry.address_text(82) equals `about:blank`
   - Expected: registry.address_text(82) does not contain `<`
   - Expected: registry.address_text(82) does not contain `>`
   - Expected: stale_press.reason equals `chrome-pressed`
   - Expected: current_press.reason equals `chrome-pressed`
   - Expected: stale_release.callback_count equals `0`
   - Expected: current_release.reason equals `address-focused`
- Keep a newer same-window control armed after a late release
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 4 expected checks
   - Expected: same_back.reason equals `chrome-pressed`
   - Expected: same_address.reason equals `chrome-pressed`
   - Expected: late_back.callback_count equals `0`
   - Expected: registry.pressed_window_id equals `82`
- Replace page and chrome presses without accepting late releases
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 13 expected checks
   - Expected: page_first.callback_count equals `1`
   - Expected: late_page.callback_count equals `0`
   - Expected: registry.pressed_window_id equals `81`
   - Expected: page_replacement.callback_count equals `1`
   - Expected: late_chrome.callback_count equals `0`
   - Expected: registry.pressed_window_id equals `82`
   - Expected: canceled.callback_count equals `1`
   - Expected: registry.address_text(82) equals `about:blank`
   - Expected: registry.address_text(82) does not contain `<`
   - Expected: registry.address_text(82) does not contain `>`
   - Expected: favorite_press.reason equals `chrome-pressed`
   - Expected: favorite_release.reason equals `favorite-parent`
   - Expected: favorite_release.callback_count equals `0`
- Commit address back forward stop reload and home commands
   - GUI capture: after_step (HTML preferred when available)
- var address = HostedBrowserRendererProcess create
   - GUI capture: after_step (HTML preferred when available)
- browser renderer decoder new
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 2 expected checks
   - Expected: address_command.action equals `open`
   - Expected: address_command.url equals `https://address.test/`
- var back = HostedBrowserRendererProcess create
   - GUI capture: after_step (HTML preferred when available)
- browser renderer decoder new
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 4 expected checks
   - Expected: back_command.action equals `back`
   - Expected: back_command.url equals `https://history.test/one`
   - Expected: back.history_index equals `1`
   - Expected: back.pending_history_index equals `0`
- var forward = HostedBrowserRendererProcess create
   - GUI capture: after_step (HTML preferred when available)
- browser renderer decoder new
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 4 expected checks
   - Expected: forward_command.action equals `forward`
   - Expected: forward_command.url equals `https://history.test/two`
   - Expected: forward.history_index equals `0`
   - Expected: forward.pending_history_index equals `1`
- var stopped = HostedBrowserRendererProcess create
   - GUI capture: after_step (HTML preferred when available)
- browser renderer decoder new
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 2 expected checks
   - Expected: stop_command.action equals `stop`
   - Expected: stopped.pending_document_commit_url equals ``
- var reload = HostedBrowserRendererProcess create
   - GUI capture: after_step (HTML preferred when available)
- browser renderer decoder new
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 1 expected check
   - Expected: reload.pending_history_action equals `replace`
- var home = HostedBrowserRendererProcess create
   - GUI capture: after_step (HTML preferred when available)
- browser renderer decoder new
   - GUI capture: after_step (HTML preferred when available)
- Route bookmark and page-link navigation without forged authority
   - GUI capture: after_step (HTML preferred when available)
- var bookmark = HostedBrowserRendererProcess create
   - GUI capture: after_step (HTML preferred when available)
- browser renderer decoder new
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 1 expected check
   - Expected: bookmark_command.urls[0] equals `https://saved.test/`
- var link = HostedBrowserRendererProcess create
   - GUI capture: after_step (HTML preferred when available)
- Deny a late command from another renderer generation
   - GUI capture: after_step (HTML preferred when available)
- browser renderer decoder new
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 4 expected checks
   - Expected: denied.status equals `violation`
   - Expected: teardown_press.reason equals `chrome-pressed`
   - Expected: registry.pressed_window_id equals `81`
   - Expected: registry.pressed_window_id equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 270 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_production_browser_fixture()
_operate_browser_navigation()
val artifact = env_get("HOSTED_WM_ARTIFACT")
val expected_artifact_sha = env_get("HOSTED_WM_ARTIFACT_SHA256")
if artifact == "":
    fail("HOSTED_WM_ARTIFACT must name the hosted_entry native binary")
if expected_artifact_sha.len() != 64 or
    file_hash_sha256(artifact) != expected_artifact_sha:
    fail("HOSTED_WM_ARTIFACT does not match its admitted SHA-256")

step("Cancel address editing and reject a stale cross-window release")
var registry = HostedBrowserRendererRegistry.create(
    artifact, "https://home.test/"
)
expect(registry.ensure(
    81, "<main>first</main>", 64, 48, 0, 100000
)).to_equal("none")
expect(registry.ensure(
    82, "<main>second</main>", 64, 48, 0, 100000
)).to_equal("none")
expect(registry.address_text(81)).to_equal("about:blank")
expect(registry.address_text(82)).to_equal("about:blank")
expect(registry.address_text(82).contains("<")).to_equal(false)
expect(registry.address_text(82).contains(">")).to_equal(false)
expect(_await_browser_registry_ready(
    registry, 81, "<main>first</main>"
)).to_be(true)
expect(_await_browser_registry_ready(
    registry, 82, "<main>second</main>"
)).to_be(true)
val stale_press = registry.dispatch_chrome_pointer(
    1, 81, "back", true
)
val current_press = registry.dispatch_chrome_pointer(
    2, 82, "address", true
)
val stale_release = registry.dispatch_chrome_pointer(
    3, 81, "back", false
)
val current_release = registry.dispatch_chrome_pointer(
    4, 82, "address", false
)
expect(stale_press.reason).to_equal("chrome-pressed")
expect(current_press.reason).to_equal("chrome-pressed")
expect(stale_release.callback_count).to_equal(0)
expect(stale_release.reason).to_equal(
    "chrome-release-target-mismatch"
)
expect(current_release.reason).to_equal("address-focused")

step("Keep a newer same-window control armed after a late release")
val same_back = registry.dispatch_chrome_pointer(
    10, 82, "back", true
)
val same_address = registry.dispatch_chrome_pointer(
    11, 82, "address", true
)
val late_back = registry.dispatch_chrome_pointer(
    12, 82, "back", false
)
expect(same_back.reason).to_equal("chrome-pressed")
expect(same_address.reason).to_equal("chrome-pressed")
expect(late_back.callback_count).to_equal(0)
expect(late_back.reason).to_equal(
    "chrome-release-target-mismatch"
)
expect(registry.pressed_window_id).to_equal(82)
expect(registry.dispatch_chrome_pointer(
    13, 82, "address", false
).reason).to_equal("address-focused")

step("Replace page and chrome presses without accepting late releases")
val page_first = registry.dispatch_pointer(
    14, 81, 4, 4, true
)
expect(page_first.callback_count).to_equal(1)
expect(registry.dispatch_chrome_pointer(
    15, 81, "address", true
).reason).to_equal("chrome-pressed")
val late_page = registry.dispatch_pointer(
    16, 81, 4, 4, false
)
expect(late_page.callback_count).to_equal(0)
expect(late_page.reason).to_equal(
    "pointer-release-target-mismatch"
)
expect(registry.pressed_window_id).to_equal(81)
expect(registry.dispatch_chrome_pointer(
    17, 81, "address", false
).reason).to_equal("address-focused")

expect(registry.dispatch_chrome_pointer(
    18, 82, "back", true
).reason).to_equal("chrome-pressed")
val page_replacement = registry.dispatch_pointer(
    19, 82, 4, 4, true
)
expect(page_replacement.callback_count).to_equal(1)
val late_chrome = registry.dispatch_chrome_pointer(
    20, 82, "back", false
)
expect(late_chrome.callback_count).to_equal(0)
expect(late_chrome.reason).to_equal(
    "chrome-release-target-mismatch"
)
expect(registry.pressed_window_id).to_equal(82)
expect(registry.dispatch_pointer(
    21, 82, 4, 4, false
).callback_count).to_equal(1)

expect(registry.dispatch_text(
    22, 82, "https://draft.test/"
).callback_count).to_equal(1)
val canceled = registry.dispatch_key_with_shift(
    23, 82, 27, true, false
)
expect(canceled.callback_count).to_equal(1)
expect(registry.address_text(82)).to_equal("about:blank")
expect(registry.address_text(82).contains("<")).to_equal(false)
expect(registry.address_text(82).contains(">")).to_equal(false)
val favorite_press = registry.dispatch_chrome_pointer(
    24, 82, "favorite", true
)
val favorite_release = registry.dispatch_chrome_pointer(
    25, 82, "favorite", false
)
expect(favorite_press.reason).to_equal("chrome-pressed")
expect(favorite_release.reason).to_equal("favorite-parent")
expect(favorite_release.callback_count).to_equal(0)

step("Commit address back forward stop reload and home commands")
var address = HostedBrowserRendererProcess.create(31, 64, 48)
address.state = "active"
expect(address.begin_navigate(
    "https://address.test/", "GET", "", "", "", 2000
).is_ok()).to_be(true)
val address_wire = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(31), address.pending_wire
)
val address_command = browser_renderer_navigation_decode(
    address_wire.message
)
expect(address_command.action).to_equal("open")
expect(address_command.url).to_equal("https://address.test/")
expect(address.navigation_permit.active).to_be(true)

var back = HostedBrowserRendererProcess.create(32, 64, 48)
back.state = "active"
back.history_urls = [
    "https://history.test/one", "https://history.test/two"
]
back.history_index = 1
expect(back.begin_go_back(2000).is_ok()).to_be(true)
val back_command = browser_renderer_navigation_decode(
    browser_renderer_decoder_feed(
        browser_renderer_decoder_new(32), back.pending_wire
    ).message
)
expect(back_command.action).to_equal("back")
expect(back_command.url).to_equal("https://history.test/one")
expect(back.history_index).to_equal(1)
expect(back.pending_history_index).to_equal(0)

var forward = HostedBrowserRendererProcess.create(33, 64, 48)
forward.state = "active"
forward.history_urls = [
    "https://history.test/one", "https://history.test/two"
]
forward.history_index = 0
expect(forward.begin_go_forward(2000).is_ok()).to_be(true)
val forward_command = browser_renderer_navigation_decode(
    browser_renderer_decoder_feed(
        browser_renderer_decoder_new(33), forward.pending_wire
    ).message
)
expect(forward_command.action).to_equal("forward")
expect(forward_command.url).to_equal("https://history.test/two")
expect(forward.history_index).to_equal(0)
expect(forward.pending_history_index).to_equal(1)

var stopped = HostedBrowserRendererProcess.create(34, 64, 48)
stopped.state = "active"
expect(stopped.begin_navigate(
    "https://late.test/", "GET", "", "", "", 2000
).is_ok()).to_be(true)
stopped.pending_document_commit_url = "https://late.test/"
expect(stopped.begin_stop(2000).is_ok()).to_be(true)
val stop_command = browser_renderer_navigation_decode(
    browser_renderer_decoder_feed(
        browser_renderer_decoder_new(34), stopped.pending_wire
    ).message
)
expect(stop_command.action).to_equal("stop")
expect(stopped.navigation_permit.active).to_be(false)
expect(stopped.pending_document_commit_url).to_equal("")

var reload = HostedBrowserRendererProcess.create(35, 64, 48)
reload.state = "active"
reload.document_url = "https://reload.test/page"
expect(reload.begin_reload(2000).is_ok()).to_be(true)
expect(browser_renderer_navigation_decode(
    browser_renderer_decoder_feed(
        browser_renderer_decoder_new(35), reload.pending_wire
    ).message
).action).to_equal("reload")
expect(reload.pending_history_action).to_equal("replace")

var home = HostedBrowserRendererProcess.create(36, 64, 48)
home.state = "active"
expect(home.set_home_url(
    "https://home.test/"
)).to_be(true)
expect(home.begin_go_home(2000).is_ok()).to_be(true)
expect(browser_renderer_navigation_decode(
    browser_renderer_decoder_feed(
        browser_renderer_decoder_new(36), home.pending_wire
    ).message
).action).to_equal("home")

step("Route bookmark and page-link navigation without forged authority")
var bookmark = HostedBrowserRendererProcess.create(37, 64, 48)
bookmark.state = "active"
expect(bookmark.begin_bookmark_snapshot(
    BrowserBookmarkSnapshot.create([
        Pair(
            first: "https://saved.test/",
            second: "Saved"
        )
    ]), 2000
).is_ok()).to_be(true)
val bookmark_command = browser_renderer_bookmark_snapshot_decode(
    browser_renderer_decoder_feed(
        browser_renderer_decoder_new(37), bookmark.pending_wire
    ).message
)
expect(bookmark_command.ok).to_be(true)
expect(bookmark_command.urls[0]).to_equal("https://saved.test/")

var link = HostedBrowserRendererProcess.create(38, 64, 48)
link.document_url = "https://source.test/page"
link.document_origin = "https://source.test"
expect(link.authorize_renderer_navigation(
    BrowserRendererNetworkDecodeResult(
        ok: true, reason: "", reply_to_request_id: 1,
        request_id: "link-1", kind: "document",
        url: "https://destination.test/", method: "GET",
        headers: "", body: "", content_type: "",
        credentials: "include", script_cookie_writes: [],
        status: 0, error: ""
    )
)).to_be(true)
expect(link.navigation_permit.url).to_equal(
    "https://destination.test/"
)

step("Deny a late command from another renderer generation")
val wrong_generation = browser_renderer_navigation_encode(
    99, 1, "open", "https://late.test/", "GET", "", "", ""
)
val denied = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(38), wrong_generation.wire
)
expect(denied.status).to_equal("violation")
val teardown_press = registry.dispatch_chrome_pointer(
    26, 81, "back", true
)
expect(teardown_press.reason).to_equal("chrome-pressed")
expect(registry.pressed_window_id).to_equal(81)
expect(registry.close()).to_be(true)
expect(registry.pressed_window_id).to_equal(0)
```

</details>

#### should persist bounded page titles across renderer and profile restart

**Requirements:** `REQ-WEB-BROWSER-009`, `REQ-WEB-BROWSER-021`

- setup hosted bookmark title profile
   - Text capture: after_step
- fail
   - Text capture: after_step
- file hash sha256
   - Text capture: after_step
- fail
   - Text capture: after_step
- Open bounded titled documents through hosted chrome
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: admitted_title equals `BOOKMARK_TITLE_512`
- Err
   - Text capture: after_step
- fail
   - Text capture: after_step
- Ok
   - Text capture: after_step
- registry bookmark stored title
   - Text capture: after_step
- check bookmark title witness admission
   - Text capture: after_step
- registry bookmark stored title
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: second_commit.bookmarks.entries[1].second equals ``
- Commit bookmarks through the parent profile owner
   - Text capture: after_step
   - Evidence: text output verified by 2 expected checks
   - Expected: accepted_persisted_title equals `BOOKMARK_TITLE_512`
   - Expected: fallback_persisted_title equals ``
- profile close
   - Text capture: after_step
- BrowserProfileStore open
   - Text capture: after_step
- Restart the renderer generation and profile-backed window
   - Text capture: after_step
   - Evidence: text output verified by 3 expected checks
   - Expected: restarted_count equals `2`
   - Expected: restarted.profile_bookmarks.entries.len() equals `2`
   - Expected: restarted.profile_bookmarks.entries[1].second equals ``
- check restarted bookmark listing
   - Text capture: after_step
   - Evidence: restarted BrowserSession UI nodes resolved by canonical href, independent of bookmark order
   - Expected: accepted bookmark label equals `BOOKMARK_TITLE_512`
   - Expected: accepted bookmark href equals `https://accepted-title.test/`
   - Expected: fallback bookmark label equals `https://fallback-title.test/`
   - Expected: fallback bookmark href equals `https://fallback-title.test/`
- check in process registry profile reopen
   - Text capture: after_step
   - Evidence: bookmark mutations, canonical remove/re-add, and restart use HostedWebContentRegistry public actions with URL-keyed comparison
   - Expected: remove leaves `1` bookmark
   - Expected: re-add restores `2` bookmarks
   - Expected: both canonical URLs occur exactly once with their safe labels
- List persisted bookmarks with safe titles
   - Text capture: after_step
   - Evidence: canonical URL lookup verified by 4 expected checks
   - Expected: each canonical URL occurs exactly once
   - Expected: restored_title equals `BOOKMARK_TITLE_512`
   - Expected: restored_fallback equals ``
- set mock registry
   - Text capture: after_step
- remove bookmark title profile
   - Text capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 124 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
setup_hosted_bookmark_title_profile()
val artifact = env_get("HOSTED_WM_ARTIFACT")
val expected_artifact_sha = env_get("HOSTED_WM_ARTIFACT_SHA256")
if artifact == "":
    fail("HOSTED_WM_ARTIFACT must name the hosted_entry native binary")
if expected_artifact_sha.len() != 64 or
    file_hash_sha256(artifact) != expected_artifact_sha:
    fail("HOSTED_WM_ARTIFACT does not match its admitted SHA-256")
var registry = HostedBrowserRendererRegistry.create(
    artifact, "https://accepted-title.test/"
)
val body_html = "<main>bookmark title witness</main>"
expect(registry.ensure(
    93, body_html, 64, 48, 0, 100000
)).to_equal("none")
expect(_await_browser_registry_ready(
    registry, 93, body_html
)).to_be(true)
_open_hosted_bookmark_document(
    registry, 93, "https://accepted-title.test/", 100, body_html
)
expect(registry.bookmark_stored_title(93)).to_equal(
    BOOKMARK_TITLE_512
)
check_bookmark_title_witness_admission(
    registry, 93, BOOKMARK_TITLE_512
)
val admitted_title = registry.bookmark_stored_title(93)
step("Open bounded titled documents through hosted chrome")
expect(admitted_title).to_equal(BOOKMARK_TITLE_512)

var profile = match BrowserProfileStore.open(
    BOOKMARK_TITLE_PROFILE_PATH
):
    Err(error):
        fail(error.message())
    Ok(opened):
        opened
val _ = registry.dispatch_chrome_pointer(
    110, 93, "favorite", true
)
expect(registry.dispatch_chrome_pointer(
    111, 93, "favorite", false
).reason).to_equal("favorite-parent")
val first_commit = hosted_browser_parent_toggle_bookmark(
    profile,
    "https://accepted-title.test/",
    registry.bookmark_stored_title(93)
)
expect(first_commit.ok).to_be(true)
expect(first_commit.enabled).to_be(true)
expect(first_commit.bookmarks.entries[0].second).to_equal(
    BOOKMARK_TITLE_512
)
profile = first_commit.profile
_open_hosted_bookmark_document(
    registry, 93, "https://fallback-title.test/", 120, body_html
)
check_bookmark_title_witness_admission(registry, 93, "")
val _ = registry.dispatch_chrome_pointer(
    130, 93, "favorite", true
)
expect(registry.dispatch_chrome_pointer(
    131, 93, "favorite", false
).reason).to_equal("favorite-parent")
val second_commit = hosted_browser_parent_toggle_bookmark(
    profile,
    "https://fallback-title.test/",
    registry.bookmark_stored_title(93)
)
expect(second_commit.ok).to_be(true)
expect(second_commit.enabled).to_be(true)
expect(second_commit.bookmarks.entries[1].second).to_equal("")
profile = second_commit.profile
val accepted_persisted_title = (
    first_commit.bookmarks.entries[0].second
)
val fallback_persisted_title = (
    second_commit.bookmarks.entries[1].second
)
step("Commit bookmarks through the parent profile owner")
expect(accepted_persisted_title).to_equal(BOOKMARK_TITLE_512)
expect(fallback_persisted_title).to_equal("")

expect(registry.next_generation).to_be_greater_than(2)
expect(registry.close()).to_be(true)
profile.close()?
var restarted = HostedWebContentRegistry.create_with_bookmark_store(
    BrowserBookmarkStore.from_profile(
        BrowserProfileStore.open(BOOKMARK_TITLE_PROFILE_PATH)?
    )
)
val _ = restarted.advance_window(
    94, "<main>restarted</main>", 64, 48, 100000, true
)
val restarted_count = restarted.profile_bookmarks.entries.len()
step("Restart the renderer generation and profile-backed window")
expect(registry.next_generation).to_be_greater_than(2)
expect(restarted_count).to_equal(2)

expect(restarted.profile_bookmarks.entries.len()).to_equal(2)
check_restarted_bookmark_listing(restarted)
check_in_process_registry_profile_reopen(
    restarted.profile_bookmarks
)
var restored_title = ""
var restored_fallback = ""
var restored_accepted_count = 0
var restored_fallback_count = 0
for entry in restarted.profile_bookmarks.entries:
    if entry.first == "https://accepted-title.test/":
        restored_accepted_count = restored_accepted_count + 1
        restored_title = entry.second
    elif entry.first == "https://fallback-title.test/":
        restored_fallback_count = restored_fallback_count + 1
        restored_fallback = entry.second
step("List persisted bookmarks with safe titles")
expect(restored_accepted_count).to_equal(1)
expect(restored_fallback_count).to_equal(1)
expect(restored_title).to_equal(BOOKMARK_TITLE_512)
expect(restored_fallback).to_equal("")
expect(restarted.close()).to_be(true)
set_mock_registry(MockResponseRegistry.create())
_remove_bookmark_title_profile(BOOKMARK_TITLE_PROFILE_PATH)
```

</details>

#### should enforce one UTF-8 byte bound for every browser address editor

-  production browser fixture
   - Protocol capture: after_step
- fail
   - Protocol capture: after_step
- file hash sha256
   - Protocol capture: after_step
- fail
   - Protocol capture: after_step
- Accept an address draft of exactly 2048 UTF-8 bytes
   - Protocol capture: after_step
   - Evidence: protocol response verified by 5 expected checks
   - Expected: focused.reason equals `chrome-pressed`
   - Expected: released.reason equals `address-focused`
   - Expected: accepted.callback_count equals `1`
   - Expected: accepted.reason equals ``
   - Expected: registry.address_text(92) equals `exact`
- Reject a 2049-byte multibyte draft without mutating state
   - Protocol capture: after_step
   - Evidence: protocol response verified by 4 expected checks
   - Expected: rejected.callback_count equals `0`
   - Expected: rejected.reason equals `address-too-long`
   - Expected: registry.address_text(92) equals `exact`
   - Expected: registry.document_url(92) equals `committed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_production_browser_fixture()
val artifact = env_get("HOSTED_WM_ARTIFACT")
val expected_artifact_sha = env_get("HOSTED_WM_ARTIFACT_SHA256")
if artifact == "":
    fail("HOSTED_WM_ARTIFACT must name the hosted_entry native binary")
if expected_artifact_sha.len() != 64 or
    file_hash_sha256(artifact) != expected_artifact_sha:
    fail("HOSTED_WM_ARTIFACT does not match its admitted SHA-256")
var registry = HostedBrowserRendererRegistry.create(
    artifact, "https://example.com/"
)
expect(registry.ensure(
    92, "<div>secondary</div>", 64, 48, 0, 100000
)).to_equal("none")

step("Accept an address draft of exactly 2048 UTF-8 bytes")
val focused = registry.dispatch_chrome_pointer(
    1, 92, "address", true
)
val released = registry.dispatch_chrome_pointer(
    2, 92, "address", false
)
val exact = _repeat_browser_text("a", 2048)
val accepted = registry.dispatch_text(3, 92, exact)
expect(focused.reason).to_equal("chrome-pressed")
expect(released.reason).to_equal("address-focused")
expect(accepted.callback_count).to_equal(1)
expect(accepted.reason).to_equal("")
expect(registry.address_text(92)).to_equal(exact)
val committed = registry.document_url(92)

step("Reject a 2049-byte multibyte draft without mutating state")
val _ = registry.dispatch_chrome_pointer(
    4, 92, "address", true
)
val _ = registry.dispatch_chrome_pointer(
    5, 92, "address", false
)
val oversized = _repeat_browser_text("a", 2047) + "é"
val rejected = registry.dispatch_text(6, 92, oversized)
expect(rejected.semantic_target_id).to_equal(
    "browser:parent#address"
)
expect(rejected.callback_count).to_equal(0)
expect(rejected.reason).to_equal("address-too-long")
expect(registry.address_text(92)).to_equal(exact)
expect(registry.document_url(92)).to_equal(committed)
expect(registry.close()).to_be(true)
```

</details>

<details>
<summary>Advanced: should report unsupported content without fake success</summary>

#### should report unsupported content without fake success

-  production browser fixture
- Open unsupported and malformed compatibility fixtures
-  require production browser evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_production_browser_fixture()
step("Open unsupported and malformed compatibility fixtures")
_require_production_browser_evidence()
```

</details>


</details>

#### should render br as one forced inline line break

- Render forced HTML line breaks through canonical Draw IR
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 2 expected checks
   - Expected: beta_y - alpha_y equals `20`
   - Expected: hidden_beta_y equals `hidden_alpha_y`
- Read back the forced-line pixels after semantic geometry
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 2 expected checks
   - Expected: forced_pixels.len() equals `160 * 64`
   - Expected: _pixels_equal(forced_pixels, inline_pixels) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 65 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render forced HTML line breaks through canonical Draw IR")
val html = (
    "<div style='margin:0;padding:0;font-size:16px;line-height:20px'>" +
    "<span id='alpha'>alpha</span><br id='break'>" +
    "<span id='beta'>beta</span></div>"
)
val commands = simple_web_layout_render_html_draw_ir_with_images(
    html, 160, 64, []
).batches[0].commands
val alpha_index = _browser_draw_ir_text_index(commands, "alpha")
val beta_index = _browser_draw_ir_text_index(commands, "beta")
expect(alpha_index).to_be_greater_than(-1)
expect(beta_index).to_be_greater_than(alpha_index)
val alpha = commands[alpha_index]
val beta = commands[beta_index]
expect(_browser_draw_ir_style_value(
    alpha, "display"
)).to_equal("inline")
expect(_browser_draw_ir_style_value(
    beta, "line-height"
)).to_equal("20")
expect(simple_web_layout_debug_style_by_id(
    html, "break", "display"
)).to_equal("inline")
expect(simple_web_layout_debug_layout_by_id(
    html, 160, 64, "break", "w"
)).to_equal("0")
expect(simple_web_layout_debug_layout_by_id(
    html, 160, 64, "break", "h"
)).to_equal("20")
expect(simple_web_layout_debug_layout_by_id(
    html, 160, 64, "beta", "x"
)).to_equal(simple_web_layout_debug_layout_by_id(
    html, 160, 64, "alpha", "x"
))
val alpha_y = simple_web_layout_debug_layout_by_id(
    html, 160, 64, "alpha", "y"
).to_i32()
val beta_y = simple_web_layout_debug_layout_by_id(
    html, 160, 64, "beta", "y"
).to_i32()
expect(beta_y - alpha_y).to_equal(20)
val hidden_break_html = (
    "<div style='margin:0;padding:0;font-size:16px;line-height:20px'>" +
    "<span id='hidden-alpha'>alpha</span>" +
    "<br style='display:none'>" +
    "<span id='hidden-beta'>beta</span></div>"
)
val hidden_alpha_y = simple_web_layout_debug_layout_by_id(
    hidden_break_html, 160, 64, "hidden-alpha", "y"
).to_i32()
val hidden_beta_y = simple_web_layout_debug_layout_by_id(
    hidden_break_html, 160, 64, "hidden-beta", "y"
).to_i32()
expect(hidden_beta_y).to_equal(hidden_alpha_y)

step("Read back the forced-line pixels after semantic geometry")
val renderer = BrowserRenderer.create(160, 64)
val forced_pixels = renderer.render_html_to_pixels(html).pixel_data
val inline_pixels = renderer.render_html_to_pixels(
    "<div style='margin:0;padding:0;font-size:16px;" +
    "line-height:20px'>alpha beta</div>"
).pixel_data
expect(forced_pixels.len()).to_equal(160 * 64)
expect(_pixels_equal(forced_pixels, inline_pixels)).to_equal(false)
```

</details>

#### should retain the canonical document tree while rendering its body

- Load one explicit head and body through the canonical tree builder
   - GUI capture: after_step (HTML preferred when available)
- var session = BrowserSession new
   - GUI capture: after_step (HTML preferred when available)
- Ok
   - GUI capture: after_step (HTML preferred when available)
-
   - GUI capture: after_step (HTML preferred when available)
- Err
   - GUI capture: after_step (HTML preferred when available)
- fail
   - GUI capture: after_step (HTML preferred when available)
- Retain head metadata and title in the installed semantic document
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 4 expected checks
   - Expected: heads.len() equals `1`
   - Expected: be_dom_find_by_tag(heads[0], "meta").len() equals `1`
   - Expected: be_dom_find_by_tag(heads[0], "title").len() equals `1`
   - Expected: session.current_title equals `Canonical Tree`
- Lower the same body through canonical Draw IR
   - GUI capture: after_step (HTML preferred when available)
- session render html document
   - GUI capture: after_step (HTML preferred when available)
- Execute the same composition through Engine2D pixels
   - GUI capture: after_step (HTML preferred when available)
- raster shutdown
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 1 expected check
   - Expected: rendered.pixels.len() equals `32 * 32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Load one explicit head and body through the canonical tree builder")
var session = BrowserSession.new()
match session.open_html(
    "https://example.test/canonical-tree",
    "<!DOCTYPE html><html><head>" +
    "<meta name='fixture' content='whatwg-tree'>" +
    "<title>Canonical Tree</title></head>" +
    "<body style='margin:0'><div id='canonical-tree-visible' " +
    "style='width:24px;height:24px;background-color:#00ff00'>" +
    "tree-visible</div></body></html>"
):
    Ok(_):
        ()
    Err(reason):
        fail("canonical tree fixture failed to open: {reason}")

step("Retain head metadata and title in the installed semantic document")
val heads = be_dom_find_by_tag(session.current_dom, "head")
expect(heads.len()).to_equal(1)
expect(be_dom_find_by_tag(heads[0], "meta").len()).to_equal(1)
expect(be_dom_find_by_tag(heads[0], "title").len()).to_equal(1)
expect(session.current_title).to_equal("Canonical Tree")

step("Lower the same body through canonical Draw IR")
val composition = simple_web_layout_render_html_draw_ir_with_images(
    session.render_html_document(), 32, 32, session.image_resources
)
expect(_browser_draw_ir_text_index(
    composition.batches[0].commands, "tree-visible"
)).to_be_greater_than(-1)

step("Execute the same composition through Engine2D pixels")
val raster = Engine2dCompositorBackend.create_named(
    32, 32, "software"
)
val rendered = raster.render_draw_ir_composition(composition, [])
raster.shutdown()
expect(rendered.pixels.len()).to_equal(32 * 32)
expect(_count_color(
    rendered.pixels, 0xFF00FF00u32
)).to_be_greater_than(0)
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

- **Requirements:** `doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md`
- **Plan:** `doc/03_plan/sys_test/simple_web_browser_engine_production_hardening.md`
- **Design:** `doc/05_design/simple_web_browser_engine_production_hardening.md`
- **Research:** `doc/01_research/local/simple_web_browser_engine_production_hardening.md`


</details>
