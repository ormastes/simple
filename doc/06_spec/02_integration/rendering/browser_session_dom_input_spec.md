# Browser Session Dom Input Specification

> Tests covering BrowserSession live DOM input.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Dom Input Specification

## Scenarios

### BrowserSession live DOM input

#### should parse mixed-case document tags through layout Draw IR and pixels

- Open a document with uppercase structural and visible tags
   - HTML capture: after_step
- var session = BrowserSession new
   - HTML capture: after_step
   - Evidence: HTML text verified by 4 expected checks
   - Expected: session.current_title equals `Case İ`
   - Expected: paragraphs.len() equals `1`
   - Expected: paragraph_id equals `case`
   - Expected: paragraph_text equals `Visible İ`
- Inspect the canonical web semantic style and layout box
   - HTML capture: after_step
   - Evidence: HTML text verified by 3 expected checks
   - Expected: display equals `block`
   - Expected: layout_width equals `24`
   - Expected: layout_height equals `16`
- Require matching final Draw IR and visible pixels
   - HTML capture: after_step
   - Evidence: HTML text verified by 3 expected checks
   - Expected: box_found is true
   - Expected: text_found is true
   - Expected: tag equals `p`
- "{opened}|{session current title}|{paragraphs len
   - HTML capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 73 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Open a document with uppercase structural and visible tags")
var session = BrowserSession.new()
val opened = session.open_html(
    "https://example.test/mixed-case",
    "<HTML><HEAD><TITLE>Case İ</TITLE></HEAD><BODY>" +
    "<P id='case' style='display:block;width:24px;height:16px;" +
    "background-color:#2563eb'>Visible İ</P></BODY></HTML>"
).is_ok()
expect(session.current_title).to_equal("Case İ")
val paragraphs = be_dom_find_by_tag(session.dom_root(), "p")
expect(paragraphs.len()).to_equal(1)
val paragraph_id = be_dom_get_attr(paragraphs[0], "id")
val paragraph_text = be_dom_get_text_content(paragraphs[0])
expect(paragraph_id).to_equal("case")
expect(paragraph_text).to_equal("Visible İ")

step("Inspect the canonical web semantic style and layout box")
val rendered = session.render_html_document()
val display = simple_web_layout_debug_style_by_id(
    rendered, "case", "display"
)
expect(display).to_equal("block")
val layout_width = simple_web_layout_debug_layout_by_id(
    rendered, 64, 48, "case", "w"
)
expect(layout_width).to_equal("24")
val layout_height = simple_web_layout_debug_layout_by_id(
    rendered, 64, 48, "case", "h"
)
expect(layout_height).to_equal("16")

step("Require matching final Draw IR and visible pixels")
val composition = WebRenderBackend.create(
    "pure_simple", 64, 48
).render_html_to_draw_ir(rendered)
var box_found = false
var box_geometry_ok = true
var text_found = false
var sources_ok = true
var tag = ""
for batch in composition.batches:
    if batch.source.source_kind != "html_ast":
        sources_ok = false
    for command in batch.commands:
        if command.component_id == "case":
            box_found = true
            if command.width != 24 or command.height != 16:
                box_geometry_ok = false
            for property in command.computed_style:
                if property.key == "tag":
                    tag = property.value
        if (
            command.kind == "text" and
            command.text_value == "Visible İ" and
            command.parent_id == "case"
        ):
            text_found = true
expect(box_found).to_equal(true)
expect(text_found).to_equal(true)
expect(tag).to_equal("p")
val pixels = session.render_to_pixels(64, 48).pixel_data
val visible_pixels = _count_dom_input_color(
    pixels, 0xFF2563EBu32
)
expect(
    "{opened}|{session.current_title}|{paragraphs.len()}|" +
    "{paragraph_id}|{paragraph_text}|{display}|" +
    "{layout_width}|{layout_height}|{sources_ok}|{box_found}|" +
    "{box_geometry_ok}|{text_found}|{tag}|{visible_pixels > 0}"
).to_equal(
    "true|Case İ|1|case|Visible İ|block|24|16|" +
    "true|true|true|true|p|true"
)
```

</details>

#### runs an inline click handler and renders the checkbox default state

- var session = BrowserSession new
   - Expected: opened.is_ok() is true
   - Expected: dispatch.default_action equals `input-checkbox-toggle`
   - Expected: dispatch.default_action_allowed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val opened = session.open_html(
    "https://example.test/form",
    "<html><head><style>input { display:block; width:32px; height:24px; background-color:#ef4444; } input[checked] { background-color:#2563eb; }</style></head><body><input id='accept' type='checkbox' onclick=\"document.title=document.body.innerHTML\" oninput=\"document.title=document.title+':input'\" onchange=\"document.title=document.title+':change'\"></body></html>"
)
expect(opened.is_ok()).to_equal(true)

val before = session.render_to_pixels(64, 48)
expect(_count_dom_input_color(before.pixel_data, 0xFFEF4444u32)).to_be_greater_than(0)

val dispatch = session.dispatch_dom_event("accept", "click", true, true)
expect(dispatch.default_action).to_equal("input-checkbox-toggle")
expect(dispatch.default_action_allowed).to_equal(true)
expect(session.current_title).to_contain("checked=\"checked\"")
expect(session.current_title).to_end_with(":input:change")
expect(session.current_body_html).to_contain("checked=\"checked\"")

val after = session.render_to_pixels(64, 48)
expect(_count_dom_input_color(after.pixel_data, 0xFF2563EBu32)).to_be_greater_than(0)
```

</details>

#### honors prevent-default before link navigation enters the request pump

- var session = BrowserSession new
   - Expected: dispatch.event.default_prevented is true
   - Expected: dispatch.default_action_allowed is false
   - Expected: session.current_url equals `https://example.test/start`
   - Expected: session.has_pending_requests() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.test/start",
    "<html><body><a id='blocked' href='/next' onclick='prevent-default'>Next</a></body></html>"
)

val dispatch = session.dispatch_dom_event("blocked", "click", true, true)

expect(dispatch.event.default_prevented).to_equal(true)
expect(dispatch.default_action_allowed).to_equal(false)
expect(session.current_url).to_equal("https://example.test/start")
expect(session.has_pending_requests()).to_equal(false)
```

</details>

#### rolls back canceled checkbox pre-activation

- var session = BrowserSession new
   - Expected: dispatch.event.default_prevented is true
   - Expected: session.current_body_html does not contain `checked=`
   - Expected: session.current_title equals `Initial`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.test/form",
    "<html><head><title>Initial</title></head><body><input id='accept' type='checkbox' onclick='prevent-default' oninput=\"document.title='input'\" onchange=\"document.title='change'\"></body></html>"
)

val dispatch = session.dispatch_dom_event(
    "accept", "click", true, true
)

expect(dispatch.event.default_prevented).to_equal(true)
expect(session.current_body_html.contains("checked=")).to_equal(false)
expect(session.current_title).to_equal("Initial")
```

</details>

#### routes an uncanceled link default through session navigation

- var session = BrowserSession new
   - Expected: dispatch.default_action_allowed is true
- Some
   - Expected: request.kind equals `document`
   - Expected: request.url equals `https://example.test/next`
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.test/start",
    "<html><body><a id='next' href='/next'>Next</a></body></html>"
)

val dispatch = session.dispatch_dom_event("next", "click", true, true)

expect(dispatch.default_action_allowed).to_equal(true)
match session.take_pending_request():
    Some(request):
        expect(request.kind).to_equal("document")
        expect(request.url).to_equal("https://example.test/next")
    nil:
        fail("Expected uncanceled link navigation request")
```

</details>

#### dispatches controls without author-supplied ids by stable node identity

- var session = BrowserSession new
   - Expected: buttons.len() equals `1`
- be dom event identity
   - Expected: dispatch.default_action equals `button-activate`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.test/controls",
    "<html><body><button>Save</button></body></html>"
)
val buttons = be_dom_find_by_tag(session.dom_root(), "button")
expect(buttons.len()).to_equal(1)

val dispatch = session.dispatch_dom_event(
    be_dom_event_identity(buttons[0]), "click", true, true
)

expect(dispatch.default_action).to_equal("button-activate")
expect(session.current_body_html).to_contain("data-activated=\"true\"")
```

</details>

#### dispatches submit and honors preventDefault on the owning form

- var session = BrowserSession new
   - Expected: dispatch.default_action_allowed is true
   - Expected: session.has_pending_requests() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.test/form",
    "<html><body><form id='profile' onsubmit='prevent-default'><button id='save'>Save</button></form></body></html>"
)

val dispatch = session.dispatch_dom_event("save", "click", true, true)

expect(dispatch.default_action_allowed).to_equal(true)
expect(session.current_body_html).to_contain("data-activated=\"true\"")
expect(session.current_body_html.contains(
    "data-submitted=\"true\""
)).to_equal(false)
expect(session.has_pending_requests()).to_equal(false)
```

</details>

#### dispatches submit but blocks form navigation under header sandbox

- var session = BrowserSession new
- Some
- fail
   - Expected: dispatch.default_action equals `button-activate`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
expect(session.begin_network_navigation(
    "https://example.test/form", "GET", "", "", ""
).is_ok()).to_be(true)
match session.take_pending_request():
    Some(request):
        expect(session.commit_network_response(BrowserResponse.create(
            request_id: request.id,
            kind: request.kind,
            url: request.url,
            status: 200,
            headers: (
                "Content-Security-Policy: sandbox allow-scripts;" +
                " script-src 'unsafe-inline'"
            ),
            body: (
                "<html><body><form id='profile' action='/save'" +
                " method='post'><input name='name' value='Ada'>" +
                "<button id='save'>Save</button></form></body></html>"
            ),
            error: ""
        )).is_ok()).to_be(true)
    nil:
        fail("Expected sandbox form document request")

val dispatch = session.dispatch_dom_event(
    "save", "click", true, true
)
expect(dispatch.default_action).to_equal("button-activate")
expect(session.has_pending_requests()).to_be(false)
expect(session.warnings.join("|")).to_contain(
    "CSP sandbox blocked form submission"
)
```

</details>

#### submits a button with an invalid type as the default submitter

- var session = BrowserSession new
- session dom root
   - Expected: dispatch.default_action equals `button-activate`
- Some
   - Expected: request.method equals `POST`
   - Expected: request.url equals `https://example.test/save`
   - Expected: request.body equals `name=Ada`
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.test/form",
    "<html><body><form id='profile' action='/save' method='post'><input name='name' value='Ada'><button id='save' type='wat'>Save</button></form></body></html>"
)

expect(be_dom_default_submitter_id(
    session.dom_root(), "profile"
)).to_equal("save")
val dispatch = session.dispatch_dom_event(
    "save", "click", true, true
)

expect(dispatch.default_action).to_equal("button-activate")
match session.take_pending_request():
    Some(request):
        expect(request.method).to_equal("POST")
        expect(request.url).to_equal("https://example.test/save")
        expect(request.body).to_equal("name=Ada")
    nil:
        fail("Expected invalid button type to submit its form")
```

</details>

#### does not submit an invalid button type when click is canceled

- var session = BrowserSession new
   - Expected: dispatch.default_action_allowed is false
   - Expected: session.has_pending_requests() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.test/form",
    "<html><body><form action='/save' method='post'><button id='save' type='wat' onclick='prevent-default'>Save</button></form></body></html>"
)

val dispatch = session.dispatch_dom_event(
    "save", "click", true, true
)

expect(dispatch.default_action_allowed).to_equal(false)
expect(session.has_pending_requests()).to_equal(false)
```

</details>

#### does not submit an explicit button control

- var session = BrowserSession new
   - Expected: dispatch.default_action equals `button-activate`
   - Expected: session.has_pending_requests() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.test/form",
    "<html><body><form action='/save' method='post'><button id='save' type='button'>Save</button></form></body></html>"
)

val dispatch = session.dispatch_dom_event(
    "save", "click", true, true
)

expect(dispatch.default_action).to_equal("button-activate")
expect(session.has_pending_requests()).to_equal(false)
```

</details>

#### resets nested controls to parsed defaults unless reset is canceled

- var session = BrowserSession new
   - Expected: session.set_dom_text_input("name", "changed").is_ok() is true
   - Expected: session.set_dom_text_input("notes", "changed").is_ok() is true
   - Expected: session.set_dom_select_value("choice", "two").is_ok() is true
   - Expected: reset.default_action equals `form-reset`
   - Expected: be_dom_get_attr(name[name.len() - 1], "value") equals `seed`
   - Expected: be_dom_get_text_content(notes[notes.len() - 1]) equals `memo`
   - Expected: be_dom_has_attr(flag[flag.len() - 1], "checked") is true
   - Expected: be_dom_has_attr(one[one.len() - 1], "selected") is true
   - Expected: be_dom_has_attr(two[two.len() - 1], "selected") is false
- profile[profile len
- session clear dom focus
- initial, session render to pixels
   - Expected: session.set_dom_text_input("kept", "changed").is_ok() is true
- session clear dom focus
   - Expected: prevented.default_action equals `form-reset`
- kept[kept len
- session clear dom focus
- session render to pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 59 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.test/reset",
    "<html><head><style>input,textarea,select,button{display:block;width:96px;height:22px}input[checked]{background-color:#2563eb}</style></head><body><form id='profile' onreset='set-attr:data-reset=yes'><div><input id='name' value='seed'><textarea id='notes'>memo</textarea><input id='flag' type='checkbox' checked><select id='choice'><option id='one' value='one' selected>One</option><option id='two' value='two'>Two</option></select><button id='restore' type='reset'>Reset</button></div></form><form id='blocked' onreset='prevent-default'><input id='kept' value='safe'><input id='blocked-reset' type='reset' value='Reset'></form></body></html>"
)
val initial = session.render_to_pixels(128, 180).pixel_data

expect(session.set_dom_text_input("name", "changed").is_ok()).to_equal(true)
expect(session.set_dom_text_input("notes", "changed").is_ok()).to_equal(true)
val _ = session.dispatch_dom_event("flag", "click", true, true)
expect(session.set_dom_select_value("choice", "two").is_ok()).to_equal(true)
val callbacks_before_reset = session.dom_callback_count
val reset = session.dispatch_dom_event(
    "restore", "click", true, true
)

expect(reset.default_action).to_equal("form-reset")
expect(session.dom_callback_count).to_equal(
    callbacks_before_reset + 1
)
val name = be_dom_find_path_to_id(session.dom_root(), "name")
val notes = be_dom_find_path_to_id(session.dom_root(), "notes")
val flag = be_dom_find_path_to_id(session.dom_root(), "flag")
val one = be_dom_find_path_to_id(session.dom_root(), "one")
val two = be_dom_find_path_to_id(session.dom_root(), "two")
val profile = be_dom_find_path_to_id(session.dom_root(), "profile")
expect(be_dom_get_attr(name[name.len() - 1], "value")).to_equal("seed")
expect(be_dom_get_text_content(notes[notes.len() - 1])).to_equal("memo")
expect(be_dom_has_attr(flag[flag.len() - 1], "checked")).to_equal(true)
expect(be_dom_has_attr(one[one.len() - 1], "selected")).to_equal(true)
expect(be_dom_has_attr(two[two.len() - 1], "selected")).to_equal(false)
expect(be_dom_get_attr(
    profile[profile.len() - 1], "data-reset"
)).to_equal("yes")
session.clear_dom_focus()
expect(_dom_input_pixels_equal(
    initial, session.render_to_pixels(128, 180).pixel_data
)).to_equal(true)

expect(session.set_dom_text_input("kept", "changed").is_ok()).to_equal(true)
session.clear_dom_focus()
val prevented_before = session.render_to_pixels(128, 180).pixel_data
val callbacks_before_prevented = session.dom_callback_count
val prevented = session.dispatch_dom_event(
    "blocked-reset", "click", true, true
)
expect(prevented.default_action).to_equal("form-reset")
expect(session.dom_callback_count).to_equal(
    callbacks_before_prevented + 1
)
val kept = be_dom_find_path_to_id(session.dom_root(), "kept")
expect(be_dom_get_attr(
    kept[kept.len() - 1], "value"
)).to_equal("changed")
session.clear_dom_focus()
expect(_dom_input_pixels_equal(
    prevented_before,
    session.render_to_pixels(128, 180).pixel_data
)).to_equal(true)
```

</details>

#### queues an uncanceled POST form with live DOM values

- var session = BrowserSession new
   - Expected: session.set_dom_text_input("name", "Ada & Bob").is_ok() is true
   - Expected: dispatch.default_action_allowed is true
- Some
   - Expected: request.kind equals `document`
   - Expected: request.method equals `POST`
   - Expected: request.url equals `https://example.test/save`
   - Expected: request.body equals `name=Ada+%26+Bob&commit=yes`
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.test/form",
    "<html><body><form id='profile' action='/save' method='post'><input id='name' name='name' value='old'><button id='save' name='commit' value='yes'>Save</button></form></body></html>"
)
expect(session.set_dom_text_input("name", "Ada & Bob").is_ok()).to_equal(true)

val dispatch = session.dispatch_dom_event("save", "click", true, true)

expect(dispatch.default_action_allowed).to_equal(true)
match session.take_pending_request():
    Some(request):
        expect(request.kind).to_equal("document")
        expect(request.method).to_equal("POST")
        expect(request.url).to_equal("https://example.test/save")
        expect(request.body).to_equal("name=Ada+%26+Bob&commit=yes")
        expect(request.content_type).to_equal(
            "application/x-www-form-urlencoded"
        )
    nil:
        fail("Expected form navigation request")
```

</details>

#### updates text input value and emits its inline input handler

- var session = BrowserSession new
   - Expected: updated.is_ok() is true
   - Expected: session.current_title equals `Typing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.test/input",
    "<html><body><input id='name' oninput=\"document.title='Typing'\"></body></html>"
)

val updated = session.set_dom_text_input("name", "Ada & Bob")

expect(updated.is_ok()).to_equal(true)
expect(session.current_title).to_equal("Typing")
expect(session.current_body_html).to_contain("value=\"Ada &amp; Bob\"")
```

</details>

#### dispatches focus before text input and keeps one focused control

- var session = BrowserSession new
   - Expected: session.set_dom_text_input("first", "Ada").is_ok() is true
   - Expected: session.current_title equals `Focused`
   - Expected: session.set_dom_text_input("first", "Ada Lovelace").is_ok() is true
   - Expected: session.dom_callback_count equals `callbacks_after_focus`
   - Expected: session.set_dom_text_input("second", "Bob").is_ok() is true
   - Expected: be_dom_get_attr(inputs[0], "data-focused") equals ``
   - Expected: be_dom_get_attr(inputs[1], "data-focused") equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.test/input",
    "<html><body><input id='first' onfocus=\"document.title='Focused'\"><input id='second'></body></html>"
)

expect(session.set_dom_text_input("first", "Ada").is_ok()).to_equal(true)
expect(session.current_title).to_equal("Focused")
val callbacks_after_focus = session.dom_callback_count
expect(session.set_dom_text_input("first", "Ada Lovelace").is_ok()).to_equal(true)
expect(session.dom_callback_count).to_equal(callbacks_after_focus)
expect(session.set_dom_text_input("second", "Bob").is_ok()).to_equal(true)
val inputs = be_dom_find_by_tag(session.dom_root(), "input")
expect(be_dom_get_attr(inputs[0], "data-focused")).to_equal("")
expect(be_dom_get_attr(inputs[1], "data-focused")).to_equal("true")
```

</details>

#### blurs the old control before focus mutates and paints the new state

- Open two controls whose focus transition mutates rendered CSS
- var session = BrowserSession new
- "<html><head><style>#stage{width:32px;height:24px;background-color:#ef4444} blurred{background-color:#f59e0b} focused{background-color:#2563eb}</style></head><body><div id='stage'></div><input id='first' onblur=\"document title=document title+'blur>';document getElementById
- Focus the first control, then move focus to the second
   - Expected: session.set_dom_text_input("first", "Ada").is_ok() is true
   - Expected: session.eval_script("document.title=''").is_ok() is true
   - Expected: session.set_dom_text_input("second", "Bob").is_ok() is true
- Require blur-before-focus state through DOM, Draw IR, and pixels
   - Expected: session.current_title equals `blur>focus>`
   - Expected: be_dom_get_attr(inputs[0], "data-focused") equals ``
   - Expected: be_dom_get_attr(inputs[1], "data-focused") equals `true`
   - Expected: stage_color equals `0xFF2563EBu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Open two controls whose focus transition mutates rendered CSS")
var session = BrowserSession.new()
expect(session.open_html(
    "https://example.test/focus-order",
    "<html><head><style>#stage{width:32px;height:24px;background-color:#ef4444}.blurred{background-color:#f59e0b}.focused{background-color:#2563eb}</style></head><body><div id='stage'></div><input id='first' onblur=\"document.title=document.title+'blur>';document.getElementById('stage').className='blurred'\"><input id='second' onfocus=\"document.title=document.title+'focus>';document.getElementById('stage').className='focused'\"></body></html>"
).is_ok()).to_equal(true)

step("Focus the first control, then move focus to the second")
expect(session.set_dom_text_input("first", "Ada").is_ok()).to_equal(true)
expect(session.eval_script("document.title=''").is_ok()).to_equal(true)
expect(session.set_dom_text_input("second", "Bob").is_ok()).to_equal(true)

step("Require blur-before-focus state through DOM, Draw IR, and pixels")
expect(session.current_title).to_equal("blur>focus>")
val inputs = be_dom_find_by_tag(session.dom_root(), "input")
expect(be_dom_get_attr(inputs[0], "data-focused")).to_equal("")
expect(be_dom_get_attr(inputs[1], "data-focused")).to_equal("true")
val rendered = session.render_html_document()
expect(rendered).to_contain("id=\"stage\" class=\"focused\"")
val composition = WebRenderBackend.create(
    "pure_simple", 64, 64
).render_html_to_draw_ir(rendered)
var stage_color = 0u32
for batch in composition.batches:
    for command in batch.commands:
        if command.component_id == "stage":
            stage_color = command.color
expect(stage_color).to_equal(0xFF2563EBu32)
val pixels = session.render_to_pixels(64, 64).pixel_data
expect(_count_dom_input_color(
    pixels, 0xFF2563EBu32
)).to_be_greater_than(0)
expect(_count_dom_input_color(
    pixels, 0xFFF59E0Bu32
)).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/browser_session_dom_input_spec.spl` |
| Updated | 2026-07-29 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering BrowserSession live DOM input.
- BrowserSession live DOM input

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
