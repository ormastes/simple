# browser_session_ui_access_controls_spec

> This spec exercises browser chrome and DOM controls through the canonical textual UI access surface, including bounded address input and rendered state.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# browser_session_ui_access_controls_spec

This spec exercises browser chrome and DOM controls through the canonical textual UI access surface, including bounded address input and rendered state.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/feature/simple_web_browser_production_hardening.md |
| Plan | doc/03_plan/sys_test/simple_web_browser_production_hardening.md |
| Design | doc/05_design/ui/web/simple_web_browser_production_hardening.md |
| Research | doc/01_research/local/simple_web_browser_production_hardening.md |
| Source | `test/03_system/app/browser/feature/browser_session_ui_access_controls_spec.spl` |
| Updated | 2026-07-30 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This spec exercises browser chrome and DOM controls through the canonical
textual UI access surface, including bounded address input and rendered state.

**Requirements:** doc/02_requirements/feature/simple_web_browser_production_hardening.md
**Plan:** doc/03_plan/sys_test/simple_web_browser_production_hardening.md
**Design:** doc/05_design/ui/web/simple_web_browser_production_hardening.md
**Research:** doc/01_research/local/simple_web_browser_production_hardening.md

## Examples

Each displayed scenario drives `BrowserSession.ui_access_act`, then asserts
semantic state and, where relevant, rendered pixels.

**TUI Captures:** build/test-artifacts/03_system/app/browser/feature/browser_session_ui_access_controls/browser_ui_access_snapshot.txt

## Evidence

Display policy: `embed_tui`

| Category | Count |
|----------|------:|
| TUI Captures | 1 |

### TUI Captures

| Item | Kind | Path |
|------|------|------|
| `browser_ui_access_snapshot.txt` | TUI capture | `build/test-artifacts/03_system/app/browser/feature/browser_session_ui_access_controls/browser_ui_access_snapshot.txt` |

## Scenarios

### BrowserSession primitive controls through textual UI access

#### exposes browser toolbar controls as queryable UI access nodes

- var session =  browser session fixture
   - Expected: snapshot.mode equals `browser_session`
   - Expected: snapshot.active_surface equals `browser:session`
   - Expected: ui_access_find_nodes(snapshot, "browser:session", "button", "Back", 1).len() equals `1`
   - Expected: ui_access_find_nodes(snapshot, "browser:session", "button", "Forward", 1).len() equals `1`
   - Expected: ui_access_find_nodes(snapshot, "browser:session", "button", "Stop", 1).len() equals `1`
   - Expected: ui_access_find_nodes(snapshot, "browser:session", "button", "Reload", 1).len() equals `1`
   - Expected: ui_access_find_nodes(snapshot, "browser:session", "button", "Home", 1).len() equals `1`
   - Expected: ui_access_find_nodes(snapshot, "browser:session", "button", "Favorite", 1).len() equals `1`
   - Expected: ui_access_find_nodes(snapshot, "browser:session", "textfield", "https://example.com/two", 1).len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = _browser_session_fixture()

val snapshot = session.ui_access_snapshot()
expect(snapshot.mode).to_equal("browser_session")
expect(snapshot.active_surface).to_equal("browser:session")
expect(ui_access_find_nodes(snapshot, "browser:session", "button", "Back", 1).len()).to_equal(1)
expect(ui_access_find_nodes(snapshot, "browser:session", "button", "Forward", 1).len()).to_equal(1)
expect(ui_access_find_nodes(snapshot, "browser:session", "button", "Stop", 1).len()).to_equal(1)
expect(ui_access_find_nodes(snapshot, "browser:session", "button", "Reload", 1).len()).to_equal(1)
expect(ui_access_find_nodes(snapshot, "browser:session", "button", "Home", 1).len()).to_equal(1)
expect(ui_access_find_nodes(snapshot, "browser:session", "button", "Favorite", 1).len()).to_equal(1)
expect(ui_access_find_nodes(snapshot, "browser:session", "textfield", "https://example.com/two", 1).len()).to_equal(1)
```

</details>

#### captures browser UI access visible state for the generated manual

- var session = BrowserSession new
- session open html
   - Expected: _write_ui_capture(capture) equals `0`
   - Expected: _capture_file_state(capture) equals `matched`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/start/index.html", "<html><head><title>Start</title></head><body><a href='../docs/page.html'>Read docs</a></body></html>")
val snapshot = session.ui_access_snapshot()
val capture = _snapshot_capture(snapshot)

expect(capture).to_contain("BrowserSession UI Access Snapshot")
expect(capture).to_contain("node: back kind=button text=Back")
expect(capture).to_contain("node: reload kind=button text=Reload")
expect(capture).to_contain("node: favorite kind=button text=Favorite")
expect(capture).to_contain("node: address kind=textfield text=https://example.com/start/index.html")
expect(capture).to_contain("node: link_0 kind=link text=Read docs")
expect(_write_ui_capture(capture)).to_equal(0)
expect(_capture_file_state(capture)).to_equal("matched")
```

</details>

#### routes textual UI access actions into BrowserSession primitive controls

- var session =  browser session fixture
   - Expected: back.ok is true
   - Expected: session.current_url equals `https://example.com/one`
   - Expected: forward.ok is true
   - Expected: session.current_url equals `https://example.com/two`
   - Expected: favorite.ok is true
   - Expected: session.is_favorite("https://example.com/two") is true
   - Expected: favorite_nodes.len() equals `1`
   - Expected: favorite_nodes[0].selected is true
   - Expected: unfavorite.ok is true
   - Expected: session.is_favorite("https://example.com/two") is false
- session ui access snapshot
   - Expected: stop_nodes.len() equals `1`
   - Expected: stop_nodes[0].enabled is true
   - Expected: stop.ok is true
   - Expected: session.can_stop_loading() is false
   - Expected: home.ok is true
   - Expected: session.current_url equals `https://example.com/home`
   - Expected: reload.ok is true
   - Expected: session.current_url equals `https://example.com/home`


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = _browser_session_fixture()

val back = session.ui_access_act(WinTextActionRequest(target_id: "browser:session#back", action: "click", text_value: "", x: 0, y: 0))
expect(back.ok).to_equal(true)
expect(session.current_url).to_equal("https://example.com/one")

val forward = session.ui_access_act(WinTextActionRequest(target_id: "browser:session#forward", action: "click", text_value: "", x: 0, y: 0))
expect(forward.ok).to_equal(true)
expect(session.current_url).to_equal("https://example.com/two")

val favorite = session.ui_access_act(WinTextActionRequest(target_id: "browser:session#favorite", action: "click", text_value: "", x: 0, y: 0))
expect(favorite.ok).to_equal(true)
expect(session.is_favorite("https://example.com/two")).to_equal(true)
val favorite_nodes = ui_access_find_nodes(session.ui_access_snapshot(), "browser:session", "button", "Favorite", 1)
expect(favorite_nodes.len()).to_equal(1)
expect(favorite_nodes[0].selected).to_equal(true)
val unfavorite = session.ui_access_act(WinTextActionRequest(target_id: "browser:session#favorite", action: "click", text_value: "", x: 0, y: 0))
expect(unfavorite.ok).to_equal(true)
expect(session.is_favorite("https://example.com/two")).to_equal(false)

session.open_html(
    "https://example.com/pending",
    "<html><head><link rel='stylesheet' href='/slow.css'></head><body>Visible</body></html>"
)
val stop_nodes = ui_access_find_nodes(
    session.ui_access_snapshot(), "browser:session", "button", "Stop", 1
)
expect(stop_nodes.len()).to_equal(1)
expect(stop_nodes[0].enabled).to_equal(true)
val stop = session.ui_access_act(WinTextActionRequest(target_id: "browser:session#stop", action: "click", text_value: "", x: 0, y: 0))
expect(stop.ok).to_equal(true)
expect(session.can_stop_loading()).to_equal(false)
expect(session.current_body_html).to_contain("Visible")

val home = session.ui_access_act(WinTextActionRequest(target_id: "browser:session#home", action: "click", text_value: "", x: 0, y: 0))
expect(home.ok).to_equal(true)
expect(session.current_url).to_equal("https://example.com/home")

val reload = session.ui_access_act(WinTextActionRequest(target_id: "browser:session#reload", action: "click", text_value: "", x: 0, y: 0))
expect(reload.ok).to_equal(true)
expect(session.current_url).to_equal("https://example.com/home")
```

</details>

#### edits and submits the address through textual UI access

- var session = BrowserSession new
- session register resource
- session open html
   - Expected: edit.ok is true
   - Expected: session.ui_access_snapshot().nodes[6].text_value equals `https://example.com/target`
   - Expected: session.current_url equals `https://example.com/start`
   - Expected: submit.ok is true
   - Expected: session.current_url equals `https://example.com/target`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource("https://example.com/target", "<html><head><title>Target</title></head><body>Target</body></html>")
session.open_html("https://example.com/start", "<html><head><title>Start</title></head><body>Start</body></html>")

val edit = session.ui_access_act(WinTextActionRequest(target_id: "browser:session#address", action: "set_value", text_value: "https://example.com/target", x: 0, y: 0))
expect(edit.ok).to_equal(true)
expect(session.ui_access_snapshot().nodes[6].text_value).to_equal("https://example.com/target")
expect(session.current_url).to_equal("https://example.com/start")

val submit = session.ui_access_act(WinTextActionRequest(target_id: "browser:session#address", action: "submit", text_value: "", x: 0, y: 0))
expect(submit.ok).to_equal(true)
expect(session.current_url).to_equal("https://example.com/target")
```

</details>

#### bounds UTF-8 address input without partial state or pixel mutation

- var session = BrowserSession new
- Accept exactly 2048 UTF-8 bytes and project the draft accessibly
   - Expected: BROWSER_ADDRESS_MAX_BYTES equals `2048`
   - Expected: text_byte_len(exact_draft) equals `2048`
   - Expected: text_codepoint_len(exact_draft) equals `2046`
   - Expected: accepted.ok is true
- session ui access snapshot
   - Expected: address_nodes.len() equals `1`
- Reject 2049 bytes before trimming and preserve browser state
   - Expected: leading_overflow.code equals `address-too-long`
   - Expected: trailing_overflow.code equals `address-too-long`
   - Expected: session.address_draft equals `exact_draft`
   - Expected: session.current_url equals `https://example.com/start`
   - Expected: session.history.len() equals `history_before`
   - Expected: session.current_index equals `index_before`
   - Expected: session.pending_request_count() equals `pending_before`
   - Expected: session.ui_access_revision equals `revision_before`
- session render to pixels
- Reject newline control and NUL input before UI projection
   - Expected: leading_newline.code equals `address-invalid-control`
   - Expected: trailing_newline.code equals `address-invalid-control`
   - Expected: nul.code equals `address-invalid-control`
   - Expected: session.address_draft equals `exact_draft`
   - Expected: session.current_url equals `https://example.com/start`
   - Expected: session.pending_request_count() equals `pending_before`
- Submit an exact 2048-byte URL and render the committed page
   - Expected: text_byte_len(exact_url) equals `2048`
   - Expected: exact_submit.ok is true
   - Expected: session.current_url equals `exact_url`
- session render to pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 86 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/start",
    "<html><body style='background:#ff0000'>Start</body></html>"
)
val exact_draft = _repeat_ascii("a", 2045) + "한"
val initial_pixels = session.render_to_pixels(8, 8).pixels

step("Accept exactly 2048 UTF-8 bytes and project the draft accessibly")
expect(BROWSER_ADDRESS_MAX_BYTES).to_equal(2048)
expect(text_byte_len(exact_draft)).to_equal(2048)
expect(text_codepoint_len(exact_draft)).to_equal(2046)
val accepted = session.ui_access_act(WinTextActionRequest(
    target_id: "browser:session#address", action: "set_value",
    text_value: exact_draft, x: 0, y: 0
))
expect(accepted.ok).to_equal(true)
val address_nodes = ui_access_find_nodes(
    session.ui_access_snapshot(), "browser:session",
    "textfield", exact_draft, 1
)
expect(address_nodes.len()).to_equal(1)
expect(address_nodes[0].action_names).to_contain("submit")
val revision_before = session.ui_access_revision
val history_before = session.history.len()
val index_before = session.current_index
val pending_before = session.pending_request_count()

step("Reject 2049 bytes before trimming and preserve browser state")
val leading_overflow = session.ui_access_act(WinTextActionRequest(
    target_id: "browser:session#address", action: "submit",
    text_value: " " + exact_draft, x: 0, y: 0
))
val trailing_overflow = session.ui_access_act(WinTextActionRequest(
    target_id: "browser:session#address", action: "set_value",
    text_value: exact_draft + " ", x: 0, y: 0
))
expect(leading_overflow.code).to_equal("address-too-long")
expect(trailing_overflow.code).to_equal("address-too-long")
expect(session.address_draft).to_equal(exact_draft)
expect(session.current_url).to_equal("https://example.com/start")
expect(session.history.len()).to_equal(history_before)
expect(session.current_index).to_equal(index_before)
expect(session.pending_request_count()).to_equal(pending_before)
expect(session.ui_access_revision).to_equal(revision_before)
expect(_pixels_equal(
    session.render_to_pixels(8, 8).pixels, initial_pixels
)).to_equal(true)

step("Reject newline control and NUL input before UI projection")
val leading_newline = session.ui_access_act(WinTextActionRequest(
    target_id: "browser:session#address", action: "submit",
    text_value: "\nhttps://example.com/", x: 0, y: 0
))
val trailing_newline = session.ui_access_act(WinTextActionRequest(
    target_id: "browser:session#address", action: "set_value",
    text_value: "https://example.com/\n", x: 0, y: 0
))
val nul = session.ui_access_act(WinTextActionRequest(
    target_id: "browser:session#address", action: "set_value",
    text_value: "https://example.com/\0tail", x: 0, y: 0
))
expect(leading_newline.code).to_equal("address-invalid-control")
expect(trailing_newline.code).to_equal("address-invalid-control")
expect(nul.code).to_equal("address-invalid-control")
expect(session.address_draft).to_equal(exact_draft)
expect(session.current_url).to_equal("https://example.com/start")
expect(session.pending_request_count()).to_equal(pending_before)

step("Submit an exact 2048-byte URL and render the committed page")
val exact_url = "https://example.com/" + _repeat_ascii("a", 2028)
expect(text_byte_len(exact_url)).to_equal(2048)
session.register_resource(
    exact_url,
    "<html><body style='background:#00ff00'>Exact</body></html>"
)
val exact_submit = session.ui_access_act(WinTextActionRequest(
    target_id: "browser:session#address", action: "submit",
    text_value: exact_url, x: 0, y: 0
))
expect(exact_submit.ok).to_equal(true)
expect(session.current_url).to_equal(exact_url)
expect(session.current_body_html).to_contain("Exact")
expect(_pixels_equal(
    session.render_to_pixels(8, 8).pixels, initial_pixels
)).to_equal(false)
```

</details>

#### lists and opens a saved bookmark through textual UI access

- var session = BrowserSession new
- session add favorite
- session ui access snapshot
   - Expected: bookmarks.len() equals `1`
   - Expected: opened.ok is true
   - Expected: session.current_url equals `https://example.com/saved`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource(
    "https://example.com/saved",
    "<html><head><title>Saved</title></head><body>Saved page</body></html>"
)
session.open_html(
    "https://example.com/start", "<html><body>Start</body></html>"
)
session.add_favorite("https://example.com/saved", "Saved bookmark")

val bookmarks = ui_access_find_nodes(
    session.ui_access_snapshot(), "browser:session", "link", "Saved bookmark", 1
)
expect(bookmarks.len()).to_equal(1)
val opened = session.ui_access_act(WinTextActionRequest(
    target_id: bookmarks[0].canonical_id, action: "click",
    text_value: "", x: 0, y: 0
))

expect(opened.ok).to_equal(true)
expect(session.current_url).to_equal("https://example.com/saved")
expect(session.current_body_html).to_contain("Saved page")
```

</details>

#### rejects unsupported browser UI actions through the textual route

- var session = BrowserSession new
- session open html
   - Expected: result.ok is false
   - Expected: result.code equals `unsupported_operation`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("about:blank", "<html><body>Blank</body></html>")
val result = session.ui_access_act(WinTextActionRequest(target_id: "browser:session#home", action: "set_value", text_value: "x", x: 0, y: 0))
expect(result.ok).to_equal(false)
expect(result.code).to_equal("unsupported_operation")
```

</details>

#### exposes page anchors as actionable textual UI links

- var session = BrowserSession new
- session register resource
- session open html
   - Expected: links.len() equals `1`
   - Expected: _node_prop(links[0], "href") equals `https://example.com/docs/page.html`
   - Expected: result.ok is true
   - Expected: session.current_url equals `https://example.com/docs/page.html`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource("https://example.com/docs/page.html", "<html><head><title>Docs</title></head><body>Docs page</body></html>")
session.open_html("https://example.com/start/index.html", "<html><head><title>Start</title></head><body><a href='../docs/page.html'>Read docs</a></body></html>")

val links = ui_access_find_nodes(session.ui_access_snapshot(), "browser:session", "link", "Read docs", 1)
expect(links.len()).to_equal(1)
expect(_node_prop(links[0], "href")).to_equal("https://example.com/docs/page.html")

val result = session.ui_access_act(WinTextActionRequest(target_id: links[0].canonical_id, action: "click", text_value: "", x: 0, y: 0))
expect(result.ok).to_equal(true)
expect(session.current_url).to_equal("https://example.com/docs/page.html")
expect(session.current_body_html).to_contain("Docs page")
```

</details>

#### routes accessible link clicks through DOM cancellation

- var session = BrowserSession new
- session ui access snapshot
   - Expected: links.len() equals `1`
   - Expected: result.ok is true
   - Expected: result.message equals `link event canceled`
   - Expected: session.current_url equals `https://example.com/start`
   - Expected: session.has_pending_requests() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/start",
    "<html><body><a href='/blocked' onclick='prevent-default'>Blocked</a></body></html>"
)
val links = ui_access_find_nodes(
    session.ui_access_snapshot(), "browser:session", "link", "Blocked", 1
)
expect(links.len()).to_equal(1)

val result = session.ui_access_act(WinTextActionRequest(
    target_id: links[0].canonical_id, action: "click",
    text_value: "", x: 0, y: 0
))

expect(result.ok).to_equal(true)
expect(result.message).to_equal("link event canceled")
expect(session.current_url).to_equal("https://example.com/start")
expect(session.has_pending_requests()).to_equal(false)
```

</details>

#### edits and activates page controls through the DOM-backed UI surface

- var session = BrowserSession new
   - Expected: edited.ok is true
   - Expected: session.current_title equals `Typing`
   - Expected: canceled.ok is true
   - Expected: canceled.message equals `input edit canceled`
   - Expected: session.current_title equals `Changed`
   - Expected: session.current_body_html does not contain `value="blocked"`
   - Expected: focused_count equals `1`
   - Expected: blurred.ok is true
   - Expected: session.current_title equals `Changed`
   - Expected: focused_count equals `0`
   - Expected: clicked.ok is true
   - Expected: clicked.message equals `control key activated`
   - Expected: session.current_title equals `Saved`
   - Expected: blocked_key.ok is true
   - Expected: blocked_key.message equals `control key event canceled`
   - Expected: session.current_title equals `Saved`
   - Expected: checked.ok is true
- session ui access snapshot
   - Expected: checkboxes.len() equals `1`
   - Expected: checkboxes[0].selected is true
   - Expected: selected_radio.ok is true
- session ui access snapshot
   - Expected: radios.len() equals `2`
   - Expected: radios[0].selected is false
   - Expected: radios[1].selected is true
   - Expected: radios[1].focused is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 81 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/form",
    "<html><body><button onkeydown='set-attr:data-keydown=yes' onclick=\"document.title='Saved'\">Save</button><button onkeydown='prevent-default' onclick=\"document.title='ShouldNotRun'\">Blocked key</button><input value='old' oninput=\"document.title='Typing'\" onchange=\"document.title='Changed'\"><input value='kept' onbeforeinput='prevent-default' oninput=\"document.title='ShouldNotRun'\"><input type='checkbox'><input type='radio' name='choice' checked><input type='radio' name='choice'></body></html>"
)

val edited = session.ui_access_act(WinTextActionRequest(
    target_id: "browser:session#page_input_0", action: "set_value",
    text_value: "Ada", x: 0, y: 0
))
expect(edited.ok).to_equal(true)
expect(session.current_title).to_equal("Typing")
expect(session.current_body_html).to_contain("value=\"Ada\"")

val canceled = session.ui_access_act(WinTextActionRequest(
    target_id: "browser:session#page_input_1", action: "set_value",
    text_value: "blocked", x: 0, y: 0
))
expect(canceled.ok).to_equal(true)
expect(canceled.message).to_equal("input edit canceled")
expect(session.current_title).to_equal("Changed")
expect(session.current_body_html).to_contain("value=\"kept\"")
expect(session.current_body_html.contains("value=\"blocked\"")).to_equal(false)
var focused_count = 0
for node in session.ui_access_snapshot().nodes:
    if node.focused:
        focused_count = focused_count + 1
expect(focused_count).to_equal(1)

val blurred = session.ui_access_act(WinTextActionRequest(
    target_id: "browser:session#page_input_1", action: "blur",
    text_value: "", x: 0, y: 0
))
expect(blurred.ok).to_equal(true)
expect(session.current_title).to_equal("Changed")
focused_count = 0
for node in session.ui_access_snapshot().nodes:
    if node.focused:
        focused_count = focused_count + 1
expect(focused_count).to_equal(0)

val clicked = session.ui_access_act(WinTextActionRequest(
    target_id: "browser:session#page_button_0", action: "key",
    text_value: "Enter", x: 0, y: 0
))
expect(clicked.ok).to_equal(true)
expect(clicked.message).to_equal("control key activated")
expect(session.current_title).to_equal("Saved")
expect(session.current_body_html).to_contain("data-keydown=\"yes\"")

val blocked_key = session.ui_access_act(WinTextActionRequest(
    target_id: "browser:session#page_button_1", action: "key",
    text_value: "Enter", x: 0, y: 0
))
expect(blocked_key.ok).to_equal(true)
expect(blocked_key.message).to_equal("control key event canceled")
expect(session.current_title).to_equal("Saved")

val checked = session.ui_access_act(WinTextActionRequest(
    target_id: "browser:session#page_input_2", action: "click",
    text_value: "", x: 0, y: 0
))
expect(checked.ok).to_equal(true)
val checkboxes = ui_access_find_nodes(
    session.ui_access_snapshot(), "browser:session", "checkbox", "", 1
)
expect(checkboxes.len()).to_equal(1)
expect(checkboxes[0].selected).to_equal(true)

val selected_radio = session.ui_access_act(WinTextActionRequest(
    target_id: "browser:session#page_input_4", action: "key",
    text_value: "Space", x: 0, y: 0
))
expect(selected_radio.ok).to_equal(true)
val radios = ui_access_find_nodes(
    session.ui_access_snapshot(), "browser:session", "radio", "", 2
)
expect(radios.len()).to_equal(2)
expect(radios[0].selected).to_equal(false)
expect(radios[1].selected).to_equal(true)
expect(radios[1].focused).to_equal(true)
```

</details>

#### routes duplicate author IDs by exact DOM node identity

- var session = BrowserSession new
   - Expected: edited.ok is true
   - Expected: dom_inputs.len() equals `2`
   - Expected: be_dom_get_attr(dom_inputs[0], "data-routed") equals ``
   - Expected: be_dom_get_attr(dom_inputs[1], "data-routed") equals `right`
   - Expected: first_value equals `first`
   - Expected: second_value equals `changed`
   - Expected: first_focused is false
   - Expected: second_focused is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/form",
    "<html><body><input id='duplicate' value='first' oninput='set-attr:data-routed=wrong'><input id='duplicate' value='second' oninput='set-attr:data-routed=right'></body></html>"
)

val edited = session.ui_access_act(WinTextActionRequest(
    target_id: "browser:session#page_input_1", action: "set_value",
    text_value: "changed", x: 0, y: 0
))

expect(edited.ok).to_equal(true)
val dom_inputs = be_dom_find_by_tag(session.current_dom, "input")
expect(dom_inputs.len()).to_equal(2)
expect(be_dom_get_attr(dom_inputs[0], "data-routed")).to_equal("")
expect(be_dom_get_attr(dom_inputs[1], "data-routed")).to_equal("right")
var first_value = ""
var second_value = ""
var first_focused = false
var second_focused = false
for node in session.ui_access_snapshot().nodes:
    if node.widget_id == "page_input_0":
        first_value = node.text_value
        first_focused = node.focused
    elif node.widget_id == "page_input_1":
        second_value = node.text_value
        second_focused = node.focused
expect(first_value).to_equal("first")
expect(second_value).to_equal("changed")
expect(first_focused).to_equal(false)
expect(second_focused).to_equal(true)
```

</details>

#### changes the exact live select and rejects stale or disabled values

- var session = BrowserSession new
- session ui access snapshot
   - Expected: before.len() equals `3`
   - Expected: before[0].text_value equals `blue`
   - Expected: before[1].text_value equals `blue`
   - Expected: before[0].canonical_id == before[1].canonical_id is false
   - Expected: changed.ok is true
   - Expected: changed.message equals `selection updated`
   - Expected: callback_count equals `2`
- session ui access snapshot
   - Expected: after[0].text_value equals `blue`
   - Expected: after[1].text_value equals `red`
   - Expected: after[0].focused is false
   - Expected: after[1].focused is true
   - Expected: be_dom_get_attr(dom_selects[0], "data-input-route") equals ``
   - Expected: be_dom_get_attr(dom_selects[1], "data-input-route") equals `right`
   - Expected: be_dom_get_attr(dom_selects[1], "data-change-route") equals `right`
   - Expected: unchanged.ok is true
   - Expected: unchanged.message equals `selection unchanged`
   - Expected: session.dom_callback_count equals `callback_count`
   - Expected: disabled.ok is false
   - Expected: session.dom_callback_count equals `callback_count`
   - Expected: disabled_option.ok is false
   - Expected: session.dom_callback_count equals `callback_count`
   - Expected: missing.ok is false
   - Expected: session.dom_callback_count equals `callback_count`
   - Expected: disabled_select.ok is false
   - Expected: disabled_select.code equals `disabled`
   - Expected: stale.ok is false
   - Expected: stale.code equals `target_not_found`
- var focus session = BrowserSession new
- focus session ui access snapshot
   - Expected: focus_disabled.ok is false
   - Expected: focus_session.dom_callback_count equals `1`
   - Expected: be_dom_get_attr(live_select, "data-wrong") equals ``
- focus session ui access snapshot
   - Expected: focus_after[0].text_value equals `old`


<details>
<summary>Executable SSpec</summary>

Runnable source: 109 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/select",
    "<html><body><select id='duplicate'><option value='red'>Red</option><option value='blue' selected>Blue</option></select><select id='duplicate' oninput='set-attr:data-input-route=right' onchange='set-attr:data-change-route=right'><option value='red'>Red</option><option value='blue' selected>Blue</option><option value='black' disabled>Black</option><optgroup disabled><option value='green'>Green</option></optgroup></select><select disabled><option value='locked' selected>Locked</option></select></body></html>"
)

val before = ui_access_find_nodes(
    session.ui_access_snapshot(), "browser:session", "select", "", 3
)
expect(before.len()).to_equal(3)
expect(before[0].text_value).to_equal("blue")
expect(before[1].text_value).to_equal("blue")
expect(before[0].canonical_id == before[1].canonical_id).to_equal(false)

val changed = session.ui_access_act(WinTextActionRequest(
    target_id: before[1].canonical_id, action: "set_value",
    text_value: "red", x: 0, y: 0
))
expect(changed.ok).to_equal(true)
expect(changed.message).to_equal("selection updated")
val callback_count = session.dom_callback_count
expect(callback_count).to_equal(2)

val after = ui_access_find_nodes(
    session.ui_access_snapshot(), "browser:session", "select", "", 3
)
expect(after[0].text_value).to_equal("blue")
expect(after[1].text_value).to_equal("red")
expect(after[0].focused).to_equal(false)
expect(after[1].focused).to_equal(true)
val dom_selects = be_dom_find_by_tag(session.current_dom, "select")
expect(be_dom_get_attr(dom_selects[0], "data-input-route")).to_equal("")
expect(be_dom_get_attr(dom_selects[1], "data-input-route")).to_equal("right")
expect(be_dom_get_attr(dom_selects[1], "data-change-route")).to_equal("right")

val unchanged = session.ui_access_act(WinTextActionRequest(
    target_id: after[1].canonical_id, action: "set_value",
    text_value: "red", x: 0, y: 0
))
expect(unchanged.ok).to_equal(true)
expect(unchanged.message).to_equal("selection unchanged")
expect(session.dom_callback_count).to_equal(callback_count)

val disabled = session.ui_access_act(WinTextActionRequest(
    target_id: after[1].canonical_id, action: "set_value",
    text_value: "green", x: 0, y: 0
))
expect(disabled.ok).to_equal(false)
expect(session.dom_callback_count).to_equal(callback_count)

val disabled_option = session.ui_access_act(WinTextActionRequest(
    target_id: after[1].canonical_id, action: "set_value",
    text_value: "black", x: 0, y: 0
))
expect(disabled_option.ok).to_equal(false)
expect(session.dom_callback_count).to_equal(callback_count)

val missing = session.ui_access_act(WinTextActionRequest(
    target_id: after[1].canonical_id, action: "set_value",
    text_value: "missing", x: 0, y: 0
))
expect(missing.ok).to_equal(false)
expect(session.dom_callback_count).to_equal(callback_count)

val disabled_select = session.ui_access_act(WinTextActionRequest(
    target_id: after[2].canonical_id, action: "set_value",
    text_value: "locked", x: 0, y: 0
))
expect(disabled_select.ok).to_equal(false)
expect(disabled_select.code).to_equal("disabled")

val stale_target = after[1].canonical_id
session.open_html(
    "https://example.com/replaced",
    "<html><body><select><option value='new'>New</option></select></body></html>"
)
val stale = session.ui_access_act(WinTextActionRequest(
    target_id: stale_target, action: "set_value",
    text_value: "new", x: 0, y: 0
))
expect(stale.ok).to_equal(false)
expect(stale.code).to_equal("target_not_found")

var focus_session = BrowserSession.new()
focus_session.open_html(
    "https://example.com/focus-disable",
    "<html><body><select onfocus='set-attr:disabled=disabled' oninput='set-attr:data-wrong=input'><option value='old' selected>Old</option><option value='new'>New</option></select></body></html>"
)
val focus_select = ui_access_find_nodes(
    focus_session.ui_access_snapshot(), "browser:session",
    "select", "", 1
)
val focus_disabled = focus_session.ui_access_act(
    WinTextActionRequest(
        target_id: focus_select[0].canonical_id,
        action: "set_value", text_value: "new", x: 0, y: 0
    )
)
expect(focus_disabled.ok).to_equal(false)
expect(focus_session.dom_callback_count).to_equal(1)
val live_select = be_dom_find_by_tag(
    focus_session.current_dom, "select"
)[0]
expect(be_dom_get_attr(live_select, "data-wrong")).to_equal("")
val focus_after = ui_access_find_nodes(
    focus_session.ui_access_snapshot(), "browser:session",
    "select", "", 1
)
expect(focus_after[0].text_value).to_equal("old")
```

</details>

#### hides secret form state and edits textarea through one focused route

- var session = BrowserSession new
   - Expected: hidden_nodes equals `0`
   - Expected: password_value equals ``
   - Expected: textarea_value equals `old`
   - Expected: edited.ok is true
   - Expected: textarea_focused is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/form",
    "<html><body><input type='hidden' value='csrf-secret'><input type='password' value='password-secret'><textarea>old</textarea></body></html>"
)

val before = session.ui_access_snapshot()
var hidden_nodes = 0
var password_value = "missing"
var textarea_value = "missing"
for node in before.nodes:
    if node.widget_id == "page_input_0":
        hidden_nodes = hidden_nodes + 1
    elif node.widget_id == "page_input_1":
        password_value = node.text_value
    elif node.widget_id == "page_textarea_0":
        textarea_value = node.text_value
expect(hidden_nodes).to_equal(0)
expect(password_value).to_equal("")
expect(textarea_value).to_equal("old")

val edited = session.ui_access_act(WinTextActionRequest(
    target_id: "browser:session#page_textarea_0", action: "set_value",
    text_value: "Ada & Bob", x: 0, y: 0
))
expect(edited.ok).to_equal(true)
expect(session.current_body_html).to_contain("Ada &amp; Bob")
var textarea_focused = false
for node in session.ui_access_snapshot().nodes:
    if node.widget_id == "page_textarea_0":
        textarea_focused = node.focused
expect(textarea_focused).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/simple_web_browser_production_hardening.md`
- **Plan:** `doc/03_plan/sys_test/simple_web_browser_production_hardening.md`
- **Design:** `doc/05_design/ui/web/simple_web_browser_production_hardening.md`
- **Research:** `doc/01_research/local/simple_web_browser_production_hardening.md`


</details>
