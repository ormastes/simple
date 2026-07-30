# browser_session_ui_access_controls_spec

> This spec exercises browser chrome and DOM controls through the canonical textual UI access surface, including bounded address input and rendered state. Unicode noncharacters are valid scalar values and remain allowed in drafts; malformed UTF-8, C0, DEL, and C1 controls fail closed before mutation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# browser_session_ui_access_controls_spec

This spec exercises browser chrome and DOM controls through the canonical textual UI access surface, including bounded address input and rendered state. Unicode noncharacters are valid scalar values and remain allowed in drafts; malformed UTF-8, C0, DEL, and C1 controls fail closed before mutation.

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
Unicode noncharacters are valid scalar values and remain allowed in drafts;
malformed UTF-8, C0, DEL, and C1 controls fail closed before mutation.

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

#### should restore edited text controls during history traversal

Back/Forward restores departure state; Reload keeps rebuilding the committed source.

- Commit a page and edit its live text control
   - Expected: text, textarea, checkbox, radio, and select edits succeed
   - Expected: session.current_url equals `https://example.com/form`
   - Expected: session.history.len() equals `1`
   - Expected: session.current_index equals `0`
   - Expected: one textfield exposes `kept`
- Commit a second page without rewriting the first history entry
   - Expected: the same URL commits with a different scripted title and CSP
   - Expected: session.history.len() equals `2`
   - Expected: scripted page mutation cannot overwrite the first URL, source, or persisted state
   - Expected: session.current_index equals `1`
   - Expected: Back is enabled
- Traverse Back through the textual browser control
   - Expected: back.ok is true
   - Expected: the committed URL is `https://example.com/form`
   - Expected: the two-entry history ledger and index `0` are retained
- Retain the committed page ledger and edited control value
   - Expected: Back is disabled
   - Expected: Forward is enabled
   - Expected: all five control kinds expose their edited state
   - Expected: Reload restores source defaults and the first CSP without growing history
   - Expected: Forward restores the second page without growing history

<details>
<summary>Executable SSpec</summary>

Runnable source: 201 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
"""Back/Forward restores departure state; Reload keeps rebuilding the committed source."""
val first_url = "https://example.com/form"
val second_url = first_url
val first_policy = "default-src 'self'"
val second_policy = (
    "default-src 'self'; script-src 'unsafe-inline'"
)
val first_html = (
    "<html><head><title>Form</title>" +
    "<meta http-equiv='Content-Security-Policy' content=\"" +
    first_policy + "\"></head><body>" +
    "<input value='initial'>" +
    "<input type='checkbox' value='check'>" +
    "<input type='radio' name='tone' value='red' checked>" +
    "<input type='radio' name='tone' value='blue'>" +
    "<textarea>old memo</textarea>" +
    "<select><option value='a' selected>A</option>" +
    "<option value='b'>B</option></select></body></html>"
)

step("Commit a page and edit its live text control")
var session = BrowserSession.new()
expect(session.open_html(first_url, first_html).is_ok()).to_be(true)
val text_edit = session.ui_access_act(WinTextActionRequest(
    target_id: "browser:session#page_input_0",
    action: "set_value", text_value: "kept", x: 0, y: 0
))
val checkbox_edit = session.ui_access_act(WinTextActionRequest(
    target_id: "browser:session#page_input_1",
    action: "click", text_value: "", x: 0, y: 0
))
val radio_edit = session.ui_access_act(WinTextActionRequest(
    target_id: "browser:session#page_input_3",
    action: "click", text_value: "", x: 0, y: 0
))
val textarea_edit = session.ui_access_act(WinTextActionRequest(
    target_id: "browser:session#page_textarea_0",
    action: "set_value", text_value: "memo", x: 0, y: 0
))
val initial_select = ui_access_find_nodes(
    session.ui_access_snapshot(), "browser:session",
    "select", "a", 1
)
expect(initial_select.len()).to_equal(1)
val select_edit = session.ui_access_act(WinTextActionRequest(
    target_id: initial_select[0].canonical_id,
    action: "set_value", text_value: "b", x: 0, y: 0
))
expect(text_edit.ok).to_be(true)
expect(checkbox_edit.ok).to_be(true)
expect(radio_edit.ok).to_be(true)
expect(textarea_edit.ok).to_be(true)
expect(select_edit.ok).to_be(true)
expect(session.current_url).to_equal(first_url)
expect(session.history.len()).to_equal(1)
expect(session.current_index).to_equal(0)
expect(ui_access_find_nodes(
    session.ui_access_snapshot(), "browser:session",
    "textfield", "kept", 1
).len()).to_equal(1)

step("Commit a second page without rewriting the first history entry")
expect(session.open_html(
    second_url,
    "<html><head><title>Next</title>" +
    "<meta http-equiv='Content-Security-Policy' content=\"" +
    second_policy + "\"></head><body>Next" +
    "<script>document.title = 'Scripted next';" +
    "document.body.innerHTML = '<main>Scripted next</main>';" +
    "</script></body></html>"
).is_ok()).to_be(true)
val back_before = ui_access_find_nodes(
    session.ui_access_snapshot(), "browser:session",
    "button", "Back", 1
)
expect(session.current_url).to_equal(second_url)
expect(session.history.len()).to_equal(2)
expect(session.history[0].url).to_equal(first_url)
expect(session.history[0].source_html).to_equal(first_html)
expect(session.history[0].persisted_html).to_contain(
    "value=\"kept\""
)
expect(session.history[0].persisted_html.contains(
    "Scripted next"
)).to_be(false)
expect(session.history[1].url).to_equal(second_url)
expect(session.history[0].title).to_equal("Form")
expect(session.history[1].title).to_equal("Scripted next")
expect(session.history[0].content_security_policy).to_equal(
    first_policy
)
expect(session.history[1].content_security_policy).to_equal(
    second_policy
)
expect(session.current_index).to_equal(1)
expect(back_before[0].enabled).to_be(true)

step("Traverse Back through the textual browser control")
val back = session.ui_access_act(WinTextActionRequest(
    target_id: "browser:session#back", action: "click",
    text_value: "", x: 0, y: 0
))
expect(back.ok).to_be(true)
expect(session.current_url).to_equal(first_url)
expect(session.history.len()).to_equal(2)
expect(session.history[0].url).to_equal(first_url)
expect(session.history[1].url).to_equal(second_url)
expect(session.current_index).to_equal(0)
expect(session.current_title).to_equal("Form")
expect(session.content_security_policy).to_equal(first_policy)

step("Retain the committed page ledger and edited control value")
val back_after = ui_access_find_nodes(
    session.ui_access_snapshot(), "browser:session",
    "button", "Back", 1
)
val forward_after = ui_access_find_nodes(
    session.ui_access_snapshot(), "browser:session",
    "button", "Forward", 1
)
val restored = session.ui_access_snapshot()
expect(back_after[0].enabled).to_be(false)
expect(forward_after[0].enabled).to_be(true)
expect(ui_access_find_nodes(
    restored, "browser:session",
    "textfield", "kept", 1
).len()).to_equal(1)
expect(ui_access_find_nodes(
    restored, "browser:session",
    "textfield", "memo", 1
).len()).to_equal(1)
val restored_checkbox = ui_access_find_nodes(
    restored, "browser:session", "checkbox", "check", 1
)
val restored_red = ui_access_find_nodes(
    restored, "browser:session", "radio", "red", 1
)
val restored_blue = ui_access_find_nodes(
    restored, "browser:session", "radio", "blue", 1
)
expect(restored_checkbox[0].selected).to_be(true)
expect(restored_red[0].selected).to_be(false)
expect(restored_blue[0].selected).to_be(true)
expect(ui_access_find_nodes(
    restored, "browser:session", "select", "b", 1
).len()).to_equal(1)

val reload = session.ui_access_act(WinTextActionRequest(
    target_id: "browser:session#reload", action: "click",
    text_value: "", x: 0, y: 0
))
expect(reload.ok).to_be(true)
val reload_request = session.take_pending_request().unwrap()
expect(reload_request.kind).to_equal("document")
expect(session.commit_network_response(BrowserResponse.create(
    reload_request.id, "document", reload_request.url,
    200, "", first_html, ""
)).is_ok()).to_be(true)
val reloaded = session.ui_access_snapshot()
expect(session.history.len()).to_equal(2)
expect(session.current_index).to_equal(0)
expect(session.history[0].source_html).to_equal(first_html)
expect(session.history[0].content_security_policy).to_equal(
    first_policy
)
expect(session.history[1].content_security_policy).to_equal(
    second_policy
)
expect(ui_access_find_nodes(
    reloaded, "browser:session", "textfield", "initial", 1
).len()).to_equal(1)
expect(ui_access_find_nodes(
    reloaded, "browser:session", "textfield", "old memo", 1
).len()).to_equal(1)
val default_checkbox = ui_access_find_nodes(
    reloaded, "browser:session", "checkbox", "check", 1
)
val default_red = ui_access_find_nodes(
    reloaded, "browser:session", "radio", "red", 1
)
val default_blue = ui_access_find_nodes(
    reloaded, "browser:session", "radio", "blue", 1
)
expect(default_checkbox[0].selected).to_be(false)
expect(default_red[0].selected).to_be(true)
expect(default_blue[0].selected).to_be(false)
expect(ui_access_find_nodes(
    reloaded, "browser:session", "select", "a", 1
).len()).to_equal(1)

val forward = session.ui_access_act(WinTextActionRequest(
    target_id: "browser:session#forward", action: "click",
    text_value: "", x: 0, y: 0
))
expect(forward.ok).to_be(true)
expect(session.current_url).to_equal(second_url)
expect(session.history.len()).to_equal(2)
expect(session.current_index).to_equal(1)
expect(session.history[0].source_html).to_equal(first_html)
expect(session.current_title).to_equal("Scripted next")
expect(session.content_security_policy).to_equal(second_policy)
```

</details>

#### reports favorite availability and mutation truthfully

The public chrome route reports only session-local favorite mutations.

- Inspect Favorite before a network document is open
   - Expected: unavailable.len() equals `1`
   - Expected: unavailable[0].enabled equals `false`
   - Expected: session.bookmark_snapshot().entries.len() equals `0`
- Attempt Favorite through the public textual action
   - Expected: denied.ok equals `false`
   - Expected: denied.code equals `disabled`
   - Expected: session.bookmark_snapshot().entries.len() equals `0`
- Open a network document and add it through the same action
   - Expected: added.ok equals `true`
   - Expected: session.bookmark_snapshot().entries.len() equals `1`
   - Expected: session.is_favorite("https://example.com/bookmarkable") equals `true`
- Remove the saved page and retain an enabled truthful control
   - Expected: removed.ok equals `true`
   - Expected: session.bookmark_snapshot().entries.len() equals `0`
   - Expected: available[0].enabled equals `true`
   - Expected: available[0].selected equals `false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect Favorite before a network document is open")
var session = BrowserSession.new()
val unavailable = ui_access_find_nodes(
    session.ui_access_snapshot(), "browser:session",
    "button", "Favorite", 1
)
expect(unavailable.len()).to_equal(1)
expect(unavailable[0].enabled).to_equal(false)
expect(session.bookmark_snapshot().entries.len()).to_equal(0)

step("Attempt Favorite through the public textual action")
val denied = session.ui_access_act(WinTextActionRequest(
    target_id: "browser:session#favorite", action: "click",
    text_value: "", x: 0, y: 0
))
expect(denied.ok).to_equal(false)
expect(denied.code).to_equal("disabled")
expect(session.bookmark_snapshot().entries.len()).to_equal(0)

step("Open a network document and add it through the same action")
session.open_html(
    "https://example.com/bookmarkable",
    "<html><head><title>Bookmarkable</title></head><body>Page</body></html>"
)
val added = session.ui_access_act(WinTextActionRequest(
    target_id: "browser:session#favorite", action: "click",
    text_value: "", x: 0, y: 0
))
expect(added.ok).to_equal(true)
expect(session.bookmark_snapshot().entries.len()).to_equal(1)
expect(session.is_favorite(
    "https://example.com/bookmarkable"
)).to_equal(true)

step("Remove the saved page and retain an enabled truthful control")
val removed = session.ui_access_act(WinTextActionRequest(
    target_id: "browser:session#favorite", action: "click",
    text_value: "", x: 0, y: 0
))
val available = ui_access_find_nodes(
    session.ui_access_snapshot(), "browser:session",
    "button", "Favorite", 1
)
expect(removed.ok).to_equal(true)
expect(session.bookmark_snapshot().entries.len()).to_equal(0)
expect(available[0].enabled).to_equal(true)
expect(available[0].selected).to_equal(false)
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

#### publishes address edits through a newer UI snapshot revision

**Requirements exercised:** REQ-WEB-BROWSER-007, REQ-WEB-BROWSER-008,
REQ-WEB-BROWSER-009, REQ-WEB-BROWSER-021.

- Capture the address snapshot before editing
- Edit the address without starting navigation
   - Expected: edit succeeds, the snapshot revision increases, the visible
     address is found by canonical query, and the committed URL remains
     unchanged.
- Keep the published revision stable for unchanged or invalid text
   - Expected: setting the same address and rejected control text do not
     change the revision.

<details>
<summary>Executable SSpec</summary>

```simple
step("Capture the address snapshot before editing")
var session = BrowserSession.new()
session.open_html("https://example.com/start", "<html><body>Start</body></html>")
val before = session.ui_access_snapshot()

step("Edit the address without starting navigation")
val edited = session.ui_access_act(WinTextActionRequest(
    target_id: "browser:session#address", action: "set_value",
    text_value: "https://example.com/target", x: 0, y: 0
))
val after = session.ui_access_snapshot()
expect(edited.ok).to_equal(true)
expect(after.snapshot_revision).to_be_greater_than(before.snapshot_revision)
val addresses = ui_access_find_nodes(
    after, "browser:session", "textfield", "https://example.com/target", 1
)
expect(addresses.len()).to_equal(1)
expect(addresses[0].canonical_id).to_equal("browser:session#address")
expect(session.current_url).to_equal("https://example.com/start")

step("Keep the published revision stable for unchanged or invalid text")
val unchanged = session.ui_access_act(WinTextActionRequest(
    target_id: "browser:session#address", action: "set_value",
    text_value: "https://example.com/target", x: 0, y: 0
))
expect(unchanged.ok).to_equal(true)
expect(session.ui_access_snapshot().snapshot_revision).to_equal(after.snapshot_revision)
val rejected = session.ui_access_act(WinTextActionRequest(
    target_id: "browser:session#address", action: "set_value",
    text_value: "https://example.com/\nblocked", x: 0, y: 0
))
expect(rejected.code).to_equal("address-invalid-control")
expect(session.ui_access_snapshot().snapshot_revision).to_equal(after.snapshot_revision)
```

</details>

#### bounds UTF-8 address input without partial state or pixel mutation

- Accept exactly 2048 UTF-8 bytes and project the draft accessibly
   - Expected: BROWSER_ADDRESS_MAX_BYTES equals `2048`
   - Expected: initial_pixels[0] equals `0xFFFF0000u32`
   - Expected: text_byte_len(exact_draft) equals `2048`
   - Expected: text_codepoint_len(exact_draft) equals `2046`
   - Expected: accepted.ok is true
   - Expected: _address_node_count(session, exact_draft) equals `1`
   - Expected: focus_before equals `keep`
- Reject 2049 bytes before trimming and preserve browser state
   - Expected: leading_overflow.code equals `address-too-long`
   - Expected: trailing_overflow.code equals `address-too-long`
   - Expected: session.address_draft equals `exact_draft`
   - Expected: session.current_url equals `https://example.com/start`
   - Expected: session.history.len() equals `history_before`
   - Expected: session.current_index equals `index_before`
   - Expected: session.pending_request_count() equals `pending_before`
   - Expected: session.pending_url equals `pending_url_before`
   - Expected: session.is_loading equals `loading_before`
   - Expected: be_dom_focused_id(session.dom_root()) equals `focus_before`
   - Expected: session.ui_access_revision equals `revision_before`
- Reject C0 DEL and C1 controls before UI projection
   - Expected: leading_newline.code equals `address-invalid-control`
   - Expected: trailing_newline.code equals `address-invalid-control`
   - Expected: nul.code equals `address-invalid-control`
   - Expected: session.address_draft equals `exact_draft`
   - Expected: session.current_url equals `https://example.com/start`
   - Expected: session.history.len() equals `history_before`
   - Expected: session.current_index equals `index_before`
   - Expected: session.pending_request_count() equals `pending_before`
   - Expected: session.pending_url equals `pending_url_before`
   - Expected: session.is_loading equals `loading_before`
   - Expected: be_dom_focused_id(session.dom_root()) equals `focus_before`
   - Expected: session.ui_access_revision equals `revision_before`
   - Expected: _address_node_count(session, exact_draft) equals `1`
- Submit an exact 2048-byte URL and render the committed page
   - Expected: text_byte_len(exact_url) equals `2048`
   - Expected: exact_submit.ok is true
   - Expected: session.current_url equals `exact_url`
   - Expected: _pixels_equal(exact_pixels, initial_pixels) is false
   - Expected: exact_pixels[0] equals `0xFF00FF00u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 116 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/start",
    "<html style='background:#ff0000'><body>" +
    "<input id='keep' data-focused value='Start'></body></html>"
)
val exact_draft = _repeat_ascii("a", 2045) + "한"
val initial_pixels = session.render_to_pixels(8, 8).pixels
val initial_red_count = _count_pixel(
    initial_pixels, 0xFFFF0000u32
)

expect(BROWSER_ADDRESS_MAX_BYTES).to_equal(2048)
expect(initial_red_count).to_be_greater_than(0)
expect(initial_pixels[0]).to_equal(0xFFFF0000u32)
expect(text_byte_len(exact_draft)).to_equal(2048)
expect(text_codepoint_len(exact_draft)).to_equal(2046)
val accepted = session.ui_access_act(WinTextActionRequest(
    target_id: "browser:session#address", action: "set_value",
    text_value: exact_draft, x: 0, y: 0
))
expect(accepted.ok).to_equal(true)
expect(_address_node_count(session, exact_draft)).to_equal(1)
expect(_address_has_submit_action(
    session, exact_draft
)).to_equal(true)
val revision_before = session.ui_access_revision
val history_before = session.history.len()
val index_before = session.current_index
val pending_before = session.pending_request_count()
val pending_url_before = session.pending_url
val loading_before = session.is_loading
val focus_before = be_dom_focused_id(session.dom_root())
expect(focus_before).to_equal("keep")

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
expect(session.pending_url).to_equal(pending_url_before)
expect(session.is_loading).to_equal(loading_before)
expect(be_dom_focused_id(session.dom_root())).to_equal(focus_before)
expect(session.ui_access_revision).to_equal(revision_before)
expect(_address_pixels_match(
    session, initial_pixels
)).to_equal(true)

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
expect(_set_address_scalar_code(
    session, 127
)).to_equal("address-invalid-control")
expect(_set_address_scalar_code(
    session, 128
)).to_equal("address-invalid-control")
expect(_set_address_scalar_code(
    session, 159
)).to_equal("address-invalid-control")
expect(session.address_draft).to_equal(exact_draft)
expect(session.current_url).to_equal("https://example.com/start")
expect(session.history.len()).to_equal(history_before)
expect(session.current_index).to_equal(index_before)
expect(session.pending_request_count()).to_equal(pending_before)
expect(session.pending_url).to_equal(pending_url_before)
expect(session.is_loading).to_equal(loading_before)
expect(be_dom_focused_id(session.dom_root())).to_equal(focus_before)
expect(session.ui_access_revision).to_equal(revision_before)
expect(_address_node_count(session, exact_draft)).to_equal(1)
expect(_address_pixels_match(
    session, initial_pixels
)).to_equal(true)

val exact_url = "https://example.com/" + _repeat_ascii("a", 2028)
expect(text_byte_len(exact_url)).to_equal(2048)
session.register_resource(
    exact_url,
    "<html style='background:#00ff00'><body>Exact</body></html>"
)
val exact_submit = session.ui_access_act(WinTextActionRequest(
    target_id: "browser:session#address", action: "submit",
    text_value: exact_url, x: 0, y: 0
))
expect(exact_submit.ok).to_equal(true)
expect(session.current_url).to_equal(exact_url)
expect(session.current_body_html).to_contain("Exact")
val exact_pixels = session.render_to_pixels(8, 8).pixels
expect(_pixels_equal(exact_pixels, initial_pixels)).to_equal(false)
val exact_green_count = _count_pixel(
    exact_pixels, 0xFF00FF00u32
)
expect(exact_green_count).to_be_greater_than(0)
expect(exact_pixels[0]).to_equal(0xFF00FF00u32)
```

</details>

<details>
<summary>Advanced: keeps hosted worker registry and live-entry address rejection atomic</summary>

#### keeps hosted worker registry and live-entry address rejection atomic

- rt bytes to text
- rt bytes to text
- rt bytes to text
- rt bytes to text
- rt bytes to text
- rt bytes to text
- rt bytes to text
- rt bytes to text
- rt bytes to text
- rt bytes to text
- rt bytes to text
- rt bytes to text
- rt bytes to text
- rt bytes to text
- rt bytes to text
- Err
- Ok
   - Expected: live_entry_draft equals `about:blank`
   - Expected: live_entry_pending equals `pending`
   - Expected: live_entry_replace is true
- Reject C1 through the hosted semantic web editor
   - Expected: hosted_rejected.reason equals `address-invalid-control`
   - Expected: hosted.browser.current_url equals `hosted_url`
   - Expected: hosted.browser.history.len() equals `hosted_history`
   - Expected: hosted.browser.current_index equals `hosted_index`
   - Expected: hosted.browser.is_loading equals `hosted_loading`
   - Expected: hosted.mutation_revision equals `hosted_revision`
   - Expected: hosted.chrome_focus equals `address`
   - Expected: hosted.address_replace_on_text is true
- hosted browser ui access snapshot
- hosted browser render to pixels
   - Expected: hosted_exact.callback_count equals `1`
   - Expected: hosted.browser.address_draft equals `exact`
- hosted browser render to pixels
- Reject C1 through the renderer worker without clearing focus
- var worker = HostedBrowserRendererWorkerSession create
- payload: "T1\t{invalid len
   - Expected: worker.browser.current_url equals `worker_url`
   - Expected: worker.browser.history.len() equals `worker_history`
   - Expected: worker.browser.current_index equals `worker_index`
   - Expected: worker.browser.ui_access_revision equals `worker_revision`
   - Expected: worker.browser.is_loading equals `worker_loading`
   - Expected: worker.chrome_focus equals `address`
   - Expected: worker.address_replace_on_text is true
- worker browser ui access snapshot
- worker browser render to pixels
- payload: "T1\t{exact len
   - Expected: worker_exact.ok is true
   - Expected: worker.browser.address_draft equals `exact`
- Reject C1 through the hosted parent registry wire
   - Expected: registry.address_text(92) equals `about:blank`
   - Expected: registry.document_url(92) equals `registry_url`
   - Expected: registry.entries[0].renderer.state equals `registry_state`
   - Expected: registry.entries[0].address_editing is true
   - Expected: registry.entries[0].address_replace_on_text is true
   - Expected: registry_exact.callback_count equals `1`
   - Expected: registry.address_text(92) equals `exact`


<details>
<summary>Executable SSpec</summary>

Runnable source: 210 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val invalid = "https://example.com/" + _scalar_text(128)
val exact = _repeat_ascii("a", 2048)
var c0: i64 = 0
while c0 < 32:
    expect(browser_address_input_error(
        rt_bytes_to_text([c0 as u8])
    )).to_equal("address-invalid-control")
    c0 = c0 + 1
expect(browser_address_input_error(
    rt_bytes_to_text([0x7Fu8])
)).to_equal("address-invalid-control")
expect(browser_address_input_error(
    rt_bytes_to_text([0xC2u8, 0x80u8])
)).to_equal("address-invalid-control")
expect(browser_address_input_error(
    rt_bytes_to_text([0xC2u8, 0x90u8])
)).to_equal("address-invalid-control")
expect(browser_address_input_error(
    rt_bytes_to_text([0xC2u8, 0x9Fu8])
)).to_equal("address-invalid-control")
expect(browser_address_input_error(
    rt_bytes_to_text([0xC0u8, 0xAFu8])
)).to_equal("address-invalid-utf8")
expect(browser_address_input_error(
    rt_bytes_to_text([0xC2u8])
)).to_equal("address-invalid-utf8")
expect(browser_address_input_error(
    rt_bytes_to_text([0xC2u8, 0x20u8])
)).to_equal("address-invalid-utf8")
expect(browser_address_input_error(
    rt_bytes_to_text([0xEDu8, 0xA0u8, 0x80u8])
)).to_equal("address-invalid-utf8")
expect(browser_address_input_error(
    rt_bytes_to_text([0xF4u8, 0x90u8, 0x80u8, 0x80u8])
)).to_equal("address-invalid-utf8")
expect(browser_address_input_error(
    rt_bytes_to_text([0x80u8])
)).to_equal("address-invalid-utf8")
expect(browser_address_input_error(
    rt_bytes_to_text([0x61u8, 0x00u8, 0x62u8])
)).to_equal("address-invalid-control")
expect(browser_address_input_error(
    rt_bytes_to_text([0xEFu8, 0xB7u8, 0x90u8])
)).to_equal("")
expect(browser_address_input_error(
    rt_bytes_to_text([0xEFu8, 0xBFu8, 0xBFu8])
)).to_equal("")
expect(browser_address_input_error(
    rt_bytes_to_text([0xF4u8, 0x8Fu8, 0xBFu8, 0xBFu8])
)).to_equal("")
expect(browser_address_input_error("\0")).to_equal(
    "address-invalid-control"
)
expect(browser_address_input_error(_scalar_text(127))).to_equal(
    "address-invalid-control"
)
expect(browser_address_input_error(_scalar_text(128))).to_equal(
    "address-invalid-control"
)
expect(browser_address_input_error(_scalar_text(159))).to_equal(
    "address-invalid-control"
)
expect(browser_address_update(
    "about:blank", invalid, true
).is_err()).to_equal(true)
expect(browser_address_update(
    "about:blank", invalid, false
).is_err()).to_equal(true)
expect(browser_address_update(
    "about:blank", exact, true
).unwrap()).to_equal(exact)
var live_entry_draft = "about:blank"
val live_entry_pending = "pending"
var live_entry_replace = true
match browser_address_update(
    live_entry_draft, invalid, live_entry_replace
):
    Err(_): ()
    Ok(updated):
        live_entry_draft = updated
        live_entry_replace = false
expect(live_entry_draft).to_equal("about:blank")
expect(live_entry_pending).to_equal("pending")
expect(live_entry_replace).to_equal(true)

step("Reject C1 through the hosted semantic web editor")
var hosted = HostedWebContentSession.create(
    41, "<div style='background:#ff0000'>Start</div>", 8, 8
)
val _ = hosted.dispatch_chrome_pointer(1, "address", true)
val _ = hosted.dispatch_chrome_pointer(2, "address", false)
val hosted_url = hosted.browser.current_url
val hosted_history = hosted.browser.history.len()
val hosted_index = hosted.browser.current_index
val hosted_pending = hosted.browser.pending_request_count()
val hosted_loading = hosted.browser.is_loading
val hosted_revision = hosted.mutation_revision
val hosted_pixels = hosted.browser.render_to_pixels(8, 8).pixels
val hosted_rejected = hosted.dispatch_text(3, invalid)
expect(hosted_rejected.reason).to_equal("address-invalid-control")
expect(hosted.browser.current_url).to_equal(hosted_url)
expect(hosted.browser.history.len()).to_equal(hosted_history)
expect(hosted.browser.current_index).to_equal(hosted_index)
expect(hosted.browser.pending_request_count()).to_equal(
    hosted_pending
)
expect(hosted.browser.is_loading).to_equal(hosted_loading)
expect(hosted.mutation_revision).to_equal(hosted_revision)
expect(hosted.chrome_focus).to_equal("address")
expect(hosted.address_replace_on_text).to_equal(true)
expect(ui_access_find_nodes(
    hosted.browser.ui_access_snapshot(), "browser:session",
    "textfield", hosted_url, 1
).len()).to_equal(1)
expect(_pixels_equal(
    hosted.browser.render_to_pixels(8, 8).pixels, hosted_pixels
)).to_equal(true)
val hosted_exact = hosted.dispatch_text(4, exact)
expect(hosted_exact.callback_count).to_equal(1)
expect(hosted.browser.address_draft).to_equal(exact)
expect(_pixels_equal(
    hosted.browser.render_to_pixels(8, 8).pixels, hosted_pixels
)).to_equal(true)

step("Reject C1 through the renderer worker without clearing focus")
var worker = HostedBrowserRendererWorkerSession.create(8, 8)
expect(worker.handle(BrowserRendererMessage(
    kind: "init", generation: 7, request_id: 2,
    payload: "<div style='background:#ff0000'>Start</div>"
)).ok).to_equal(true)
worker.chrome_focus = "address"
worker.address_replace_on_text = true
val worker_url = worker.browser.current_url
val worker_history = worker.browser.history.len()
val worker_index = worker.browser.current_index
val worker_revision = worker.browser.ui_access_revision
val worker_pending = worker.browser.pending_request_count()
val worker_loading = worker.browser.is_loading
val worker_pixels = worker.browser.render_to_pixels(8, 8).pixels
val worker_rejected = worker.handle(BrowserRendererMessage(
    kind: "text", generation: 7, request_id: 3,
    payload: "T1\t{invalid.len()}\n{invalid}"
))
expect(worker_rejected.reason).to_equal(
    "address-invalid-control"
)
expect(worker.browser.current_url).to_equal(worker_url)
expect(worker.browser.history.len()).to_equal(worker_history)
expect(worker.browser.current_index).to_equal(worker_index)
expect(worker.browser.ui_access_revision).to_equal(worker_revision)
expect(worker.browser.pending_request_count()).to_equal(
    worker_pending
)
expect(worker.browser.is_loading).to_equal(worker_loading)
expect(worker.chrome_focus).to_equal("address")
expect(worker.address_replace_on_text).to_equal(true)
expect(ui_access_find_nodes(
    worker.browser.ui_access_snapshot(), "browser:session",
    "textfield", worker_url, 1
).len()).to_equal(1)
expect(_pixels_equal(
    worker.browser.render_to_pixels(8, 8).pixels, worker_pixels
)).to_equal(true)
val worker_exact = worker.handle(BrowserRendererMessage(
    kind: "text", generation: 7, request_id: 3,
    payload: "T1\t{exact.len()}\n{exact}"
))
expect(worker_exact.ok).to_equal(true)
expect(worker.browser.address_draft).to_equal(exact)

step("Reject C1 through the hosted parent registry wire")
var registry = HostedBrowserRendererRegistry.create(
    "/bin/false", "https://example.com/"
)
val _ = registry.ensure(
    92, "<div>Start</div>", 8, 8, 0, 100000
)
val _ = registry.dispatch_chrome_pointer(
    1, 92, "address", true
)
val _ = registry.dispatch_chrome_pointer(
    2, 92, "address", false
)
val registry_url = registry.document_url(92)
val registry_revision = registry.entries[0].mutation_revision
val registry_pending = registry.entries[0].renderer.pending_operation
val registry_state = registry.entries[0].renderer.state
val registry_pixels = registry.entries[0].pending_frame.pixels
val registry_rejected = registry.dispatch_text(3, 92, invalid)
expect(registry_rejected.reason).to_equal(
    "address-invalid-control"
)
expect(registry.address_text(92)).to_equal("about:blank")
expect(registry.document_url(92)).to_equal(registry_url)
expect(registry.entries[0].mutation_revision).to_equal(
    registry_revision
)
expect(registry.entries[0].renderer.pending_operation).to_equal(
    registry_pending
)
expect(registry.entries[0].renderer.state).to_equal(registry_state)
expect(_pixels_equal(
    registry.entries[0].pending_frame.pixels, registry_pixels
)).to_equal(true)
expect(registry.entries[0].address_editing).to_equal(true)
expect(registry.entries[0].address_replace_on_text).to_equal(true)
val registry_exact = registry.dispatch_text(4, 92, exact)
expect(registry_exact.callback_count).to_equal(1)
expect(registry.address_text(92)).to_equal(exact)
val _ = registry.close()
```

</details>


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
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/simple_web_browser_production_hardening.md`
- **Plan:** `doc/03_plan/sys_test/simple_web_browser_production_hardening.md`
- **Design:** `doc/05_design/ui/web/simple_web_browser_production_hardening.md`
- **Research:** `doc/01_research/local/simple_web_browser_production_hardening.md`


</details>
