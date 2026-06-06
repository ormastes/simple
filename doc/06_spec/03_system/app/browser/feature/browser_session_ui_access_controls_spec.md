# Browser Session Ui Access Controls Specification

> 1. var session = BrowserSession new

<!-- sdn-diagram:id=browser_session_ui_access_controls_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_session_ui_access_controls_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_session_ui_access_controls_spec -> std
browser_session_ui_access_controls_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_session_ui_access_controls_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Ui Access Controls Specification

## Scenarios

### BrowserSession primitive controls through textual UI access

#### exposes browser toolbar controls as queryable UI access nodes

1. var session = BrowserSession new

2. session register resource

3. session open html

4. session open html

5. session set home url
   - Expected: snapshot.mode equals `browser_session`
   - Expected: snapshot.active_surface equals `browser:session`
   - Expected: ui_access_find_nodes(snapshot, "browser:session", "button", "Back", 1).len() equals `1`
   - Expected: ui_access_find_nodes(snapshot, "browser:session", "button", "Forward", 1).len() equals `1`
   - Expected: ui_access_find_nodes(snapshot, "browser:session", "button", "Stop", 1).len() equals `1`
   - Expected: ui_access_find_nodes(snapshot, "browser:session", "button", "Home", 1).len() equals `1`
   - Expected: ui_access_find_nodes(snapshot, "browser:session", "button", "Favorite", 1).len() equals `1`
   - Expected: ui_access_find_nodes(snapshot, "browser:session", "textfield", "https://example.com/two", 1).len() equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource("https://example.com/home", "<html><head><title>Home</title></head><body>Home</body></html>")
session.open_html("https://example.com/one", "<html><head><title>One</title></head><body>One</body></html>")
session.open_html("https://example.com/two", "<html><head><title>Two</title></head><body>Two</body></html>")
session.set_home_url("https://example.com/home")

val snapshot = session.ui_access_snapshot()
expect(snapshot.mode).to_equal("browser_session")
expect(snapshot.active_surface).to_equal("browser:session")
expect(ui_access_find_nodes(snapshot, "browser:session", "button", "Back", 1).len()).to_equal(1)
expect(ui_access_find_nodes(snapshot, "browser:session", "button", "Forward", 1).len()).to_equal(1)
expect(ui_access_find_nodes(snapshot, "browser:session", "button", "Stop", 1).len()).to_equal(1)
expect(ui_access_find_nodes(snapshot, "browser:session", "button", "Home", 1).len()).to_equal(1)
expect(ui_access_find_nodes(snapshot, "browser:session", "button", "Favorite", 1).len()).to_equal(1)
expect(ui_access_find_nodes(snapshot, "browser:session", "textfield", "https://example.com/two", 1).len()).to_equal(1)
```

</details>

#### routes textual UI access actions into BrowserSession primitive controls

1. var session = BrowserSession new

2. session register resource

3. session open html

4. session open html

5. session set home url
   - Expected: back.ok is true
   - Expected: session.current_url equals `https://example.com/one`
   - Expected: forward.ok is true
   - Expected: session.current_url equals `https://example.com/two`
   - Expected: favorite.ok is true
   - Expected: session.is_favorite("https://example.com/two") is true
   - Expected: favorite_nodes.len() equals `1`
   - Expected: favorite_nodes[0].selected is true

6. session begin navigation
   - Expected: stop.ok is true
   - Expected: session.is_loading is false
   - Expected: home.ok is true
   - Expected: session.current_url equals `https://example.com/home`


<details>
<summary>Executable SPipe</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource("https://example.com/home", "<html><head><title>Home</title></head><body>Home</body></html>")
session.open_html("https://example.com/one", "<html><head><title>One</title></head><body>One</body></html>")
session.open_html("https://example.com/two", "<html><head><title>Two</title></head><body>Two</body></html>")
session.set_home_url("https://example.com/home")

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

session.begin_navigation("https://example.com/pending")
val stop = session.ui_access_act(WinTextActionRequest(target_id: "browser:session#stop", action: "click", text_value: "", x: 0, y: 0))
expect(stop.ok).to_equal(true)
expect(session.is_loading).to_equal(false)

val home = session.ui_access_act(WinTextActionRequest(target_id: "browser:session#home", action: "click", text_value: "", x: 0, y: 0))
expect(home.ok).to_equal(true)
expect(session.current_url).to_equal("https://example.com/home")
```

</details>

#### rejects unsupported browser UI actions through the textual route

1. var session = BrowserSession new

2. session open html
   - Expected: result.ok is false
   - Expected: result.code equals `unsupported_operation`


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session register resource

3. session open html
   - Expected: links.len() equals `1`
   - Expected: _node_prop(links[0], "href") equals `https://example.com/docs/page.html`
   - Expected: result.ok is true
   - Expected: session.current_url equals `https://example.com/docs/page.html`


<details>
<summary>Executable SPipe</summary>

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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/browser/feature/browser_session_ui_access_controls_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserSession primitive controls through textual UI access

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
