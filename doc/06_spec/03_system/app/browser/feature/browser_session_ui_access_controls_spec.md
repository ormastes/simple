# browser_session_ui_access_controls_spec

> BrowserSession textual UI access control system specification.

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
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# browser_session_ui_access_controls_spec

BrowserSession textual UI access control system specification.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/browser/feature/browser_session_ui_access_controls_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

BrowserSession textual UI access control system specification.

## Evidence

Display policy: `embed_tui`

| Category | Count |
|----------|------:|
| TUI Captures | 1 |

### TUI Captures

| Item | Kind | Path |
|------|------|------|
| `browser_ui_access_snapshot.txt` | TUI capture | `build/test-artifacts/03_system/app/browser/feature/browser_session_ui_access_controls/browser_ui_access_snapshot.txt` |

#### Embedded TUI Text Captures

<details>
<summary>browser_ui_access_snapshot.txt</summary>

```text
BrowserSession UI Access Snapshot
mode: browser_session
active-surface: browser:session
surfaces: 1
surface: browser:session title=Start app=simple-browser active=true
nodes: 8
node: back kind=button text=Back enabled=false selected=false actions=click
node: forward kind=button text=Forward enabled=false selected=false actions=click
node: stop kind=button text=Stop enabled=false selected=false actions=click
node: home kind=button text=Home enabled=true selected=false actions=click
node: favorite kind=button text=Favorite enabled=true selected=false actions=click
node: address kind=textfield text=https://example.com/start/index.html enabled=true selected=false actions=set_value
node: title kind=label text=Start enabled=true selected=false actions=
node: link_0 kind=link text=Read docs enabled=true selected=false actions=click
```

</details>

## Scenarios

### BrowserSession primitive controls through textual UI access

#### exposes browser toolbar controls as queryable UI access nodes

1. var session =  browser session fixture
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

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = _browser_session_fixture()

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

#### captures browser UI access visible state for the generated manual

1. var session = BrowserSession new

2. session open html
   - Expected: _write_ui_capture(capture) equals `0`
   - Expected: _capture_file_state(capture) equals `matched`


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/start/index.html", "<html><head><title>Start</title></head><body><a href='../docs/page.html'>Read docs</a></body></html>")
val snapshot = session.ui_access_snapshot()
val capture = _snapshot_capture(snapshot)

expect(capture).to_contain("BrowserSession UI Access Snapshot")
expect(capture).to_contain("node: back kind=button text=Back")
expect(capture).to_contain("node: favorite kind=button text=Favorite")
expect(capture).to_contain("node: address kind=textfield text=https://example.com/start/index.html")
expect(capture).to_contain("node: link_0 kind=link text=Read docs")
expect(_write_ui_capture(capture)).to_equal(0)
expect(_capture_file_state(capture)).to_equal("matched")
```

</details>

#### routes textual UI access actions into BrowserSession primitive controls

1. var session =  browser session fixture
   - Expected: back.ok is true
   - Expected: session.current_url equals `https://example.com/one`
   - Expected: forward.ok is true
   - Expected: session.current_url equals `https://example.com/two`
   - Expected: favorite.ok is true
   - Expected: session.is_favorite("https://example.com/two") is true
   - Expected: favorite_nodes.len() equals `1`
   - Expected: favorite_nodes[0].selected is true

2. session begin navigation
   - Expected: stop.ok is true
   - Expected: session.is_loading is false
   - Expected: home.ok is true
   - Expected: session.current_url equals `https://example.com/home`


<details>
<summary>Executable SPipe</summary>

Runnable source: 25 lines folded for reproduction.
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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
