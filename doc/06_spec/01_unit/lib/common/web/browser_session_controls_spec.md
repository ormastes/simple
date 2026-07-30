# Browser Session Controls Specification

> Tests covering BrowserSession primitive browser controls.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Controls Specification

## Scenarios

### BrowserSession primitive browser controls

#### stores a bounded title sentinel and derives the URL only for display

- var session = BrowserSession new
- session add favorite
   - Expected: session.favorite_title(url) ?? "missing" equals ``
   - Expected: snapshot.nodes[8].text_value equals `url`
   - Expected: snapshot.nodes[8].props[2].value equals `url`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val url = "https://title.test/saved"
val title_512 = "a".repeat(510) + "é"
val title_513 = "a".repeat(511) + "é"
expect(browser_bookmark_stored_title(title_512)).to_equal(title_512)
expect(browser_bookmark_stored_title(title_513)).to_equal("")
expect(browser_bookmark_title_or_url("", url)).to_equal(url)

var session = BrowserSession.new()
session.add_favorite(url, title_513)
expect(session.favorite_title(url) ?? "missing").to_equal("")
val snapshot = session.ui_access_snapshot()
expect(snapshot.nodes[8].text_value).to_equal(url)
expect(snapshot.nodes[8].props[2].value).to_equal(url)
```

</details>

#### navigates to the configured home page through registered resources

- var session = BrowserSession new
- session register resource
- session open html
- session set home url
- Ok
   - Expected: session.current_url equals `https://example.com/home`
   - Expected: session.current_title equals `Home`
- Err
   - Expected: "unexpected go_home error: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.register_resource("https://example.com/home", "<html><head><title>Home</title></head><body>Home</body></html>")
session.open_html("about:start", "<html><head><title>Start</title></head><body>Start</body></html>")
session.set_home_url("https://example.com/home")

val result = session.go_home()
match result:
    Ok(_) =>
        expect(session.current_url).to_equal("https://example.com/home")
        expect(session.current_title).to_equal("Home")
        expect(session.current_body_html).to_contain("Home")
    Err(e) =>
        expect("unexpected go_home error: {e}").to_equal("")
```

</details>

#### queues a real HTTPS request for an unregistered home page

- var session = BrowserSession new
- session open html
- session set home url
- Ok
- Some
   - Expected: request.kind equals `document`
   - Expected: request.url equals `https://example.com/home`
   - Expected: request.method equals `GET`
- fail
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("about:start", "<html><body>Start</body></html>")
session.set_home_url("https://example.com/home")

match session.go_home():
    Ok(_) =>
        match session.take_pending_request():
            Some(request) =>
                expect(request.kind).to_equal("document")
                expect(request.url).to_equal("https://example.com/home")
                expect(request.method).to_equal("GET")
            nil =>
                fail("Expected home navigation request")
    Err(e) =>
        fail("Expected HTTPS home navigation to start: {e}")
```

</details>

#### normalizes a bare address to HTTPS and rejects explicit unsafe schemes

- var session = BrowserSession new
   - Expected: started.is_ok() is true
   - Expected: request.url equals `https://Example.COM/path`
- fail
- "javascript:alert


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
val started = session.begin_network_navigation(
    "  Example.COM/path  ", "GET", "", "", ""
)
expect(started.is_ok()).to_equal(true)
if val Some(request) = session.take_pending_request():
    expect(request.url).to_equal("https://Example.COM/path")
else:
    fail("Expected normalized HTTPS address request")
expect(session.begin_network_navigation(
    "javascript:alert(1)", "GET", "", "", ""
).is_err()).to_equal(true)
expect(session.begin_network_navigation(
    "ftp://example.com/file", "GET", "", "", ""
).is_err()).to_equal(true)
```

</details>

#### stores normalizes updates and removes favorite links

- var session = BrowserSession new
- session open html
- session add current favorite
   - Expected: session.is_favorite("https://example.com/app") is true
   - Expected: session.favorite_title("https://example.com/app") ?? "" equals `App`
- session add favorite
- session add favorite
   - Expected: session.favorite_links.len() equals `2`
   - Expected: session.favorite_title("https://example.com/docs") ?? "" equals `Docs v2`
- session remove favorite
   - Expected: session.is_favorite("https://example.com/app") is false
   - Expected: session.favorite_links.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html("https://example.com/app", "<html><head><title>App</title></head><body>App</body></html>")
session.add_current_favorite()
expect(session.is_favorite("https://example.com/app")).to_equal(true)
expect(session.favorite_title("https://example.com/app") ?? "").to_equal("App")

session.add_favorite("https://example.com/docs", "Docs")
session.add_favorite("https://example.com/docs", "Docs v2")
expect(session.favorite_links.len()).to_equal(2)
expect(session.favorite_title("https://example.com/docs") ?? "").to_equal("Docs v2")

session.remove_favorite("https://example.com/app")
expect(session.is_favorite("https://example.com/app")).to_equal(false)
expect(session.favorite_links.len()).to_equal(1)
```

</details>

#### loads only bounded network bookmarks through a typed snapshot

- var source = BrowserSession new
- source add favorite
- source remove favorite
- var restored = BrowserSession new
   - Expected: accepted equals `1`
   - Expected: restored.favorite_title("https://example.com/docs") ?? "" equals `Docs`
- Pair
- Pair
- Pair
   - Expected: restored.load_bookmark_snapshot(hostile) equals `1`
   - Expected: restored.favorite_links.len() equals `1`
   - Expected: restored.is_favorite("https://safe.example/path") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var source = BrowserSession.new()
source.add_favorite("https://example.com/docs", " Docs ")
val snapshot = source.bookmark_snapshot()
source.remove_favorite("https://example.com/docs")

var restored = BrowserSession.new()
val accepted = restored.load_bookmark_snapshot(snapshot)
expect(accepted).to_equal(1)
expect(restored.favorite_title("https://example.com/docs") ?? "").to_equal("Docs")

val hostile = BrowserBookmarkSnapshot.create([
    Pair(first: "javascript:alert(1)", second: "unsafe"),
    Pair(first: "file:///etc/passwd", second: "local"),
    Pair(first: "https://safe.example/path", second: "Safe")
])
expect(restored.load_bookmark_snapshot(hostile)).to_equal(1)
expect(restored.favorite_links.len()).to_equal(1)
expect(restored.is_favorite("https://safe.example/path")).to_equal(true)
```

</details>

#### replaces an older pending navigation

- var session = BrowserSession new
- Ok
   - Expected: session.has_pending_requests() is true
- Err
- fail
- Ok
   - Expected: session.has_pending_requests() is true
- Err
- fail
- Some
   - Expected: request.url equals `https://example.com/two`
   - Expected: request.method equals `POST`
   - Expected: request.body equals `body`
- fail
   - Expected: session.has_pending_requests() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()

val first_result = session.begin_network_navigation("https://example.com/one", "GET", "", "", "")
val second_result = session.begin_network_navigation("https://example.com/two", "POST", "X-Test: 1", "body", "text/plain")

match first_result:
    Ok(_) =>
        expect(session.has_pending_requests()).to_equal(true)
    Err(e) =>
        fail("Expected first navigation request to enqueue: {e}")
match second_result:
    Ok(_) =>
        expect(session.has_pending_requests()).to_equal(true)
    Err(e) =>
        fail("Expected second navigation request to enqueue: {e}")

match session.take_pending_request():
    Some(request) =>
        expect(request.url).to_equal("https://example.com/two")
        expect(request.method).to_equal("POST")
        expect(request.body).to_equal("body")
    nil =>
        fail("Expected replacement pending request")

expect(session.has_pending_requests()).to_equal(false)
```

</details>

#### stops a pending subresource while preserving the committed document

- var session = BrowserSession new
   - Expected: session.is_loading is false
   - Expected: session.can_stop_loading() is true
   - Expected: session.has_inflight_request(pending) is true
- session stop loading
   - Expected: session.can_stop_loading() is false
   - Expected: session.current_url equals `https://example.com/page`
   - Expected: session.history.len() equals `1`
   - Expected: session.has_inflight_request(pending) is false
   - Expected: late.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/page",
    "<html><head><title>Page</title><link rel='stylesheet' href='/slow.css'></head><body>Visible</body></html>"
)
expect(session.is_loading).to_equal(false)
expect(session.can_stop_loading()).to_equal(true)
val request = session.take_pending_request()
if val Some(pending) = request:
    expect(session.has_inflight_request(pending)).to_equal(true)

session.stop_loading()

expect(session.can_stop_loading()).to_equal(false)
expect(session.current_url).to_equal("https://example.com/page")
expect(session.current_body_html).to_contain("Visible")
expect(session.history.len()).to_equal(1)
if val Some(pending) = request:
    expect(session.has_inflight_request(pending)).to_equal(false)
    val late = session.commit_network_response(BrowserResponse.create(
        request_id: pending.id,
        kind: pending.kind,
        url: pending.url,
        status: 200,
        headers: "",
        body: "body { color: red; }",
        error: ""
    ))
    expect(late.is_err()).to_equal(true)
```

</details>

#### stops a pending document without destroying the active page

- var session = BrowserSession new
   - Expected: session.eval_script("var alive = 7; alive").is_ok() is true
   - Expected: started.is_ok() is true
- session stop loading
   - Expected: session.current_url equals `https://example.com/old`
   - Expected: session.current_title equals `Old`
   - Expected: session.current_body_html equals `old_body`
   - Expected: session.current_style_html equals `old_style`
   - Expected: session.history.len() equals `old_history_count`
- Ok
   - Expected: value equals `7.0`
- fail
   - Expected: late.is_err() is true
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BrowserSession.new()
session.open_html(
    "https://example.com/old",
    "<html><head><title>Old</title><style>#old { color: red; }</style></head><body><div id='old'>Visible</div></body></html>"
)
expect(session.eval_script("var alive = 7; alive").is_ok()).to_equal(true)
val old_body = session.current_body_html
val old_style = session.current_style_html
val old_history_count = session.history.len()

val started = session.begin_network_navigation(
    "https://example.com/slow", "GET", "", "", ""
)
expect(started.is_ok()).to_equal(true)
val request = session.take_pending_request()
session.stop_loading()

expect(session.current_url).to_equal("https://example.com/old")
expect(session.current_title).to_equal("Old")
expect(session.current_body_html).to_equal(old_body)
expect(session.current_style_html).to_equal(old_style)
expect(session.history.len()).to_equal(old_history_count)
match session.eval_script("alive"):
    Ok(JsValue.Number(value)):
        expect(value).to_equal(7.0)
    _:
        fail("Expected stopped navigation to preserve page runtime")

if val Some(pending) = request:
    val late = session.commit_network_response(BrowserResponse.create(
        request_id: pending.id,
        kind: pending.kind,
        url: pending.url,
        status: 200,
        headers: "",
        body: "<html><body>Late</body></html>",
        error: ""
    ))
    expect(late.is_err()).to_equal(true)
else:
    fail("Expected pending stylesheet request")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_controls_spec.spl` |
| Updated | 2026-07-30 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering BrowserSession primitive browser controls.
- BrowserSession primitive browser controls

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
