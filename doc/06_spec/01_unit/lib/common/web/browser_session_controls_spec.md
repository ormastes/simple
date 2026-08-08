# Browser Session Controls Specification

> Tests covering BrowserSession primitive browser controls.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

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

#### replays the committed request on reload without growing history

- Commit a direct POST and reload its exact request
   - Expected: reload method equals `POST`
   - Expected: reload body equals `name=simple`
   - Expected: reload content type equals `application/x-www-form-urlencoded`
   - Expected: history remains one entry
- Preserve replay metadata through Back and Forward traversal
   - Expected: traversal back to the POST entry reloads its exact request
- Preserve POST across 307 and 308 redirects
   - Expected: final and reload requests preserve POST, body, and content type
- Keep redirect-rewritten and direct GET reloads body-free
   - Expected: 301, 302, and 303 reload as body-free GET
   - Expected: a direct GET remains a body-free GET
- Charge all stored request metadata to the bounded history budget
   - Expected: twelve 4 MiB entries remain within the 50 MiB retained budget


<details>
<summary>Executable SSpec</summary>

Runnable source: 127 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Commit a direct POST and reload its exact request")
var direct = BrowserSession.new()
expect(direct.begin_network_navigation(
    "https://reload.test/form", "POST", "",
    "name=simple", "application/x-www-form-urlencoded"
).is_ok()).to_equal(true)
val direct_request = direct.take_pending_request().unwrap()
expect(direct.commit_network_response(BrowserResponse.create(
    direct_request.id, "document", direct_request.url,
    200, "", "<html><body>posted</body></html>", ""
)).is_ok()).to_equal(true)
expect(direct.history.len()).to_equal(1)
expect(direct.reload().is_ok()).to_equal(true)
val direct_reload = direct.take_pending_request().unwrap()
expect(direct_reload.method).to_equal("POST")
expect(direct_reload.body).to_equal("name=simple")
expect(direct_reload.content_type).to_equal(
    "application/x-www-form-urlencoded"
)
expect(direct.commit_network_response(BrowserResponse.create(
    direct_reload.id, "document", direct_reload.url,
    200, "", "<html><body>posted again</body></html>", ""
)).is_ok()).to_equal(true)
expect(direct.history.len()).to_equal(1)

step("Preserve replay metadata through Back and Forward traversal")
expect(direct.begin_network_navigation(
    "https://reload.test/next", "GET", "", "", ""
).is_ok()).to_equal(true)
val next_request = direct.take_pending_request().unwrap()
expect(direct.commit_network_response(BrowserResponse.create(
    next_request.id, "document", next_request.url,
    200, "", "<html><body>next</body></html>", ""
)).is_ok()).to_equal(true)
expect(direct.go_back().is_ok()).to_equal(true)
expect(direct.go_forward().is_ok()).to_equal(true)
expect(direct.go_back().is_ok()).to_equal(true)
expect(direct.reload().is_ok()).to_equal(true)
val traversal_reload = direct.take_pending_request().unwrap()
expect(traversal_reload.method).to_equal("POST")
expect(traversal_reload.body).to_equal("name=simple")
expect(traversal_reload.content_type).to_equal(
    "application/x-www-form-urlencoded"
)

step("Preserve POST across 307 and 308 redirects")
for status in [307, 308]:
    var preserved = BrowserSession.new()
    expect(preserved.begin_network_navigation(
        "https://reload.test/start-{status}", "POST", "",
        "status={status}", "text/plain"
    ).is_ok()).to_equal(true)
    val initial = preserved.take_pending_request().unwrap()
    expect(preserved.commit_network_response(BrowserResponse.create(
        initial.id, "document", initial.url, status,
        "Location: /final-{status}", "", ""
    )).is_ok()).to_equal(true)
    val redirected = preserved.take_pending_request().unwrap()
    expect(redirected.method).to_equal("POST")
    expect(preserved.commit_network_response(BrowserResponse.create(
        redirected.id, "document", redirected.url,
        200, "", "<html><body>final</body></html>", ""
    )).is_ok()).to_equal(true)
    expect(preserved.reload().is_ok()).to_equal(true)
    val replay = preserved.take_pending_request().unwrap()
    expect(replay.method).to_equal("POST")
    expect(replay.body).to_equal("status={status}")
    expect(replay.content_type).to_equal("text/plain")

step("Keep redirect-rewritten and direct GET reloads body-free")
for status in [301, 302, 303]:
    var rewritten = BrowserSession.new()
    expect(rewritten.begin_network_navigation(
        "https://reload.test/rewrite-{status}", "POST", "",
        "discarded", "text/plain"
    ).is_ok()).to_equal(true)
    val initial = rewritten.take_pending_request().unwrap()
    expect(rewritten.commit_network_response(BrowserResponse.create(
        initial.id, "document", initial.url, status,
        "Location: /get-{status}", "", ""
    )).is_ok()).to_equal(true)
    val redirected = rewritten.take_pending_request().unwrap()
    expect(redirected.method).to_equal("GET")
    expect(rewritten.commit_network_response(BrowserResponse.create(
        redirected.id, "document", redirected.url,
        200, "", "<html><body>get</body></html>", ""
    )).is_ok()).to_equal(true)
    expect(rewritten.reload().is_ok()).to_equal(true)
    val replay = rewritten.take_pending_request().unwrap()
    expect(replay.method).to_equal("GET")
    expect(replay.body).to_equal("")
    expect(replay.content_type).to_equal("")

var get_session = BrowserSession.new()
expect(get_session.begin_network_navigation(
    "https://reload.test/get", "GET", "", "", ""
).is_ok()).to_equal(true)
val get_request = get_session.take_pending_request().unwrap()
expect(get_session.commit_network_response(BrowserResponse.create(
    get_request.id, "document", get_request.url,
    200, "", "<html><body>get</body></html>", ""
)).is_ok()).to_equal(true)
expect(get_session.reload().is_ok()).to_equal(true)
val get_reload = get_session.take_pending_request().unwrap()
expect(get_reload.method).to_equal("GET")
expect(get_reload.body).to_equal("")
expect(get_reload.content_type).to_equal("")

step("Charge all stored request metadata to the bounded history budget")
val one_mib = "x".repeat(1024 * 1024)
var bounded: [BrowserHistoryEntry] = []
var index = 0
while index < 27:
    bounded = browser_history_push_bounded(
        bounded, bounded.len() - 1,
        BrowserHistoryEntry.create_with_request(
            "https://reload.test/{index}", "", one_mib, "",
            one_mib, one_mib, one_mib
        )
    )
    index = index + 1
expect(bounded.len()).to_equal(12)
expect(bounded[11].request_method.len()).to_equal(one_mib.len())
expect(bounded[11].request_body.len()).to_equal(one_mib.len())
expect(bounded[11].request_content_type.len()).to_equal(
    one_mib.len()
)
```

</details>

#### keeps synthetic history URLs and oversized bodies non-replayable

- Make pushState and replaceState synthetic URLs body-free
   - Expected: both history entries and reload requests use GET with no body
- Reject oversized replay metadata before navigation state mutates
   - Expected: URL, history, loading, and pending-request state remain unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 54 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Make pushState and replaceState synthetic URLs body-free")
for mode in ["pushState", "replaceState"]:
    var session = BrowserSession.new()
    expect(session.begin_network_navigation(
        "https://reload.test/form-{mode}", "POST", "",
        "secret={mode}", "application/x-www-form-urlencoded"
    ).is_ok()).to_equal(true)
    val request = session.take_pending_request().unwrap()
    expect(session.commit_network_response(BrowserResponse.create(
        request.id, "document", request.url, 200, "",
        "<html><body><script>var ready = true;</script></body></html>",
        ""
    )).is_ok()).to_equal(true)
    expect(session.eval_script(
        "history.{mode}(1, '', '/synthetic-{mode}')"
    ).is_ok()).to_equal(true)
    val synthetic = session.history[session.current_index]
    expect(synthetic.request_method).to_equal("GET")
    expect(synthetic.request_body).to_equal("")
    expect(synthetic.request_content_type).to_equal("")
    expect(session.reload().is_ok()).to_equal(true)
    val reload = session.take_pending_request().unwrap()
    expect(reload.url).to_equal(
        "https://reload.test/synthetic-{mode}"
    )
    expect(reload.method).to_equal("GET")
    expect(reload.body).to_equal("")
    expect(reload.content_type).to_equal("")

step("Reject oversized replay metadata before navigation state mutates")
var bounded = BrowserSession.new()
expect(bounded.open_html(
    "https://reload.test/keep",
    "<html><body>keep</body></html>"
).is_ok()).to_equal(true)
val before_url = bounded.current_url
val before_index = bounded.current_index
val before_history = bounded.history.len()
val before_loading = bounded.is_loading
val before_pending = bounded.pending_request_count()
val oversized = "x".repeat(50 * 1024 * 1024 + 1)
expect(bounded.begin_network_navigation(
    "https://reload.test/rejected", "POST", "",
    "", oversized
).is_err()).to_equal(true)
expect(bounded.begin_network_navigation(
    "https://reload.test/rejected", "POST", "",
    "x", oversized.slice(0, 50 * 1024 * 1024 - 4)
).is_err()).to_equal(true)
expect(bounded.current_url).to_equal(before_url)
expect(bounded.current_index).to_equal(before_index)
expect(bounded.history.len()).to_equal(before_history)
expect(bounded.is_loading).to_equal(before_loading)
expect(bounded.pending_request_count()).to_equal(before_pending)
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
| Updated | 2026-07-31 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering BrowserSession primitive browser controls.
- BrowserSession primitive browser controls

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
