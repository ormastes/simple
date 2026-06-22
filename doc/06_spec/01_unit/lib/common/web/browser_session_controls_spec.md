# Browser Session Controls Specification

> <details>

<!-- sdn-diagram:id=browser_session_controls_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_session_controls_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_session_controls_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_session_controls_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Controls Specification

## Scenarios

### BrowserSession primitive browser controls

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

#### dequeues pending network requests in insertion order

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
   - Expected: request.url equals `https://example.com/one`
   - Expected: request.method equals `GET`
- fail
- Some
   - Expected: request.url equals `https://example.com/two`
   - Expected: request.method equals `POST`
   - Expected: request.body equals `body`
- fail
   - Expected: session.has_pending_requests() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
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
        expect(request.url).to_equal("https://example.com/one")
        expect(request.method).to_equal("GET")
    nil =>
        fail("Expected first pending request")
match session.take_pending_request():
    Some(request) =>
        expect(request.url).to_equal("https://example.com/two")
        expect(request.method).to_equal("POST")
        expect(request.body).to_equal("body")
    nil =>
        fail("Expected second pending request")

expect(session.has_pending_requests()).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_controls_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserSession primitive browser controls

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
