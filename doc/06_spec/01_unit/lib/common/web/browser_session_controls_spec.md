# Browser Session Controls Specification

> 1. var session = BrowserSession new

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
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Controls Specification

## Scenarios

### BrowserSession primitive browser controls

#### navigates to the configured home page through registered resources

1. var session = BrowserSession new

2. session register resource

3. session open html

4. session set home url

5. Ok
   - Expected: session.current_url equals `https://example.com/home`
   - Expected: session.current_title equals `Home`

6. Err
   - Expected: "unexpected go_home error: {e}" equals ``


<details>
<summary>Executable SPipe</summary>

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

1. var session = BrowserSession new

2. session open html

3. session add current favorite
   - Expected: session.is_favorite("https://example.com/app") is true
   - Expected: session.favorite_title("https://example.com/app") ?? "" equals `App`

4. session add favorite

5. session add favorite
   - Expected: session.favorite_links.len() equals `2`
   - Expected: session.favorite_title("https://example.com/docs") ?? "" equals `Docs v2`

6. session remove favorite
   - Expected: session.is_favorite("https://example.com/app") is false
   - Expected: session.favorite_links.len() equals `1`


<details>
<summary>Executable SPipe</summary>

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
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
