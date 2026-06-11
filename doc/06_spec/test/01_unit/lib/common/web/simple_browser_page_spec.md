# Simple Browser Page Specification

> 1. Some

<!-- sdn-diagram:id=simple_browser_page_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_browser_page_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_browser_page_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_browser_page_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Browser Page Specification

## Scenarios

### Simple browser page adapter

#### collects anchor and form targets from rendered html

1. Some
   - Expected: target.action equals `https://example.com/next`

2. fail

3. Some

4. fail

5. Some
   - Expected: target.action equals `https://example.com/search`

6. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><a href='/next'>Next</a><form action='/search' method='get'><input name='q' value='hello'><button>Go</button></form></body></html>"
val page = simple_browser_render_remote_page("https://example.com/start", html, 320, 240)

val anchor_target = _find_target(page, "anchor")
match anchor_target:
    Some(target) =>
        expect(target.action).to_equal("https://example.com/next")
        expect(target.width).to_be_greater_than(0)
    nil =>
        fail("Expected rendered page to expose an anchor target")

val field_target = _find_target(page, "field")
match field_target:
    Some(target) =>
        expect(target.field_key.len()).to_be_greater_than(0)
    nil =>
        fail("Expected rendered page to expose a field target")

val submit_target = _find_target(page, "submit")
match submit_target:
    Some(target) =>
        expect(target.form_key.len()).to_be_greater_than(0)
        expect(target.action).to_equal("https://example.com/search")
    nil =>
        fail("Expected rendered page to expose a submit target")
```

</details>

#### preserves field edits and builds GET submission urls

1. Some

2. Some
   - Expected: next_url equals `https://example.com/search?q=cats+and+dogs`

3. fail

4. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><form action='/search' method='get'><input name='q' value='hello'><button>Go</button></form></body></html>"
val page = simple_browser_render_remote_page("https://example.com/start", html, 320, 240)

val field_target = _find_target(page, "field")
val submit_target = _find_target(page, "submit")
match field_target:
    Some(field_hit) =>
        match submit_target:
            Some(submit_hit) =>
                val edited = simple_browser_set_field_value(page, field_hit.field_key, "cats and dogs")
                val next_url = simple_browser_submit_get_url(edited, submit_hit.form_key, submit_hit.action)
                expect(next_url).to_equal("https://example.com/search?q=cats+and+dogs")
            nil =>
                fail("Expected rendered GET form to expose a submit target")
    nil =>
        fail("Expected rendered GET form to expose a field target")
```

</details>

#### builds POST submission requests for post forms

1. Some

2. Some
   - Expected: request.method equals `POST`
   - Expected: request.url equals `https://example.com/submit`
   - Expected: request.body equals `q=cats+and+dogs`
   - Expected: request.content_type equals `application/x-www-form-urlencoded`

3. fail

4. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><form action='/submit' method='post'><input name='q' value='hello'><button>Save</button></form></body></html>"
val page = simple_browser_render_remote_page("https://example.com/start", html, 320, 240)

val field_target = _find_target(page, "field")
val submit_target = _find_target(page, "submit")
match field_target:
    Some(field_hit) =>
        match submit_target:
            Some(submit_hit) =>
                val edited = simple_browser_set_field_value(page, field_hit.field_key, "cats and dogs")
                val request = simple_browser_submit_request(edited, submit_hit.form_key, submit_hit.action, submit_hit.method)
                expect(request.method).to_equal("POST")
                expect(request.url).to_equal("https://example.com/submit")
                expect(request.body).to_equal("q=cats+and+dogs")
                expect(request.content_type).to_equal("application/x-www-form-urlencoded")
            nil =>
                fail("Expected rendered POST form to expose a submit target")
    nil =>
        fail("Expected rendered POST form to expose a field target")
```

</details>

#### hit tests the rendered target rectangles

1. Some

2. Some
   - Expected: resolved.kind equals `anchor`
   - Expected: resolved.action equals `https://example.com/go`

3. fail

4. fail


<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><a href='/go'>Go</a></body></html>"
val page = simple_browser_render_remote_page("https://example.com/base", html, 320, 240)
val anchor_target = _find_target(page, "anchor")
match anchor_target:
    Some(target) =>
        val hit = simple_browser_hit_target(page, target.x + 1, target.y + 1)
        match hit:
            Some(resolved) =>
                expect(resolved.kind).to_equal("anchor")
                expect(resolved.action).to_equal("https://example.com/go")
            nil =>
                fail("Expected hit test to resolve the anchor target rectangle")
    nil =>
        fail("Expected rendered page to expose an anchor target for hit testing")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/simple_browser_page_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Simple browser page adapter

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
