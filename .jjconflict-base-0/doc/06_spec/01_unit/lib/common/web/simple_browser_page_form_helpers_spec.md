# Simple Browser Page Form Helpers Specification

> <details>

<!-- sdn-diagram:id=simple_browser_page_form_helpers_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_browser_page_form_helpers_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_browser_page_form_helpers_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_browser_page_form_helpers_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Browser Page Form Helpers Specification

## Scenarios

### Simple browser page form helpers

#### hit-tests target rectangles using stable target ordering

- Some
   - Expected: target.kind equals `anchor`
   - Expected: target.action equals `https://example.com/go`
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page = _page([], [_target("anchor", 10, 20, 40, 12), _target("submit", 80, 20, 30, 12)])

val hit = simple_browser_hit_target(page, 12, 22)

match hit:
    Some(target) =>
        expect(target.kind).to_equal("anchor")
        expect(target.action).to_equal("https://example.com/go")
    nil =>
        fail("Expected hit target")
```

</details>

#### looks up field values and form keys by stable field keys

-  field
-  field
   - Expected: simple_browser_field_value(page, "field:1") equals `hello`
   - Expected: simple_browser_field_form_key(page, "field:1") equals `form:search`
   - Expected: simple_browser_field_value(page, "missing") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page = _page([
    _field("field:1", "form:search", "GET", "q", "hello", false),
    _field("field:2", "form:search", "GET", "skip", "x", true)
], [])

expect(simple_browser_field_value(page, "field:1")).to_equal("hello")
expect(simple_browser_field_form_key(page, "field:1")).to_equal("form:search")
expect(simple_browser_field_value(page, "missing")).to_equal("")
```

</details>

#### serializes GET and POST form pairs while skipping unsupported fields

-  field
-  field
-  field
   - Expected: get_url equals `https://example.com/search?q=cats+and+dogs`
   - Expected: post.method equals `POST`
   - Expected: post.url equals `https://example.com/search`
   - Expected: post.body equals `q=cats+and+dogs`
   - Expected: post.content_type equals `application/x-www-form-urlencoded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page = _page([
    _field("field:1", "form:search", "GET", "q", "cats and dogs", false),
    _field("field:2", "form:search", "GET", "skip", "x", true),
    _field("field:3", "form:search", "GET", "", "unnamed", false)
], [])

val get_url = simple_browser_submit_get_url(page, "form:search", "https://example.com/search")
val post = simple_browser_submit_request(page, "form:search", "https://example.com/search", "POST")

expect(get_url).to_equal("https://example.com/search?q=cats+and+dogs")
expect(post.method).to_equal("POST")
expect(post.url).to_equal("https://example.com/search")
expect(post.body).to_equal("q=cats+and+dogs")
expect(post.content_type).to_equal("application/x-www-form-urlencoded")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/simple_browser_page_form_helpers_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Simple browser page form helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
