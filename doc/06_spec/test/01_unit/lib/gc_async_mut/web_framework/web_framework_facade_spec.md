# Web Framework Facade Specification

> <details>

<!-- sdn-diagram:id=web_framework_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=web_framework_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

web_framework_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=web_framework_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Framework Facade Specification

## Scenarios

### gc_async_mut web_framework facades

#### re-exports pure web framework helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pipeline = AssetPipeline.new("public", false)
expect(pipeline.resolve("/css/app.css")).to_equal("/css/app.css")
expect(pipeline.asset_path("js/app.js")).to_equal("/assets/js/app.js")
expect(insert_fingerprint("/css/app.css", "a1b2c3d4")).to_equal("/css/app-a1b2c3d4.css")

expect(csrf_hidden_field("token").contains("_csrf_token")).to_equal(true)
expect(csrf_meta_tag("token").contains("csrf-token")).to_equal(true)

expect(detect_content_type("application/x-www-form-urlencoded; charset=utf-8")).to_equal("url_encoded")
expect(detect_content_type("multipart/form-data; boundary=abc")).to_equal("multipart")
expect(extract_header_param("form-data; name=\"upload\"; filename=\"a.txt\"", "filename")).to_equal("a.txt")
val field = MultipartField(name: "title", value: "Hello", filename: "", content_type: "")
expect(field.name).to_equal("title")

val role = Role(name: "admin", permissions: [Permission(resource: "users", action: "write")])
expect(has_permission(role, "users", "write")).to_equal(true)
expect(has_permission(role, "users", "read")).to_equal(false)

expect(i64_to_hex_padded(255, 4)).to_equal("00ff")
expect(hex_char_to_i64("f")).to_equal(15)
expect(hex_to_i64("10")).to_equal(16)
val trace_id = TraceId(high: 1, low: 2)
expect(trace_id_to_hex(trace_id)).to_equal("00000000000000010000000000000002")
match trace_id_from_hex("00000000000000010000000000000002"):
    Some(parsed): expect(parsed.low).to_equal(2)
    nil: expect(false).to_equal(true)
expect(span_id_to_hex(SpanId(value: 3))).to_equal("0000000000000003")
expect(join_texts(["a", "b", "c"], ",")).to_equal("a,b,c")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/web_framework/web_framework_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut web_framework facades

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
