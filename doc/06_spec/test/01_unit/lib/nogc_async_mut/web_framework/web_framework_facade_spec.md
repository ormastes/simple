# Web Framework Facade Re-export Specification

> Verifies that the `nogc_async_mut.web_framework` facade re-exports the pure asset, CSRF, form parsing, RBAC, and tracing helpers used by web applications.

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

# Web Framework Facade Re-export Specification

Verifies that the `nogc_async_mut.web_framework` facade re-exports the pure asset, CSRF, form parsing, RBAC, and tracing helpers used by web applications.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WEB-FRAMEWORK-FACADE-001 |
| Category | Web Framework |
| Difficulty | 2/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/lib/nogc_async_mut/web_framework/web_framework_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that the `nogc_async_mut.web_framework` facade re-exports the pure
asset, CSRF, form parsing, RBAC, and tracing helpers used by web applications.

## Syntax

The spec imports helpers through their facade modules and checks representative
return values for each helper family.

## Examples

`trace_id_from_hex` must parse a valid 128-bit trace id and expose the original
low word through the returned `TraceId`.

## Scenarios

### nogc_async_mut web_framework facades

#### re-exports pure web framework helpers

1. Some

2. nil: fail
   - Expected: span_id_to_hex(SpanId(value: 3)) equals `0000000000000003`
   - Expected: join_texts(["a", "b", "c"], ",") equals `a,b,c`


<details>
<summary>Executable SPipe</summary>

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
    nil: fail("trace_id_from_hex returned nil for a valid 128-bit trace id")
expect(span_id_to_hex(SpanId(value: 3))).to_equal("0000000000000003")
expect(join_texts(["a", "b", "c"], ",")).to_equal("a,b,c")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
