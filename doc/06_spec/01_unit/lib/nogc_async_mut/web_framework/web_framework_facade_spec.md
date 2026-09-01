# Web Framework Facade Re-export Specification

> Verifies that the `nogc_async_mut.web_framework` facade re-exports the pure asset, CSRF, form parsing, RBAC, and tracing helpers used by web applications.

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
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports pure web framework helpers
   - Expected: pipeline.resolve("/css/app.css") equals `/css/app.css`
   - Expected: pipeline.asset_path("js/app.js") equals `/assets/js/app.js`
   - Expected: insert_fingerprint("/css/app.css", "a1b2c3d4") equals `/css/app-a1b2c3d4.css`
   - Expected: csrf_hidden_field("token") contains `_csrf_token`
   - Expected: csrf_meta_tag("token") contains `csrf-token`
   - Expected: detect_content_type("application/x-www-form-urlencoded; charset=utf-8") equals `url_encoded`
   - Expected: detect_content_type("multipart/form-data; boundary=abc") equals `multipart`
   - Expected: extract_header_param("form-data; name=\"upload\"; filename=\"a.txt\"", "filename") equals `a.txt`
   - Expected: field.name equals `title`
   - Expected: has_permission(role, "users", "write") is true
   - Expected: has_permission(role, "users", "read") is false
   - Expected: i64_to_hex_padded(255, 4) equals `00ff`
   - Expected: hex_char_to_i64("f") equals `15`
   - Expected: hex_to_i64("10") equals `16`
   - Expected: trace_id_to_hex(trace_id) equals `00000000000000010000000000000002`
   - Expected: span_id_to_hex(SpanId(value: 3)) equals `0000000000000003`
   - Expected: join_texts(["a", "b", "c"], ",") equals `a,b,c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports pure web framework helpers")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c871af63237769078d0b7e4c6463bb6bf188aa97674a9f999df9d5252574e309`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c871af63237769078d0b7e4c6463bb6bf188aa97674a9f999df9d5252574e309`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c871af63237769078d0b7e4c6463bb6bf188aa97674a9f999df9d5252574e309`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/nogc_async_mut/web_framework/web_framework_facade_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/web_framework/web_framework_facade_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/web_framework/web_framework_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/web_framework/web_framework_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/web_framework/web_framework_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_async_mut/web_framework/web_framework_facade_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports pure web framework helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
