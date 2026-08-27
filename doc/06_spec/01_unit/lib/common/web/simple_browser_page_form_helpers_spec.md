# Simple Browser Page Form Helpers Specification

> Tests covering Simple browser page form helpers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Browser Page Form Helpers Specification

## Scenarios

### Simple browser page form helpers

#### hit-tests target rectangles using stable target ordering

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- hit-tests target rectangles using stable target ordering
   - Expected: target.kind equals `anchor`
   - Expected: target.action equals `https://example.com/go`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hit-tests target rectangles using stable target ordering")
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

- looks up field values and form keys by stable field keys
   - Expected: simple_browser_field_value(page, "field:1") equals `hello`
   - Expected: simple_browser_field_form_key(page, "field:1") equals `form:search`
   - Expected: simple_browser_field_value(page, "missing") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("looks up field values and form keys by stable field keys")
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

- serializes GET and POST form pairs while skipping unsupported fields
   - Expected: get_url equals `https://example.com/search?q=cats+and+dogs`
   - Expected: post.method equals `POST`
   - Expected: post.url equals `https://example.com/search`
   - Expected: post.body equals `q=cats+and+dogs`
   - Expected: post.content_type equals `application/x-www-form-urlencoded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes GET and POST form pairs while skipping unsupported fields")
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

#### uses canonical textarea newline encoding for page adapter forms

- uses canonical textarea newline encoding for page adapter forms


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses canonical textarea newline encoding for page adapter forms")
val textarea = SimpleBrowserField(
    key: "field:note",
    form_key: "form:profile",
    form_method: "POST",
    name: "note",
    tag: "textarea",
    input_type: "textarea",
    value: "LF\nCR\rCRLF\r\n한",
    placeholder: "",
    x: 0,
    y: 0,
    width: 10,
    height: 10,
    unsupported: false
)
val request = simple_browser_submit_request(
    _page([textarea], []), "form:profile",
    "https://example.com/save", "POST"
)

expect(request.body).to_equal(
    "note=LF%0D%0ACR%0D%0ACRLF%0D%0A%ED%95%9C"
)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/simple_browser_page_form_helpers_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Simple browser page form helpers.
- Simple browser page form helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `347851c393215b3fb64a540e1be5c26ed3d05cf8361c69373537d0d8da377d5b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `347851c393215b3fb64a540e1be5c26ed3d05cf8361c69373537d0d8da377d5b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `347851c393215b3fb64a540e1be5c26ed3d05cf8361c69373537d0d8da377d5b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/web/simple_browser_page_form_helpers_spec.spl
mirror: doc/06_spec/01_unit/lib/common/web/simple_browser_page_form_helpers_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/web/simple_browser_page_form_helpers_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/web/simple_browser_page_form_helpers_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/web/simple_browser_page_form_helpers_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hit-tests target rectangles using stable target ordering' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/web/simple_browser_page_form_helpers_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'looks up field values and form keys by stable field keys' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/web/simple_browser_page_form_helpers_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'serializes GET and POST form pairs while skipping unsupported fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
