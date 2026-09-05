# Simple Browser Page Specification

> Tests covering Simple browser page adapter.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Browser Page Specification

## Scenarios

### Simple browser page adapter

#### collects anchor and form targets from rendered html

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- collects anchor and form targets from rendered html
   - Expected: target.action equals `https://example.com/next`
   - Expected: false is true
   - Expected: false is true
   - Expected: target.action equals `https://example.com/search`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("collects anchor and form targets from rendered html")
val html = "<html><body><a href='/next'>Next</a><form action='/search' method='get'><input name='q' value='hello'><button>Go</button></form></body></html>"
val page = simple_browser_render_remote_page("https://example.com/start", html, 320, 240)

val anchor_target = _find_target(page, "anchor")
match anchor_target:
    Some(target) =>
        expect(target.action).to_equal("https://example.com/next")
        expect(target.width).to_be_greater_than(0)
    nil =>
        expect(false).to_equal(true)

val field_target = _find_target(page, "field")
match field_target:
    Some(target) =>
        expect(target.field_key.len()).to_be_greater_than(0)
    nil =>
        expect(false).to_equal(true)

val submit_target = _find_target(page, "submit")
match submit_target:
    Some(target) =>
        expect(target.form_key.len()).to_be_greater_than(0)
        expect(target.action).to_equal("https://example.com/search")
    nil =>
        expect(false).to_equal(true)
```

</details>

#### preserves field edits and builds GET submission urls

- preserves field edits and builds GET submission urls
   - Expected: next_url equals `https://example.com/search?q=cats+and+dogs`
   - Expected: false is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves field edits and builds GET submission urls")
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
                expect(false).to_equal(true)
    nil =>
        expect(false).to_equal(true)
```

</details>

#### builds POST submission requests for post forms

- builds POST submission requests for post forms
   - Expected: request.method equals `POST`
   - Expected: request.url equals `https://example.com/submit`
   - Expected: request.body equals `q=cats+and+dogs`
   - Expected: request.content_type equals `application/x-www-form-urlencoded`
   - Expected: false is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds POST submission requests for post forms")
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
                expect(false).to_equal(true)
    nil =>
        expect(false).to_equal(true)
```

</details>

#### hit tests the rendered target rectangles

- hit tests the rendered target rectangles
   - Expected: resolved.kind equals `anchor`
   - Expected: resolved.action equals `https://example.com/go`
   - Expected: false is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hit tests the rendered target rectangles")
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
                expect(false).to_equal(true)
    nil =>
        expect(false).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/web/simple_browser_page_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Simple browser page adapter.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `47783a262238719aa27306510becd2a552086d4abba53ad17e886f738d57e6d8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `47783a262238719aa27306510becd2a552086d4abba53ad17e886f738d57e6d8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `47783a262238719aa27306510becd2a552086d4abba53ad17e886f738d57e6d8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/web/simple_browser_page_spec.spl
mirror: doc/06_spec/unit/lib/common/web/simple_browser_page_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/web/simple_browser_page_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/web/simple_browser_page_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/web/simple_browser_page_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'collects anchor and form targets from rendered html' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/web/simple_browser_page_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves field edits and builds GET submission urls' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/web/simple_browser_page_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds POST submission requests for post forms' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
