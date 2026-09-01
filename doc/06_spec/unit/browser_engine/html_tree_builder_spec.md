# Html Tree Builder Specification

> Tests covering HtmlTreeBuilder implicit closing, HtmlTreeBuilder scope-based insertion, HtmlTreeBuilder foster parenting.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Html Tree Builder Specification

## Scenarios

### HtmlTreeBuilder implicit closing

#### AC-2: wraps body content in html/head/body even when absent

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- AC-2: wraps body content in html/head/body even when absent
   - Expected: html equals `html`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: wraps body content in html/head/body even when absent")
val doc = _build("<p>hello</p>")
val html = _first_child_tag(doc)
expect(html).to_equal("html")
```

</details>

#### AC-2: implicitly closes <li> when next <li> starts

- AC-2: implicitly closes <li> when next <li> starts
   - Expected: count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: implicitly closes <li> when next <li> starts")
val doc = _build("<ul><li>a<li>b</ul>")
val ul = _find_nested(doc, "ul")
val count = _child_count(ul)
expect(count).to_equal(2)
```

</details>

#### AC-2: implicitly closes <p> when block element starts

- AC-2: implicitly closes <p> when block element starts
   - Expected: tag equals `div`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: implicitly closes <p> when block element starts")
val doc = _build("<p>text<div>block</div>")
val div = _find_nested(doc, "div")
val tag = be_dom_get_tag_name(div)
expect(tag).to_equal("div")
```

</details>

### HtmlTreeBuilder scope-based insertion

#### AC-2: inserts heading inside body scope

- AC-2: inserts heading inside body scope
   - Expected: be_dom_get_tag_name(h1) equals `h1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: inserts heading inside body scope")
val doc = _build("<h1>Title</h1>")
val h1 = _find_nested(doc, "h1")
expect(be_dom_get_tag_name(h1)).to_equal("h1")
```

</details>

#### AC-2: attribute preserved on parsed element

- AC-2: attribute preserved on parsed element
   - Expected: href equals `/path`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: attribute preserved on parsed element")
val doc = _build("<a href=\"/path\">link</a>")
val a = _find_nested(doc, "a")
val href = be_dom_get_attribute(a, "href")
expect(href).to_equal("/path")
```

</details>

#### AC-2: nested structure preserves parent-child relationship

- AC-2: nested structure preserves parent-child relationship
   - Expected: be_dom_get_tag_name(span) equals `span`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: nested structure preserves parent-child relationship")
val doc = _build("<div><p><span>text</span></p></div>")
val div = _find_nested(doc, "div")
val p = _find_first_by_tag(div, "p")
val span = _find_first_by_tag(p, "span")
expect(be_dom_get_tag_name(span)).to_equal("span")
```

</details>

### HtmlTreeBuilder foster parenting

#### AC-2: text before <table> is foster-parented before table

- AC-2: text before <table> is foster-parented before table


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: text before <table> is foster-parented before table")
val doc = _build("<table>misplaced text<tr><td>cell</td></tr></table>")
val body = _find_nested(doc, "body")
val count = _child_count(body)
expect(count).to_be_greater_than(0)
```

</details>

#### AC-2: <p> inside <table> is foster-parented outside table

- AC-2: <p> inside <table> is foster-parented outside table
   - Expected: be_dom_get_tag_name(p) equals `p`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: <p> inside <table> is foster-parented outside table")
val doc = _build("<table><p>para</p><tr><td>x</td></tr></table>")
val body = _find_nested(doc, "body")
val p = _find_first_by_tag(body, "p")
expect(be_dom_get_tag_name(p)).to_equal("p")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/unit/browser_engine/html_tree_builder_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering HtmlTreeBuilder implicit closing, HtmlTreeBuilder scope-based insertion, HtmlTreeBuilder foster parenting.
- HtmlTreeBuilder implicit closing
- HtmlTreeBuilder scope-based insertion
- HtmlTreeBuilder foster parenting

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `f529ccf9facdcc7427d8aa71b7a6ac57df52e738ab06637473f3d155fe3115ba`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f529ccf9facdcc7427d8aa71b7a6ac57df52e738ab06637473f3d155fe3115ba`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f529ccf9facdcc7427d8aa71b7a6ac57df52e738ab06637473f3d155fe3115ba`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/browser_engine/html_tree_builder_spec.spl
mirror: doc/06_spec/unit/browser_engine/html_tree_builder_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/browser_engine/html_tree_builder_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/browser_engine/html_tree_builder_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/browser_engine/html_tree_builder_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/browser_engine/html_tree_builder_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2: wraps body content in html/head/body even when absent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/browser_engine/html_tree_builder_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2: implicitly closes <li> when next <li> starts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/browser_engine/html_tree_builder_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2: implicitly closes <p> when block element starts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
