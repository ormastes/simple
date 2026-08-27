# Dom Accessors Specification

> Tests covering Browser engine DOM accessors.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dom Accessors Specification

## Scenarios

### Browser engine DOM accessors

#### collects recursive text content without changing visible text

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- collects recursive text content without changing visible text
   - Expected: be_dom_get_text_content(root) equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("collects recursive text content without changing visible text")
val span = BeDomNode(
    node_id: 2,
    tag_name: "span",
    data: "",
    attributes: {},
    style: _node(0, "x").style,
    children: [_text(3, "world")],
    parent_id: 1)
val root = BeDomNode(
    node_id: 1,
    tag_name: "div",
    data: "",
    attributes: {},
    style: _node(0, "x").style,
    children: [_text(4, "hello "), span],
    parent_id: -1)

expect(be_dom_get_text_content(root)).to_equal("hello world")
```

</details>

#### finds nodes by id and tag in depth-first order

- finds nodes by id and tag in depth-first order
   - Expected: found.tag_name equals `p`
   - Expected: paragraphs.len() equals `3`
   - Expected: paragraphs[0].node_id equals `3`
   - Expected: paragraphs[1].node_id equals `4`
   - Expected: paragraphs[2].node_id equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("finds nodes by id and tag in depth-first order")
val style = _node(0, "x").style
val section = BeDomNode(
    node_id: 2,
    tag_name: "section",
    data: "",
    attributes: {},
    style: style,
    children: [_node(3, "p"), _node(4, "p")],
    parent_id: 1)
val root = BeDomNode(
    node_id: 1,
    tag_name: "div",
    data: "",
    attributes: {},
    style: style,
    children: [section, _node(5, "p")],
    parent_id: -1)

match be_dom_find_by_id(root, 4):
    Some(found) =>
        expect(found.tag_name).to_equal("p")
    nil =>
        fail("Expected node id 4")

val paragraphs = be_dom_find_by_tag(root, "p")
expect(paragraphs.len()).to_equal(3)
expect(paragraphs[0].node_id).to_equal(3)
expect(paragraphs[1].node_id).to_equal(4)
expect(paragraphs[2].node_id).to_equal(5)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_accessors_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Browser engine DOM accessors.
- Browser engine DOM accessors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a5d8cf5e2c082bcb6b6a57d363cc3b29f5e460271dcc5256791bd21eb4057580`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a5d8cf5e2c082bcb6b6a57d363cc3b29f5e460271dcc5256791bd21eb4057580`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a5d8cf5e2c082bcb6b6a57d363cc3b29f5e460271dcc5256791bd21eb4057580`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_accessors_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_accessors_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_accessors_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_accessors_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_accessors_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_accessors_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'collects recursive text content without changing visible text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_accessors_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds nodes by id and tag in depth-first order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
