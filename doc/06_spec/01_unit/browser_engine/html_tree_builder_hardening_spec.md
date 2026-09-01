# HTML Tree Builder — Defensive Limits

> Purpose: Prove that HtmlTreeBuilder depth cap.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HTML Tree Builder — Defensive Limits

Purpose: Prove that HtmlTreeBuilder depth cap.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser Engine / HTML Parsing |
| Status | Implemented |
| Source | `test/01_unit/browser_engine/html_tree_builder_hardening_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that HtmlTreeBuilder depth cap.
Audience: compiler and tooling engineers who maintain this spec.
# HTML Tree Builder — Defensive Limits

**Category:** Browser Engine / HTML Parsing
**Status:** Implemented

## Overview

`html_tree_builder.spl` caps open-element depth at `HTML_MAX_TREE_DEPTH`
(512) and total element-node creation at `HTML_MAX_NODES` (65536), matching
Blink/WebKit defensive limits. A hostile/deeply-nested document must still
parse to completion (never abort, never drop already-open content) — once
the depth cap is hit, further nesting flattens into siblings at the cap
level instead of recursing deeper.

## Scenarios

### HtmlTreeBuilder depth cap

#### deeply nested markup parses to completion with bounded depth

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Build 2000 levels of nested <div> markup
- Parse the markup into a DOM tree
- Then measured tree depth stays within the HTML_MAX_TREE_DEPTH cap
- Then no content was dropped — all 2000 divs are still present as siblings
   - Expected: measured_count equals `2000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-BROWSER-ENGINE-HTML-TREE-BUILDER-HARDENING-SPEC-SPL-001
step("Build 2000 levels of nested <div> markup")
val html = build_nested_markup(2000)

step("Parse the markup into a DOM tree")
val doc = html_tree_builder_build(html)

step("Then measured tree depth stays within the HTML_MAX_TREE_DEPTH cap")
val measured_depth = _max_depth(doc)
expect(measured_depth).to_be_less_than(513)

step("Then no content was dropped — all 2000 divs are still present as siblings")
val measured_count = _count_by_tag(doc, "div")
expect(measured_count).to_equal(2000)  # oracle: 2000 — named expected value from the requirement
```

</details>

### HtmlTreeBuilder node cap

#### accepts the exact limit and truncates the next node

- accepts the exact limit and truncates the next node
- Verify: accepts the exact limit and truncates the next node
   - Expected: _count_by_tag(overflow.doc, "p") equals `1`
   - Expected: _count_by_tag(overflow.doc, "b") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("accepts the exact limit and truncates the next node")
step("Verify: accepts the exact limit and truncates the next node")
val exact = html_tree_builder_build_with_scripts_limit("<p>x</p>", 6)
val overflow = html_tree_builder_build_with_scripts_limit(
    "<p>x</p><b>later</b>", 6
)

expect(exact.truncated).to_be(false)
expect(overflow.truncated).to_be(true)
expect(_count_by_tag(overflow.doc, "p")).to_equal(1)
expect(_count_by_tag(overflow.doc, "b")).to_equal(0)
```

</details>

#### propagates tokenizer truncation to document admission

- propagates tokenizer truncation to document admission
- Verify: propagates tokenizer truncation to document admission


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("propagates tokenizer truncation to document admission")
step("Verify: propagates tokenizer truncation to document admission")
val result = html_tree_builder_build_with_parse_limits(
    "<p>x</p>", 100, 1, 10
)
expect(result.truncated).to_be(true)
```

</details>

### HtmlTreeBuilder honest content

#### reports ordinary documents as complete

- reports ordinary documents as complete
- Verify: reports ordinary documents as complete


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("reports ordinary documents as complete")
step("Verify: reports ordinary documents as complete")
val result = html_tree_builder_build_with_scripts("<p>safe</p>")
expect(result.truncated).to_be(false)
```

</details>

#### normal nesting is unchanged by the defensive limits

- normal nesting is unchanged by the defensive limits
- Parse a shallow, well-formed document (depth 3)
- Then parent-child structure is exact, unaffected by the caps
   - Expected: be_dom_get_tag(span) equals `span`
   - Expected: be_dom_get_children(p).len() equals `1`
   - Expected: be_dom_get_children(div).len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("normal nesting is unchanged by the defensive limits")
step("Parse a shallow, well-formed document (depth 3)")
val doc = html_tree_builder_build("<div><p><span>text</span></p></div>")

step("Then parent-child structure is exact, unaffected by the caps")
val div = _find_first_by_tag(doc, "div")
val p = _find_first_by_tag(div, "p")
val span = _find_first_by_tag(p, "span")
expect(be_dom_get_tag(span)).to_equal("span")
expect(be_dom_get_children(p).len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(be_dom_get_children(div).len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### assigns stable node identities and serializes the parsed DOM

- assigns stable node identities and serializes the parsed DOM
- Verify: assigns stable node identities and serializes the parsed DOM


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("assigns stable node identities and serializes the parsed DOM")
step("Verify: assigns stable node identities and serializes the parsed DOM")
val doc = html_tree_builder_build("<button>Go</button><input value='x'>")
val button = _find_first_by_tag(doc, "button")
val input = _find_first_by_tag(doc, "input")

expect(button.node_id).to_be_greater_than(0)
expect(input.node_id).to_be_greater_than(button.node_id)
val generation = DomDocumentGeneration.create(1).unwrap()
val index = dom_identity_index_build(doc, generation).unwrap()
val button_route = DomNodeRoute(
    generation: generation, node_id: button.node_id
)
expect(index.contains_route(button_route)).to_be(true)
expect(index.author_id_for_route(button_route)).to_be_nil()
val html = be_dom_serialize_html(doc)
expect(html).to_contain("<button>Go</button>")
expect(html).to_contain("<input value=\"x\">")
```

</details>

#### does not expose stylesheet text as body content

- does not expose stylesheet text as body content
- Verify: does not expose stylesheet text as body content
   - Expected: html does not contain `#stage`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("does not expose stylesheet text as body content")
step("Verify: does not expose stylesheet text as body content")
val doc = html_tree_builder_build(
    "<html><head><style>#stage { color: red; }</style></head><body><div>Visible</div></body></html>"
)
val html = be_dom_serialize_html(doc)

expect(html).to_contain("<div>Visible</div>")
expect(html.contains("#stage")).to_equal(false)
```

</details>

### DOM serialization work

#### preserves escaping void elements and render-only attributes

- preserves escaping void elements and render-only attributes
- Verify: preserves escaping void elements and render-only attributes


<details>
<summary>Executable SSpec</summary>

Runnable source: 51 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("preserves escaping void elements and render-only attributes")
step("Verify: preserves escaping void elements and render-only attributes")
var container = BeDomNode.element("div")
container.set_attr("id", "ordered")
container.set_attr("title", "<&\"")
container.set_attr("data-last", "z")
container.add_child(BeDomNode.text_node(1, "<&"))

val container_html = be_dom_serialize_html(container)
expect(container_html).to_start_with("<div ")
expect(container_html).to_contain(" id=\"ordered\"")
expect(container_html).to_contain(
    " title=\"&lt;&amp;&quot;\""
)
expect(container_html).to_contain(" data-last=\"z\"")
expect(container_html).to_end_with(">&lt;&amp;</div>")

var image = BeDomNode.element("img")
image.set_attr("src", "auth&")
image.set_attr("\u0000simple-render-image-src", "render&")
image.add_child(BeDomNode.text_node(2, "ignored"))

expect(be_dom_serialize_html(image)).to_equal(
    "<img src=\"auth&amp;\">"
)
expect(be_dom_serialize_html_for_render(image)).to_equal(
    "<img src=\"render&amp;\">"
)

var poster = BeDomNode.element("video")
poster.set_attr("poster", "poster<")
poster.set_attr("\u0000simple-render-image-poster", "render<")
expect(be_dom_serialize_html(poster)).to_equal(
    "<video poster=\"poster&lt;\"></video>"
)
expect(be_dom_serialize_html_for_render(poster)).to_equal(
    "<video poster=\"render&lt;\"></video>"
)

var styled = BeDomNode.element("div")
styled.set_attr("style", "background:url(\"auth\")")
styled.set_attr(
    "\u0000simple-render-image-style", "background:url(\"render\")"
)
expect(be_dom_serialize_html(styled)).to_equal(
    "<div style=\"background:url(&quot;auth&quot;)\"></div>"
)
expect(be_dom_serialize_html_for_render(styled)).to_equal(
    "<div style=\"background:url(&quot;render&quot;)\"></div>"
)
```

</details>

#### serializes children through the same byte-exact fragment path

- serializes children through the same byte-exact fragment path
- Verify: serializes children through the same byte-exact fragment path


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("serializes children through the same byte-exact fragment path")
step("Verify: serializes children through the same byte-exact fragment path")
var parent = BeDomNode.element("section")
var span = BeDomNode.element("span")
span.set_attr("id", "first")
span.add_child(BeDomNode.text_node(3, "A&B"))
var image = BeDomNode.element("img")
image.set_attr("src", "icon<")
parent.add_child(span)
parent.add_child(image)

expect(be_dom_serialize_children(parent)).to_equal(
    "<span id=\"first\">A&amp;B</span><img src=\"icon&lt;\">"
)
expect(be_dom_serialize_children(parent)).to_equal(
    be_dom_serialize_html(span) + be_dom_serialize_html(image)
)
```

</details>

#### keeps measured fragment work linear from N to two N siblings

- keeps measured fragment work linear from N to two N siblings
- Verify: keeps measured fragment work linear from N to two N siblings
   - Expected: smaller.fragment_count equals `3 + 4 * 512`
   - Expected: larger.fragment_count equals `3 + 4 * 1024`
   - Expected: smaller.output_length equals `11 + 14 * 512`
   - Expected: larger.output_length equals `11 + 14 * 1024`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("keeps measured fragment work linear from N to two N siblings")
step("Verify: keeps measured fragment work linear from N to two N siblings")
val smaller = _be_dom_measure_html_serialization(
    _flat_serialization_dom(512)
)
val larger = _be_dom_measure_html_serialization(
    _flat_serialization_dom(1024)
)
val old_smaller_work = _old_prefix_copy_work(512)
val old_larger_work = _old_prefix_copy_work(1024)

expect(smaller.failed).to_be(false)
expect(larger.failed).to_be(false)
expect(smaller.fragment_count).to_equal(3 + 4 * 512)
expect(larger.fragment_count).to_equal(3 + 4 * 1024)
expect(larger.fragment_count).to_equal(
    smaller.fragment_count * 2 - 3
)
expect(smaller.output_length).to_equal(11 + 14 * 512)
expect(larger.output_length).to_equal(11 + 14 * 1024)
expect(larger.output_length).to_equal(
    smaller.output_length * 2 - 11
)
expect(larger.work_units).to_be_less_than(smaller.work_units * 3)
expect(old_larger_work).to_be_greater_than(old_smaller_work * 3)
expect(larger.work_units).to_be_less_than(old_larger_work)
```

</details>

#### accepts depth 512 and fails closed at depth 513

- accepts depth 512 and fails closed at depth 513
- Verify: accepts depth 512 and fails closed at depth 513
   - Expected: at_limit.html.len().to_i64() equals `at_limit.output_length`
   - Expected: overflow.html equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("accepts depth 512 and fails closed at depth 513")
step("Verify: accepts depth 512 and fails closed at depth 513")
val at_limit = _be_dom_measure_html_serialization(
    _deep_serialization_dom(BE_DOM_HTML_SERIALIZE_MAX_DEPTH - 1)
)
val overflow = _be_dom_measure_html_serialization(
    _deep_serialization_dom(BE_DOM_HTML_SERIALIZE_MAX_DEPTH)
)

expect(at_limit.failed).to_be(false)
expect(at_limit.fragment_count).to_equal(
    3 * BE_DOM_HTML_SERIALIZE_MAX_DEPTH
)
expect(at_limit.fragment_count).to_be_less_than(
    BE_DOM_HTML_SERIALIZE_MAX_FRAGMENTS + 1
)
expect(at_limit.output_length).to_equal(
    11 * BE_DOM_HTML_SERIALIZE_MAX_DEPTH
)
expect(at_limit.output_length).to_be_less_than(
    BE_DOM_HTML_SERIALIZE_MAX_OUTPUT_LENGTH + 1
)
expect(at_limit.html.len().to_i64()).to_equal(at_limit.output_length)
expect(overflow.failed).to_be(true)
expect(overflow.html).to_equal("")
expect(be_dom_serialize_html(
    _deep_serialization_dom(BE_DOM_HTML_SERIALIZE_MAX_DEPTH)
)).to_equal("")
```

</details>

#### preflights expanding escapes against the remaining output budget

- preflights expanding escapes against the remaining output budget
- Verify: preflights expanding escapes against the remaining output budget
   - Expected: _be_dom_html_escaped_length_within("safe", 4) equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("preflights expanding escapes against the remaining output budget")
step("Verify: preflights expanding escapes against the remaining output budget")
expect(_be_dom_html_escaped_length_within(
    "&<>\"'", 24
)).to_equal(24)  # oracle: 24 — named expected value from the requirement
expect(_be_dom_html_escaped_length_within(
    "&<>\"'", 23
)).to_equal(-1)  # oracle: -1 — named expected value from the requirement
expect(_be_dom_html_escaped_length_within("safe", 4)).to_equal(4)
```

</details>

#### collects fragments once instead of copying each accumulated prefix

- collects fragments once instead of copying each accumulated prefix
- Verify: collects fragments once instead of copying each accumulated prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("collects fragments once instead of copying each accumulated prefix")
step("Verify: collects fragments once instead of copying each accumulated prefix")
val source = file_read(
    "src/lib/gc_async_mut/gpu/browser_engine/dom_accessors.spl"
)

expect(source).to_contain("parts.join(\"\")")
expect(source.index_of(
    "children_html = children_html +"
)).to_equal(-1)  # oracle: -1 — named expected value from the requirement
expect(source.index_of(
    "attributes_html = attributes_html +"
)).to_equal(-1)  # oracle: -1 — named expected value from the requirement
expect(source.index_of(
    "out = out + be_dom_serialize_html(child)"
)).to_equal(-1)  # oracle: -1 — named expected value from the requirement
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-BROWSER_ENGINE`
- `REQ-BROWSER-ENGINE-HTML-TREE-BUILDER-HARDENING-SPEC-SPL-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `789cb5f5b918c0261b3a805c89d9af58e36181e34b0fac000e1d5f701beaf746`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `789cb5f5b918c0261b3a805c89d9af58e36181e34b0fac000e1d5f701beaf746`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `789cb5f5b918c0261b3a805c89d9af58e36181e34b0fac000e1d5f701beaf746`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/browser_engine/html_tree_builder_hardening_spec.spl
mirror: doc/06_spec/01_unit/browser_engine/html_tree_builder_hardening_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/browser_engine/html_tree_builder_hardening_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/browser_engine/html_tree_builder_hardening_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/browser_engine/html_tree_builder_hardening_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/browser_engine/html_tree_builder_hardening_spec.spl:162:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'deeply nested markup parses to completion with bounded depth' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/html_tree_builder_hardening_spec.spl:179:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts the exact limit and truncates the next node' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/html_tree_builder_hardening_spec.spl:193:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'propagates tokenizer truncation to document admission' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
