# HTML Tokenizer → Tree Builder Pipeline Specification

> Every other tokenizer spec hand-builds `HtmlToken` values and every tree builder spec consumes those hand-built tokens directly — neither proves the two stages actually agree with each other. This spec closes that gap: it hands `tokenize_html` a real HTML source string and feeds the resulting token stream straight into `build_html_tree`, asserting on the DOM tree that comes out the other end. A tag-name bug, an attribute-parsing bug, or a mismatch in how the tokenizer chunks text would show up here even though each half's own unit spec stays green.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HTML Tokenizer → Tree Builder Pipeline Specification

Every other tokenizer spec hand-builds `HtmlToken` values and every tree builder spec consumes those hand-built tokens directly — neither proves the two stages actually agree with each other. This spec closes that gap: it hands `tokenize_html` a real HTML source string and feeds the resulting token stream straight into `build_html_tree`, asserting on the DOM tree that comes out the other end. A tag-name bug, an attribute-parsing bug, or a mismatch in how the tokenizer chunks text would show up here even though each half's own unit spec stays green.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink port |
| Status | Active |
| Source | `test/01_unit/lib/blink/html_tokenizer_tree_builder_pipeline_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Every other tokenizer spec hand-builds `HtmlToken` values and every tree
builder spec consumes those hand-built tokens directly — neither proves the
two stages actually agree with each other. This spec closes that gap: it
hands `tokenize_html` a real HTML source string and feeds the resulting
token stream straight into `build_html_tree`, asserting on the DOM tree
that comes out the other end. A tag-name bug, an attribute-parsing bug, or
a mismatch in how the tokenizer chunks text would show up here even though
each half's own unit spec stays green.

Deliberately out of scope (inherited from both stages): entity decoding,
RAWTEXT/RCDATA modes, CDATA sections, HTML5 insertion-mode algorithms
(implied tags, adoption agency, foster parenting).

@manual_section Browser Rendering

## Scenarios

### tokenize_html piped into build_html_tree

#### builds a nested element tree from a real HTML string, not hand-built tokens

- builds a nested element tree from a real HTML string, not hand-built tokens
- parse a small page: html > body > p with a class, plus text
- root(0) + html(1) + body(2) + p(3) + text(4) = 5 nodes
   - Expected: tree.nodes.len() equals `5`
- html is a child of the document root
   - Expected: html_node.tag_name equals `html`
   - Expected: html_node.node_type equals `NodeType.Element`
   - Expected: html_node.parent equals `0`
   - Expected: "html element created" equals `it was not`
- body nests under html
   - Expected: body_node.tag_name equals `body`
   - Expected: body_node.parent equals `1`
   - Expected: "body element created" equals `it was not`
- p nests under body and kept its class attribute from the source text
   - Expected: p_node.tag_name equals `p`
   - Expected: p_node.parent equals `2`
   - Expected: v equals `greet`
   - Expected: "class attribute parsed" equals `it was not`
   - Expected: "p element created" equals `it was not`
- the tokenizer coalesced "hi there" into one text node under p
   - Expected: text_node.node_type equals `NodeType.Text`
   - Expected: text_node.text_content equals `hi there`
   - Expected: text_node.parent equals `3`
   - Expected: "text node created" equals `it was not`


<details>
<summary>Executable SSpec</summary>

Runnable source: 47 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("builds a nested element tree from a real HTML string, not hand-built tokens")
step("parse a small page: html > body > p with a class, plus text")
val html = "<html><body><p class=\"greet\">hi there</p></body></html>"
val tree = build_html_tree(tokenize_html(html))

step("root(0) + html(1) + body(2) + p(3) + text(4) = 5 nodes")
expect(tree.nodes.len()).to_equal(5)

step("html is a child of the document root")
match tree.get_node(1):
    Some(html_node):
        expect(html_node.tag_name).to_equal("html")
        expect(html_node.node_type).to_equal(NodeType.Element)
        expect(html_node.parent).to_equal(0)
    None:
        expect("html element created").to_equal("it was not")

step("body nests under html")
match tree.get_node(2):
    Some(body_node):
        expect(body_node.tag_name).to_equal("body")
        expect(body_node.parent).to_equal(1)
    None:
        expect("body element created").to_equal("it was not")

step("p nests under body and kept its class attribute from the source text")
match tree.get_node(3):
    Some(p_node):
        expect(p_node.tag_name).to_equal("p")
        expect(p_node.parent).to_equal(2)
        match tree.get_attribute(3, "class"):
            Some(v):
                expect(v).to_equal("greet")
            None:
                expect("class attribute parsed").to_equal("it was not")
    None:
        expect("p element created").to_equal("it was not")

step("the tokenizer coalesced \"hi there\" into one text node under p")
match tree.get_node(4):
    Some(text_node):
        expect(text_node.node_type).to_equal(NodeType.Text)
        expect(text_node.text_content).to_equal("hi there")
        expect(text_node.parent).to_equal(3)
    None:
        expect("text node created").to_equal("it was not")
```

</details>

#### keeps a self-closing void element childless and its trailing text a sibling

- keeps a self-closing void element childless and its trailing text a sibling
- parse a line break followed by text, with no matching end tag
- root(0) + div(1) + text(2) + br(3) + text(4) = 5 nodes
   - Expected: tree.nodes.len() equals `5`
- br is self-closing, so it never opened as an insertion point
   - Expected: br_node.tag_name equals `br`
   - Expected: br_node.first_child equals `-1`
   - Expected: br_node.parent equals `1`
   - Expected: "br element created" equals `it was not`
- the trailing text after <br/> lands as div's child, not br's
   - Expected: text_node.text_content equals `after`
   - Expected: text_node.parent equals `1`
   - Expected: "trailing text node created" equals `it was not`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps a self-closing void element childless and its trailing text a sibling")
step("parse a line break followed by text, with no matching end tag")
val html = "<div>before<br/>after</div>"
val tree = build_html_tree(tokenize_html(html))

step("root(0) + div(1) + text(2) + br(3) + text(4) = 5 nodes")
expect(tree.nodes.len()).to_equal(5)

step("br is self-closing, so it never opened as an insertion point")
match tree.get_node(3):
    Some(br_node):
        expect(br_node.tag_name).to_equal("br")
        expect(br_node.first_child).to_equal(-1)
        expect(br_node.parent).to_equal(1)
    None:
        expect("br element created").to_equal("it was not")

step("the trailing text after <br/> lands as div's child, not br's")
match tree.get_node(4):
    Some(text_node):
        expect(text_node.text_content).to_equal("after")
        expect(text_node.parent).to_equal(1)
    None:
        expect("trailing text node created").to_equal("it was not")
```

</details>

#### drops a comment and a doctype from the tree while keeping surrounding elements

- drops a comment and a doctype from the tree while keeping surrounding elements
- parse a doctype, a comment, then a real element
- the tokenizer itself still reports the doctype and comment tokens
   - Expected: toks[0].kind equals `HtmlTokenKind.Doctype`
   - Expected: toks[0].name equals `html`
   - Expected: toks[1].kind equals `HtmlTokenKind.Comment`
- but the tree builder ignores Doctype and has no dedicated Comment-skip for span's parent
   - Expected: tree.nodes.len() equals `4`
   - Expected: span_node.tag_name equals `span`
   - Expected: span_node.parent equals `0`
   - Expected: "span element created" equals `it was not`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("drops a comment and a doctype from the tree while keeping surrounding elements")
step("parse a doctype, a comment, then a real element")
val html = "<!DOCTYPE html><!-- note --><span>x</span>"
val toks = tokenize_html(html)

step("the tokenizer itself still reports the doctype and comment tokens")
expect(toks[0].kind).to_equal(HtmlTokenKind.Doctype)
expect(toks[0].name).to_equal("html")
expect(toks[1].kind).to_equal(HtmlTokenKind.Comment)

step("but the tree builder ignores Doctype and has no dedicated Comment-skip for span's parent")
val tree = build_html_tree(toks)
# root(0) + comment(1, still a real DOM node) + span(2) + text(3) = 4 nodes
expect(tree.nodes.len()).to_equal(4)
match tree.get_node(2):
    Some(span_node):
        expect(span_node.tag_name).to_equal("span")
        expect(span_node.parent).to_equal(0)
    None:
        expect("span element created").to_equal("it was not")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-BLINK-HTML-TOK-PIPELINE-001`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cbf3a14fa64a652ee5b95028b25006807544e5a1e0a91f11a90b0efd3a029931`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cbf3a14fa64a652ee5b95028b25006807544e5a1e0a91f11a90b0efd3a029931`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cbf3a14fa64a652ee5b95028b25006807544e5a1e0a91f11a90b0efd3a029931`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/blink/html_tokenizer_tree_builder_pipeline_spec.spl
mirror: doc/06_spec/01_unit/lib/blink/html_tokenizer_tree_builder_pipeline_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/lib/blink/html_tokenizer_tree_builder_pipeline_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/blink/html_tokenizer_tree_builder_pipeline_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/blink/html_tokenizer_tree_builder_pipeline_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/blink/html_tokenizer_tree_builder_pipeline_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/blink/html_tokenizer_tree_builder_pipeline_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds a nested element tree from a real HTML string, not hand-built tokens' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/blink/html_tokenizer_tree_builder_pipeline_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps a self-closing void element childless and its trailing text a sibling' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/blink/html_tokenizer_tree_builder_pipeline_spec.spl:118:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'drops a comment and a doctype from the tree while keeping surrounding elements' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
