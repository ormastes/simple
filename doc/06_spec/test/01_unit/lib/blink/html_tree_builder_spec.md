# HTML Tree Builder Specification

> Tests for `build_html_tree` — the second stage of the Blink HTML parser port. Covers happy-path HTML5 tree construction: element nesting, text nodes, self-closing void elements, comment nodes, and attribute preservation. Token values are constructed directly to avoid tokenizer coupling.

<!-- sdn-diagram:id=html_tree_builder_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=html_tree_builder_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

html_tree_builder_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=html_tree_builder_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HTML Tree Builder Specification

Tests for `build_html_tree` — the second stage of the Blink HTML parser port. Covers happy-path HTML5 tree construction: element nesting, text nodes, self-closing void elements, comment nodes, and attribute preservation. Token values are constructed directly to avoid tokenizer coupling.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #BLK-HTML-TREE-001 |
| Category | Browser / Blink port |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/blink/html_tree_builder_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for `build_html_tree` — the second stage of the Blink HTML parser port.
Covers happy-path HTML5 tree construction: element nesting, text nodes,
self-closing void elements, comment nodes, and attribute preservation.
Token values are constructed directly to avoid tokenizer coupling.

## Scenarios

### html_tree_builder

#### build_html_tree: empty tokens produces empty tree (just root DocumentNode)

1. Some
   - Expected: root.node_type == NodeType.DocumentNode is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens: [HtmlToken] = [
    HtmlToken(
        kind: HtmlTokenKind.Eof,
        name: "",
        data: "",
        attributes: [],
        self_closing: false
    )
]
val tree = build_html_tree(tokens)
# Root node id is always 0, node count is exactly 1.
expect(tree.nodes.len()).to_equal(1)
val root_opt = tree.get_node(0)
match root_opt:
    Some(root):
        expect(root.node_type == NodeType.DocumentNode).to_equal(true)
    None:
        expect(false).to_equal(true)
```

</details>

#### build_html_tree: single \

1. Some
   - Expected: html_node.tag_name equals `html`
   - Expected: html_node.node_type == NodeType.Element is true
   - Expected: html_node.parent equals `0`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens: [HtmlToken] = [
    HtmlToken(
        kind: HtmlTokenKind.StartTag,
        name: "html",
        data: "",
        attributes: [],
        self_closing: false
    ),
    HtmlToken(
        kind: HtmlTokenKind.EndTag,
        name: "html",
        data: "",
        attributes: [],
        self_closing: false
    ),
    HtmlToken(
        kind: HtmlTokenKind.Eof,
        name: "",
        data: "",
        attributes: [],
        self_closing: false
    )
]
val tree = build_html_tree(tokens)
# There should be root + html element = 2 nodes total.
expect(tree.nodes.len()).to_equal(2)
val html_opt = tree.get_node(1)
match html_opt:
    Some(html_node):
        expect(html_node.tag_name).to_equal("html")
        expect(html_node.node_type == NodeType.Element).to_equal(true)
        expect(html_node.parent).to_equal(0)
    None:
        expect(false).to_equal(true)
```

</details>

#### build_html_tree: \

1. HtmlToken
2. HtmlToken
3. HtmlToken
4. HtmlToken
5. HtmlToken
6. HtmlToken
7. HtmlToken
8. HtmlToken
   - Expected: tree.nodes.len() equals `5`
9. Some
   - Expected: html_node.parent equals `0`
   - Expected: false is true
10. Some
   - Expected: body_node.parent equals `1`
   - Expected: body_node.tag_name equals `body`
   - Expected: false is true
11. Some
   - Expected: p_node.parent equals `2`
   - Expected: p_node.tag_name equals `p`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens: [HtmlToken] = [
    HtmlToken(kind: HtmlTokenKind.StartTag, name: "html",  data: "", attributes: [], self_closing: false),
    HtmlToken(kind: HtmlTokenKind.StartTag, name: "body",  data: "", attributes: [], self_closing: false),
    HtmlToken(kind: HtmlTokenKind.StartTag, name: "p",     data: "", attributes: [], self_closing: false),
    HtmlToken(kind: HtmlTokenKind.Character, name: "",     data: "hi", attributes: [], self_closing: false),
    HtmlToken(kind: HtmlTokenKind.EndTag,   name: "p",     data: "", attributes: [], self_closing: false),
    HtmlToken(kind: HtmlTokenKind.EndTag,   name: "body",  data: "", attributes: [], self_closing: false),
    HtmlToken(kind: HtmlTokenKind.EndTag,   name: "html",  data: "", attributes: [], self_closing: false),
    HtmlToken(kind: HtmlTokenKind.Eof,      name: "",      data: "", attributes: [], self_closing: false)
]
val tree = build_html_tree(tokens)
# root(0) + html(1) + body(2) + p(3) + text("hi")(4) = 5 nodes
expect(tree.nodes.len()).to_equal(5)
# html is child of root
val html_opt = tree.get_node(1)
match html_opt:
    Some(html_node):
        expect(html_node.parent).to_equal(0)
    None:
        expect(false).to_equal(true)
# body is child of html
val body_opt = tree.get_node(2)
match body_opt:
    Some(body_node):
        expect(body_node.parent).to_equal(1)
        expect(body_node.tag_name).to_equal("body")
    None:
        expect(false).to_equal(true)
# p is child of body
val p_opt = tree.get_node(3)
match p_opt:
    Some(p_node):
        expect(p_node.parent).to_equal(2)
        expect(p_node.tag_name).to_equal("p")
    None:
        expect(false).to_equal(true)
```

</details>

#### build_html_tree: \

1. HtmlToken
2. HtmlToken
3. HtmlToken
4. HtmlToken
   - Expected: tree.nodes.len() equals `3`
5. Some
   - Expected: text_node.node_type == NodeType.Text is true
   - Expected: text_node.text_content equals `text`
   - Expected: text_node.parent equals `1`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens: [HtmlToken] = [
    HtmlToken(kind: HtmlTokenKind.StartTag,  name: "div",  data: "",     attributes: [], self_closing: false),
    HtmlToken(kind: HtmlTokenKind.Character, name: "",     data: "text", attributes: [], self_closing: false),
    HtmlToken(kind: HtmlTokenKind.EndTag,    name: "div",  data: "",     attributes: [], self_closing: false),
    HtmlToken(kind: HtmlTokenKind.Eof,       name: "",     data: "",     attributes: [], self_closing: false)
]
val tree = build_html_tree(tokens)
# root(0) + div(1) + text(2) = 3 nodes
expect(tree.nodes.len()).to_equal(3)
val text_opt = tree.get_node(2)
match text_opt:
    Some(text_node):
        expect(text_node.node_type == NodeType.Text).to_equal(true)
        expect(text_node.text_content).to_equal("text")
        expect(text_node.parent).to_equal(1)
    None:
        expect(false).to_equal(true)
```

</details>

#### build_html_tree: \

1. HtmlToken
2. HtmlToken
   - Expected: tree.nodes.len() equals `2`
3. Some
   - Expected: br_node.tag_name equals `br`
   - Expected: br_node.first_child equals `-1`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens: [HtmlToken] = [
    HtmlToken(kind: HtmlTokenKind.StartTag, name: "br", data: "", attributes: [], self_closing: true),
    HtmlToken(kind: HtmlTokenKind.Eof,      name: "",   data: "", attributes: [], self_closing: false)
]
val tree = build_html_tree(tokens)
# root(0) + br(1) = 2 nodes; br has no children
expect(tree.nodes.len()).to_equal(2)
val br_opt = tree.get_node(1)
match br_opt:
    Some(br_node):
        expect(br_node.tag_name).to_equal("br")
        expect(br_node.first_child).to_equal(-1)
    None:
        expect(false).to_equal(true)
```

</details>

#### build_html_tree: \

1. HtmlToken
2. HtmlToken
   - Expected: tree.nodes.len() equals `2`
3. Some
   - Expected: comment_node.node_type == NodeType.Comment is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens: [HtmlToken] = [
    HtmlToken(kind: HtmlTokenKind.Comment, name: "", data: " hi ", attributes: [], self_closing: false),
    HtmlToken(kind: HtmlTokenKind.Eof,     name: "", data: "",     attributes: [], self_closing: false)
]
val tree = build_html_tree(tokens)
# root(0) + comment(1) = 2 nodes
expect(tree.nodes.len()).to_equal(2)
val comment_opt = tree.get_node(1)
match comment_opt:
    Some(comment_node):
        expect(comment_node.node_type == NodeType.Comment).to_equal(true)
        expect(comment_node.text_content.len()).to_be_greater_than(0)
    None:
        expect(false).to_equal(true)
```

</details>

#### build_html_tree: '<a href=\

1. HtmlAttribute
2. HtmlToken
3. HtmlToken
4. HtmlToken
5. HtmlToken
   - Expected: tree.nodes.len() equals `3`
6. Some
   - Expected: a_node.tag_name equals `a`
7. Some
   - Expected: v equals `x`
   - Expected: false is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val attrs: [HtmlAttribute] = [
    HtmlAttribute(name: "href", value: "x")
]
val tokens: [HtmlToken] = [
    HtmlToken(kind: HtmlTokenKind.StartTag,  name: "a",     data: "",      attributes: attrs, self_closing: false),
    HtmlToken(kind: HtmlTokenKind.Character, name: "",      data: "click", attributes: [],    self_closing: false),
    HtmlToken(kind: HtmlTokenKind.EndTag,    name: "a",     data: "",      attributes: [],    self_closing: false),
    HtmlToken(kind: HtmlTokenKind.Eof,       name: "",      data: "",      attributes: [],    self_closing: false)
]
val tree = build_html_tree(tokens)
# root(0) + a(1) + text(2) = 3 nodes
expect(tree.nodes.len()).to_equal(3)
val a_opt = tree.get_node(1)
match a_opt:
    Some(a_node):
        expect(a_node.tag_name).to_equal("a")
        val href_opt = tree.get_attribute(1, "href")
        match href_opt:
            Some(v):
                expect(v).to_equal("x")
            None:
                expect(false).to_equal(true)
    None:
        expect(false).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
