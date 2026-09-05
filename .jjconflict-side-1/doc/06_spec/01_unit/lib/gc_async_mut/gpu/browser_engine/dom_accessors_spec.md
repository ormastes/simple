# Dom Accessors Specification

> <details>

<!-- sdn-diagram:id=dom_accessors_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dom_accessors_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dom_accessors_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dom_accessors_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dom Accessors Specification

## Scenarios

### Browser engine DOM accessors

#### collects recursive text content without changing visible text

- style:  node
- children: [ text
- style:  node
- children: [ text
   - Expected: be_dom_get_text_content(root) equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- children: [ node
- children: [section,  node
- Some
   - Expected: found.tag_name equals `p`
- fail
   - Expected: paragraphs.len() equals `3`
   - Expected: paragraphs[0].node_id equals `3`
   - Expected: paragraphs[1].node_id equals `4`
   - Expected: paragraphs[2].node_id equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
