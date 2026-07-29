# Html Tree Builder Flat Projection Specification

> Tests covering Canonical HTML flat projection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Html Tree Builder Flat Projection Specification

## Scenarios

### Canonical HTML flat projection

#### should preserve canonical pre-order parentage for fostered subtrees

- Project a table document containing foster-parented elements
   - Expected: projected.nodes[nested].parent equals `foster`
   - Expected: projected.nodes[nested + 1].text_data equals `FOSTER`
   - Expected: projected.nodes[nested + 1].parent equals `nested`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Project a table document containing foster-parented elements")
val projected = html_tree_builder_flat_projection(
    "<table id='table'><div id='foster'><span id='nested'>" +
    "FOSTER</span></div></table>"
)
val table = _projection_index_by_id(projected.nodes, "table")
val foster = _projection_index_by_id(projected.nodes, "foster")
val nested = _projection_index_by_id(projected.nodes, "nested")
expect(foster).to_be_less_than(table)
expect(projected.nodes[foster].parent).to_equal(
    projected.nodes[table].parent
)
expect(projected.nodes[nested].parent).to_equal(foster)
expect(projected.nodes[nested + 1].text_data).to_equal("FOSTER")
expect(projected.nodes[nested + 1].parent).to_equal(nested)
```

</details>

#### should use exact ASCII-insensitive textarea end tags

- Project a textarea with a near-match and mixed-case end tag


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Project a textarea with a near-match and mixed-case end tag")
val projected = html_tree_builder_flat_projection(
    "<textarea id='editor'>alpha</textareaevil><b>x</b>" +
    "</TEXTAREA><div id='after'></div>"
)
val editor = _projection_index_by_id(projected.nodes, "editor")
val after = _projection_index_by_id(projected.nodes, "after")
expect(projected.nodes[editor + 1].text_data).to_contain(
    "</textareaevil><b>x</b>"
)
expect(projected.nodes[after].parent).to_equal(
    projected.nodes[editor].parent
)
```

</details>

#### should normalize attributes and synthesize document structure

- Project a body fragment with mixed-case attribute content
   - Expected: projected.nodes[0].tag equals `#document`
   - Expected: projected.nodes[1].tag equals `html`
   - Expected: projected.nodes[page].tag equals `body`
   - Expected: projected.nodes[main].parent equals `page`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Project a body fragment with mixed-case attribute content")
val projected = html_tree_builder_flat_projection(
    "<body id='page' data-mode='Glass'><main id='main'></main>"
)
expect(projected.nodes[0].tag).to_equal("#document")
expect(projected.nodes[1].tag).to_equal("html")
val page = _projection_index_by_id(projected.nodes, "page")
val main = _projection_index_by_id(projected.nodes, "main")
expect(projected.nodes[page].tag).to_equal("body")
expect(projected.nodes[page].normalized_attrs).to_contain(
    "data-mode=\"Glass\""
)
expect(projected.nodes[main].parent).to_equal(page)
```

</details>

#### should synthesize body for empty and head-only documents

- Project empty and head-only documents
   - Expected: empty_bodies equals `1`
   - Expected: head_bodies equals `1`
   - Expected: title_text equals `A&中`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Project empty and head-only documents")
val empty = html_tree_builder_flat_projection("")
val head_only = html_tree_builder_flat_projection(
    "<head><title data-kind='α'>A&amp;&#x4E2D;</title></head>"
)
var empty_bodies = 0
var head_bodies = 0
var title = -1
var title_text = ""
for node in empty.nodes:
    if node.tag == "body":
        empty_bodies = empty_bodies + 1
var i = 0
while i < head_only.nodes.len():
    if head_only.nodes[i].tag == "body":
        head_bodies = head_bodies + 1
    if head_only.nodes[i].tag == "title":
        title = i
    elif (
        title >= 0 and head_only.nodes[i].tag == "#text" and
        head_only.nodes[i].parent == title
    ):
        title_text = title_text + head_only.nodes[i].text_data
    i = i + 1
expect(empty_bodies).to_equal(1)
expect(head_bodies).to_equal(1)
expect(head_only.nodes[title].normalized_attrs).to_contain(
    "data-kind=\"α\""
)
expect(title_text).to_equal("A&中")
```

</details>

#### should retain bounded node token and attribute receipts

- Project a document with bounded nodes, tokens, and attributes
   - Expected: projected.truncated is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Project a document with bounded nodes, tokens, and attributes")
val projected = html_tree_builder_flat_projection_with_limits(
    "<div id='a' data-a='1' data-b='2'><span>x</span></div>",
    5, 32, 1
)
expect(projected.nodes.len()).to_be_less_than(6)
expect(projected.truncated).to_equal(true)
```

</details>

#### should retain the canonical open-element depth cap

- Project a document deeper than the open-element limit


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Project a document deeper than the open-element limit")
val projected = html_tree_builder_flat_projection(_nested_divs(700))
var max_depth = 0
for node in projected.nodes:
    if node.depth > max_depth:
        max_depth = node.depth
expect(max_depth).to_be_less_than(515)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser_engine/html_tree_builder_flat_projection_spec.spl` |
| Updated | 2026-07-29 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Canonical HTML flat projection.
- Canonical HTML flat projection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
