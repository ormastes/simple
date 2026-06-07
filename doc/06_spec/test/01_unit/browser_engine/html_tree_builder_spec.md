# Html Tree Builder Specification

> <details>

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
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Html Tree Builder Specification

## Scenarios

### HtmlTreeBuilder implicit closing

#### AC-2: wraps body content in html/head/body even when absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _build("<p>hello</p>")
val html = _first_child_tag(doc)
expect(html).to_equal("html")
```

</details>

#### AC-2: implicitly closes <li> when next <li> starts

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _build("<ul><li>a<li>b</ul>")
val ul = _find_nested(doc, "ul")
val count = _child_count(ul)
expect(count).to_equal(2)
```

</details>

#### AC-2: implicitly closes <p> when block element starts

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _build("<p>text<div>block</div>")
val div = _find_nested(doc, "div")
val tag = be_dom_get_tag_name(div)
expect(tag).to_equal("div")
```

</details>

### HtmlTreeBuilder scope-based insertion

#### AC-2: inserts heading inside body scope

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _build("<h1>Title</h1>")
val h1 = _find_nested(doc, "h1")
expect(be_dom_get_tag_name(h1)).to_equal("h1")
```

</details>

#### AC-2: attribute preserved on parsed element

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _build("<a href=\"/path\">link</a>")
val a = _find_nested(doc, "a")
val href = be_dom_get_attribute(a, "href")
expect(href).to_equal("/path")
```

</details>

#### AC-2: nested structure preserves parent-child relationship

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _build("<div><p><span>text</span></p></div>")
val div = _find_nested(doc, "div")
val p = _find_first_by_tag(div, "p")
val span = _find_first_by_tag(p, "span")
expect(be_dom_get_tag_name(span)).to_equal("span")
```

</details>

### HtmlTreeBuilder foster parenting

#### AC-2: text before <table> is foster-parented before table

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = _build("<table>misplaced text<tr><td>cell</td></tr></table>")
val body = _find_nested(doc, "body")
val count = _child_count(body)
expect(count).to_be_greater_than(0)
```

</details>

#### AC-2: <p> inside <table> is foster-parented outside table

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/browser_engine/html_tree_builder_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
