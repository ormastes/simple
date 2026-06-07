# DOM API Spec

> Unit tests for the Simple browser engine DOM API.

<!-- sdn-diagram:id=dom_api_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dom_api_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dom_api_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dom_api_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DOM API Spec

Unit tests for the Simple browser engine DOM API.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser/script/dom_api_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Unit tests for the Simple browser engine DOM API.

## Scenarios

### DOM API - Element Creation

#### creates an element node with correct tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val div = document_create_element("div")
expect(node_tag_name(div)).to_equal("div")
```

</details>

#### creates a text node

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tn = document_create_text_node("hello")
expect(node_tag_name(tn)).to_equal("#text")
```

</details>

#### creates a span element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val span = document_create_element("span")
expect(node_tag_name(span)).to_equal("span")
```

</details>

### DOM API - Tree Manipulation

#### appends a child to parent

1. var parent = document create element
2. parent = node append child
   - Expected: kids.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parent = document_create_element("div")
val child = document_create_element("p")
parent = node_append_child(parent, child)
val kids = node_children(parent)
expect(kids.len()).to_equal(1)
```

</details>

#### removes a child by index

1. var parent = document create element
2. parent = node append child
3. parent = node append child
4. parent = node remove child
   - Expected: kids.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parent = document_create_element("div")
val c1 = document_create_element("p")
val c2 = document_create_element("span")
parent = node_append_child(parent, c1)
parent = node_append_child(parent, c2)
parent = node_remove_child(parent, 0)
val kids = node_children(parent)
expect(kids.len()).to_equal(1)
```

</details>

#### inserts a child before a reference index

1. var parent = document create element
2. parent = node append child
3. parent = node insert before
   - Expected: kids.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parent = document_create_element("div")
val c1 = document_create_element("p")
val c2 = document_create_element("span")
parent = node_append_child(parent, c1)
parent = node_insert_before(parent, c2, 0)
val kids = node_children(parent)
expect(kids.len()).to_equal(2)
```

</details>

### DOM API - Attributes

#### sets and gets an attribute

1. var el = document create element
2. el = node set attribute
   - Expected: v != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var el = document_create_element("div")
el = node_set_attribute(el, "data-x", "42")
val v = node_get_attribute(el, "data-x")
expect(v != nil).to_equal(true)
```

</details>

#### removes an attribute

1. var el = document create element
2. el = node set attribute
3. el = node remove attribute
   - Expected: v == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var el = document_create_element("div")
el = node_set_attribute(el, "data-x", "42")
el = node_remove_attribute(el, "data-x")
val v = node_get_attribute(el, "data-x")
expect(v == nil).to_equal(true)
```

</details>

### DOM API - Text Content

#### sets text content on a node

1. var el = document create element
2. el = node set text content
   - Expected: kids.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var el = document_create_element("div")
el = node_set_text_content(el, "hello world")
val kids = node_children(el)
expect(kids.len()).to_equal(1)
```

</details>

#### sets inner HTML text fallback

1. var el = document create element
2. el = node set inner html
   - Expected: kids.len() equals `1`
   - Expected: node_get_text_content(kids[0]) equals `hello < world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var el = document_create_element("div")
el = node_set_inner_html(el, "hello < world")
val kids = node_children(el)
expect(kids.len()).to_equal(1)
expect(node_get_text_content(kids[0])).to_equal("hello < world")
```

</details>

#### parses a flat element inner HTML fragment

1. var el = document create element
2. el = node set inner html
   - Expected: kids.len() equals `1`
   - Expected: node_tag_name(kids[0]) equals `span`
   - Expected: node_get_attribute(kids[0], "id") != nil is true
   - Expected: node_class_list_contains(kids[0], "hot") is true
   - Expected: node_class_list_contains(kids[0], "active") is true
   - Expected: node_get_style_property(kids[0], "display") equals `none`
   - Expected: node_get_text_content(node_children(kids[0])[0]) equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var el = document_create_element("div")
el = node_set_inner_html(el, "<span id=\"greeting\" class=\"hot active\" style=\"display:none\">hello</span>")
val kids = node_children(el)
expect(kids.len()).to_equal(1)
expect(node_tag_name(kids[0])).to_equal("span")
expect(node_get_attribute(kids[0], "id") != nil).to_equal(true)
expect(node_class_list_contains(kids[0], "hot")).to_equal(true)
expect(node_class_list_contains(kids[0], "active")).to_equal(true)
expect(node_get_style_property(kids[0], "display")).to_equal("none")
expect(node_get_text_content(node_children(kids[0])[0])).to_equal("hello")
```

</details>

#### parses flat sibling inner HTML fragments

1. var el = document create element
2. el = node set inner html
   - Expected: kids.len() equals `2`
   - Expected: node_tag_name(kids[0]) equals `b`
   - Expected: node_tag_name(kids[1]) equals `i`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var el = document_create_element("div")
el = node_set_inner_html(el, "<b>one</b><i>two</i>")
val kids = node_children(el)
expect(kids.len()).to_equal(2)
expect(node_tag_name(kids[0])).to_equal("b")
expect(node_tag_name(kids[1])).to_equal("i")
```

</details>

### DOM API - Class List

#### adds a class

1. var el = document create element
2. el = node class list add
   - Expected: node_class_list_contains(el, "active") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var el = document_create_element("div")
el = node_class_list_add(el, "active")
expect(node_class_list_contains(el, "active")).to_equal(true)
```

</details>

#### removes a class

1. var el = document create element
2. el = node class list add
3. el = node class list remove
   - Expected: node_class_list_contains(el, "active") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var el = document_create_element("div")
el = node_class_list_add(el, "active")
el = node_class_list_remove(el, "active")
expect(node_class_list_contains(el, "active")).to_equal(false)
```

</details>

#### toggles a class on

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val el = document_create_element("div")
val result = node_class_list_toggle(el, "active")
expect(result).to_equal(true)
```

</details>

#### toggles a class off

1. var el = document create element
2. el = node class list add
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var el = document_create_element("div")
el = node_class_list_add(el, "active")
val result = node_class_list_toggle(el, "active")
expect(result).to_equal(false)
```

</details>

### DOM API - Query

#### finds element by id

1. var root = document create element
2. var child = document create element
3. child = node set attribute
4. root = node append child
   - Expected: found != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var root = document_create_element("div")
var child = document_create_element("span")
child = node_set_attribute(child, "id", "myspan")
root = node_append_child(root, child)
val found = document_get_element_by_id(root, "myspan")
expect(found != nil).to_equal(true)
```

</details>

#### query selector by tag

1. var root = document create element
2. root = node append child
   - Expected: found != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var root = document_create_element("div")
val child = document_create_element("p")
root = node_append_child(root, child)
val found = document_query_selector(root, "p")
expect(found != nil).to_equal(true)
```

</details>

#### query selector all returns multiple matches

1. var root = document create element
2. root = node append child
3. root = node append child
   - Expected: all.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var root = document_create_element("div")
val c1 = document_create_element("p")
val c2 = document_create_element("p")
root = node_append_child(root, c1)
root = node_append_child(root, c2)
val all = document_query_selector_all(root, "p")
expect(all.len()).to_equal(2)
```

</details>

### DOM API - Parent Traversal

#### returns nil without root context

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = document_create_element("div")
val p = node_parent(root)
expect(p == nil).to_equal(true)
```

</details>

#### finds parent from a known root

1. var root = document create element
2. var parent = document create element
3. parent = node set attribute
4. var child = document create element
5. child = node set attribute
6. parent = node append child
7. root = node append child
   - Expected: found != nil is true
   - Expected: node_get_attribute(node, "id") != nil is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var root = document_create_element("div")
var parent = document_create_element("section")
parent = node_set_attribute(parent, "id", "parent")
var child = document_create_element("span")
child = node_set_attribute(child, "id", "child")
parent = node_append_child(parent, child)
root = node_append_child(root, parent)
val found = node_parent_in(root, child)
expect(found != nil).to_equal(true)
match found:
    case Some(node):
        expect(node_get_attribute(node, "id") != nil).to_equal(true)
    case nil:
        expect(false).to_equal(true)
```

</details>

### DOM API - Style Properties

#### sets a style property

1. var el = document create element
2. el = node set style property
   - Expected: node_tag_name(el) equals `div`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var el = document_create_element("div")
el = node_set_style_property(el, "display", "none")
# Style is applied through BeDomNode.set_style
expect(node_tag_name(el)).to_equal("div")
```

</details>

#### gets common inline style property values

1. var el = document create element
2. el = node set style property
3. el = node set style property
4. el = node set style property
5. el = node set style property
6. el = node set style property
7. el = node set style property
8. el = node set style property
9. el = node set style property
10. el = node set style property
   - Expected: node_get_style_property(el, "display") equals `inline-flex`
   - Expected: node_get_style_property(el, "width") equals `120px`
   - Expected: node_get_style_property(el, "height") equals `50%`
   - Expected: node_get_style_property(el, "font-size") equals `18px`
   - Expected: node_get_style_property(el, "font-weight") equals `700`
   - Expected: node_get_style_property(el, "text-align") equals `center`
   - Expected: node_get_style_property(el, "visibility") equals `hidden`
   - Expected: node_get_style_property(el, "position") equals `absolute`
   - Expected: node_get_style_property(el, "overflow") equals `scroll`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var el = document_create_element("div")
el = node_set_style_property(el, "display", "inline-flex")
el = node_set_style_property(el, "width", "120px")
el = node_set_style_property(el, "height", "50%")
el = node_set_style_property(el, "font-size", "18px")
el = node_set_style_property(el, "font-weight", "700")
el = node_set_style_property(el, "text-align", "center")
el = node_set_style_property(el, "visibility", "hidden")
el = node_set_style_property(el, "position", "absolute")
el = node_set_style_property(el, "overflow", "scroll")
expect(node_get_style_property(el, "display")).to_equal("inline-flex")
expect(node_get_style_property(el, "width")).to_equal("120px")
expect(node_get_style_property(el, "height")).to_equal("50%")
expect(node_get_style_property(el, "font-size")).to_equal("18px")
expect(node_get_style_property(el, "font-weight")).to_equal("700")
expect(node_get_style_property(el, "text-align")).to_equal("center")
expect(node_get_style_property(el, "visibility")).to_equal("hidden")
expect(node_get_style_property(el, "position")).to_equal("absolute")
expect(node_get_style_property(el, "overflow")).to_equal("scroll")
```

</details>

#### keeps unsupported inline style reads empty

1. var el = document create element
2. el = node set style property
   - Expected: node_get_style_property(el, "cursor") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var el = document_create_element("div")
el = node_set_style_property(el, "display", "block")
expect(node_get_style_property(el, "cursor")).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
