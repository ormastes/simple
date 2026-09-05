# DOM build for GPU offload

> Covers the DOM-build path GPU offload snapshots rely on: BeDomNode

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 38 | 38 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DOM build for GPU offload

Covers the DOM-build path GPU offload snapshots rely on: BeDomNode

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_build_gpu_offload_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Covers the DOM-build path GPU offload snapshots rely on: BeDomNode
construction/mutation primitives, the minimal HTML string parser and the
widget-tree conversion (widget_to_dom / ui_tree_to_dom) in
widget_to_dom.spl, and generation-qualified identity routes that stay
stable across rebuilds of identical content and are invalidated when the
document generation is replaced.

Widget/parser identity is routed through the `attributes` dict
("id"/"class"), matching how the rest of browser_engine reads it
(be_dom_find_by_id, dom_accessors, dom_identity_index). Duplicate
detection in dom_identity_index_build is first-wins: a duplicate author
id bumps the counter and never rebinds the first route.

## Scenarios

### BeDomNode construction and mutation

#### creates elements and text nodes with expected defaults

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates elements and text nodes with expected defaults
   - Expected: div.tag_name equals `div`
   - Expected: div.node_id equals `0`
   - Expected: div.parent_id equals `-1`
   - Expected: div.children.len() equals `0`
   - Expected: div.is_element() is true
   - Expected: div.is_text() is false
   - Expected: ided.node_id equals `7`
   - Expected: ided.tag_name equals `section`
   - Expected: tn.tag_name equals `#text`
   - Expected: tn.data equals `hello`
   - Expected: tn.node_id equals `9`
   - Expected: tn.is_text() is true
   - Expected: tn.is_element() is false
   - Expected: anon.tag_name equals `#text`
   - Expected: anon.data equals `world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates elements and text nodes with expected defaults")
val div = BeDomNode.element("div")
expect(div.tag_name).to_equal("div")
expect(div.node_id).to_equal(0)
expect(div.parent_id).to_equal(-1)
expect(div.children.len()).to_equal(0)
expect(div.is_element()).to_equal(true)
expect(div.is_text()).to_equal(false)

val ided = BeDomNode.element_with_id(7, "section")
expect(ided.node_id).to_equal(7)
expect(ided.tag_name).to_equal("section")

val tn = BeDomNode.text_node(9, "hello")
expect(tn.tag_name).to_equal("#text")
expect(tn.data).to_equal("hello")
expect(tn.node_id).to_equal(9)
expect(tn.is_text()).to_equal(true)
expect(tn.is_element()).to_equal(false)

val anon = BeDomNode.text("world")
expect(anon.tag_name).to_equal("#text")
expect(anon.data).to_equal("world")
```

</details>

#### add_child reparents a value copy of the child

- add_child reparents a value copy of the child
   - Expected: parent.children.len() equals `1`
   - Expected: parent.children[0].parent_id equals `1`
   - Expected: parent.children[0].tag_name equals `span`
   - Expected: parent.children[0].tag_name equals `span`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("add_child reparents a value copy of the child")
var parent = BeDomNode.element_with_id(1, "div")
var child = BeDomNode.element_with_id(2, "span")
parent.add_child(child)
expect(parent.children.len()).to_equal(1)
expect(parent.children[0].parent_id).to_equal(1)
expect(parent.children[0].tag_name).to_equal("span")
# Value semantics: mutating the original after append must not
# change the appended copy (GPU snapshots rely on this isolation).
child.tag_name = "b"
expect(parent.children[0].tag_name).to_equal("span")
```

</details>

#### set_attr / get_attr / has_attr / remove_attr round-trip

- set_attr / get_attr / has_attr / remove_attr round-trip
   - Expected: node.get_attr("type") equals ``
   - Expected: node.has_attr("type") is false
   - Expected: node.get_attr("type") equals `checkbox`
   - Expected: node.has_attr("type") is true
   - Expected: node.get_attr("type") equals `radio`
   - Expected: node.has_attr("type") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("set_attr / get_attr / has_attr / remove_attr round-trip")
var node = BeDomNode.element("input")
expect(node.get_attr("type")).to_equal("")
expect(node.has_attr("type")).to_equal(false)
node.set_attr("type", "checkbox")
expect(node.get_attr("type")).to_equal("checkbox")
expect(node.has_attr("type")).to_equal(true)
node.set_attr("type", "radio")
expect(node.get_attr("type")).to_equal("radio")
node.remove_attr("type")
expect(node.has_attr("type")).to_equal(false)
```

</details>

#### set_style normalizes property names and ignores unknown properties

- set_style normalizes property names and ignores unknown properties
   - Expected: node.style.display equals `flex`
   - Expected: node.style.color equals `red`
   - Expected: node.style.background_color equals `blue`
   - Expected: node.style.font_weight equals `bold`
   - Expected: node.style.text_align equals `center`
   - Expected: node.style.position equals `absolute`
   - Expected: node.style.overflow equals `hidden`
   - Expected: node.style.float_css equals `left`
   - Expected: node.style.clear_css equals `both`
   - Expected: node.style.width equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("set_style normalizes property names and ignores unknown properties")
var node = BeDomNode.element("div")
node.set_style(" Display ", " flex ")
node.set_style("COLOR", "red")
node.set_style("background-color", "blue")
node.set_style("font-weight", "bold")
node.set_style("text-align", "center")
node.set_style("position", "absolute")
node.set_style("overflow", "hidden")
node.set_style("float", "left")
node.set_style("clear", "both")
expect(node.style.display).to_equal("flex")
expect(node.style.color).to_equal("red")
expect(node.style.background_color).to_equal("blue")
expect(node.style.font_weight).to_equal("bold")
expect(node.style.text_align).to_equal("center")
expect(node.style.position).to_equal("absolute")
expect(node.style.overflow).to_equal("hidden")
expect(node.style.float_css).to_equal("left")
expect(node.style.clear_css).to_equal("both")
# Unknown to set_style: silently ignored, width stays default.
node.set_style("width", "10px")
expect(node.style.width).to_equal(0.0)
```

</details>

#### normalizes DOM event type names

- normalizes DOM event type names
   - Expected: normalize_dom_event_type("onClick") equals `click`
   - Expected: normalize_dom_event_type("  CLICK  ") equals `click`
   - Expected: normalize_dom_event_type("online") equals `online`
   - Expected: normalize_dom_event_type("offline") equals `offline`
   - Expected: normalize_dom_event_type("on") equals `on`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("normalizes DOM event type names")
expect(normalize_dom_event_type("onClick")).to_equal("click")
expect(normalize_dom_event_type("  CLICK  ")).to_equal("click")
expect(normalize_dom_event_type("online")).to_equal("online")
expect(normalize_dom_event_type("offline")).to_equal("offline")
expect(normalize_dom_event_type("on")).to_equal("on")
```

</details>

#### event listeners dedupe, tombstone on remove, and reuse tombstones

- event listeners dedupe, tombstone on remove, and reuse tombstones
   - Expected: node.event_listener_types.len() equals `1`
   - Expected: node.event_listener_types.len() equals `2`
   - Expected: node.event_listener_types.len() equals `2`
   - Expected: node.event_listener_types[0] equals ``
   - Expected: node.event_listener_types.len() equals `2`
   - Expected: node.event_listener_types[0] equals `focus`
   - Expected: node.event_listener_actions[0] equals `a3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("event listeners dedupe, tombstone on remove, and reuse tombstones")
var node = BeDomNode.element("button")
node.add_event_listener("onclick", "a1")
node.add_event_listener("click", "a1")   # duplicate after normalize
expect(node.event_listener_types.len()).to_equal(1)
node.add_event_listener("keydown", "a2")
expect(node.event_listener_types.len()).to_equal(2)
node.remove_event_listener("click", "a1")
expect(node.event_listener_types.len()).to_equal(2)
expect(node.event_listener_types[0]).to_equal("")
# Tombstone slot is reused instead of growing the arrays.
node.add_event_listener("focus", "a3")
expect(node.event_listener_types.len()).to_equal(2)
expect(node.event_listener_types[0]).to_equal("focus")
expect(node.event_listener_actions[0]).to_equal("a3")
```

</details>

#### finds a nested node by author id attribute and by selector

- finds a nested node by author id attribute and by selector


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("finds a nested node by author id attribute and by selector")
var inner = BeDomNode.element_with_id(3, "span")
inner.set_attr("id", "target")
var mid = BeDomNode.element_with_id(2, "section")
mid.add_child(inner)
var root = BeDomNode.element_with_id(1, "div")
root.add_child(mid)

match be_dom_find_by_id(root, "target"):
    Some(found) => expect(found.tag_name).to_equal("span")
    nil => _fail("expected #target via find_by_id")
match be_dom_query_selector(root, "#target"):
    Some(found) => expect(found.node_id).to_equal(3)
    nil => _fail("expected #target via selector")
match be_dom_query_selector(root, "section"):
    Some(found) => expect(found.node_id).to_equal(2)
    nil => _fail("expected section via selector")
```

</details>

#### does not resolve an absent author id

- does not resolve an absent author id


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not resolve an absent author id")
var inner = BeDomNode.element_with_id(2, "span")
inner.set_attr("id", "present")
var root = BeDomNode.element_with_id(1, "div")
root.add_child(inner)
match be_dom_find_by_id(root, "absent"):
    Some(_) => _fail("absent id must not resolve")
    nil => expect(true).to_equal(true)
match be_dom_query_selector(root, "#absent"):
    Some(_) => _fail("absent id selector must not resolve")
    nil => expect(true).to_equal(true)
# And a node without an id attribute never matches a real query.
match be_dom_find_by_id(root, "present"):
    Some(found) => expect(found.node_id).to_equal(2)
    nil => _fail("expected #present")
```

</details>

#### dom events normalize type and gate default prevention on cancelable

- dom events normalize type and gate default prevention on cancelable
   - Expected: not_cancelable.event_type equals `click`
   - Expected: not_cancelable.default_prevented is false
   - Expected: cancelable.default_prevented is true
   - Expected: cancelable.propagation_stopped is true
   - Expected: cancelable.immediate_propagation_stopped is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("dom events normalize type and gate default prevention on cancelable")
var not_cancelable = BeDomEvent.create("onClick", "", true, false)
expect(not_cancelable.event_type).to_equal("click")
not_cancelable.prevent_default()
expect(not_cancelable.default_prevented).to_equal(false)
var cancelable = BeDomEvent.create("keydown", "", true, true)
cancelable.prevent_default()
cancelable.stop_immediate_propagation()
expect(cancelable.default_prevented).to_equal(true)
expect(cancelable.propagation_stopped).to_equal(true)
expect(cancelable.immediate_propagation_stopped).to_equal(true)
```

</details>

#### collects nested text content depth-first

- collects nested text content depth-first
   - Expected: be_dom_get_text_content(root) equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("collects nested text content depth-first")
var strong = BeDomNode.element_with_id(4, "strong")
strong.add_child(BeDomNode.text_node(5, "world"))
var p = BeDomNode.element_with_id(2, "p")
p.add_child(BeDomNode.text_node(3, "hello "))
p.add_child(strong)
var root = BeDomNode.element_with_id(1, "div")
root.add_child(p)
expect(be_dom_get_text_content(root)).to_equal("hello world")
```

</details>

### html_string_to_dom parsing

#### parses nested elements with id, class and text

- parses nested elements with id, class and text
   - Expected: dom.get_attr("id") equals `html-root`
   - Expected: dom.children.len() equals `1`
   - Expected: div.tag_name equals `div`
   - Expected: div.get_attr("id") equals `main`
   - Expected: div.get_attr("class") equals `box wide`
   - Expected: div.children.len() equals `1`
   - Expected: div.children[0].tag_name equals `span`
   - Expected: div.children[0].children[0].data equals `hi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses nested elements with id, class and text")
val dom = html_string_to_dom(
    "<div id=\"main\" class=\"box wide\"><span>hi</span></div>")
expect(dom.get_attr("id")).to_equal("html-root")
expect(dom.children.len()).to_equal(1)
val div = dom.children[0]
expect(div.tag_name).to_equal("div")
expect(div.get_attr("id")).to_equal("main")
expect(div.get_attr("class")).to_equal("box wide")
expect(div.children.len()).to_equal(1)
expect(div.children[0].tag_name).to_equal("span")
expect(div.children[0].children[0].data).to_equal("hi")
```

</details>

#### parses void and self-closing elements without nesting

- parses void and self-closing elements without nesting
   - Expected: dom.children.len() equals `2`
   - Expected: ul.tag_name equals `ul`
   - Expected: ul.children.len() equals `2`
   - Expected: be_dom_get_text_content(ul) equals `onetwo`
   - Expected: dom.children[1].tag_name equals `br`
   - Expected: dom.children[1].children.len() equals `0`
   - Expected: dom2.children.len() equals `2`
   - Expected: dom2.children[0].tag_name equals `img`
   - Expected: dom2.children[0].get_attr("src") equals `a.png`
   - Expected: dom2.children[1].tag_name equals `p`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses void and self-closing elements without nesting")
val dom = html_string_to_dom("<ul><li>one</li><li>two</li></ul><br>")
expect(dom.children.len()).to_equal(2)
val ul = dom.children[0]
expect(ul.tag_name).to_equal("ul")
expect(ul.children.len()).to_equal(2)
expect(be_dom_get_text_content(ul)).to_equal("onetwo")
expect(dom.children[1].tag_name).to_equal("br")
expect(dom.children[1].children.len()).to_equal(0)

val dom2 = html_string_to_dom("<img src=\"a.png\"/><p>after</p>")
expect(dom2.children.len()).to_equal(2)
expect(dom2.children[0].tag_name).to_equal("img")
expect(dom2.children[0].get_attr("src")).to_equal("a.png")
expect(dom2.children[1].tag_name).to_equal("p")
```

</details>

#### applies inline style declarations from the style attribute

- applies inline style declarations from the style attribute
   - Expected: div.style.color equals `red`
   - Expected: div.style.font_weight equals `bold`
   - Expected: div.style.text_align equals `center`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies inline style declarations from the style attribute")
val dom = html_string_to_dom(
    "<div style=\"color: red; font-weight: bold; text-align: center\"></div>")
val div = dom.children[0]
expect(div.style.color).to_equal("red")
expect(div.style.font_weight).to_equal("bold")
expect(div.style.text_align).to_equal("center")
```

</details>

#### keeps generic attributes and quoted values

- keeps generic attributes and quoted values
   - Expected: input.get_attr("type") equals `text`
   - Expected: input.get_attr("data-role") equals `field`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps generic attributes and quoted values")
val dom = html_string_to_dom(
    "<input type=\"text\" data-role='field'>")
val input = dom.children[0]
expect(input.get_attr("type")).to_equal("text")
expect(input.get_attr("data-role")).to_equal("field")
```

</details>

#### recovers from unclosed tags and malformed trailing markup

- recovers from unclosed tags and malformed trailing markup
   - Expected: dom.children.len() equals `1`
   - Expected: div.tag_name equals `div`
   - Expected: div.children[0].tag_name equals `span`
   - Expected: be_dom_get_text_content(div) equals `deep`
   - Expected: dom2.children.len() equals `1`
   - Expected: dom2.children[0].tag_name equals `#text`
   - Expected: dom2.children[0].data equals `plain text only`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("recovers from unclosed tags and malformed trailing markup")
val dom = html_string_to_dom("<div><span>deep")
expect(dom.children.len()).to_equal(1)
val div = dom.children[0]
expect(div.tag_name).to_equal("div")
expect(div.children[0].tag_name).to_equal("span")
expect(be_dom_get_text_content(div)).to_equal("deep")

val dom2 = html_string_to_dom("plain text only")
expect(dom2.children.len()).to_equal(1)
expect(dom2.children[0].tag_name).to_equal("#text")
expect(dom2.children[0].data).to_equal("plain text only")
```

</details>

### widget_to_dom conversion

#### maps widget kinds to their HTML tags

- maps widget kinds to their HTML tags
   - Expected: dom.tag_name equals `tags[i]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("maps widget kinds to their HTML tags")
val kinds = ["panel", "button", "text", "input", "list",
             "image", "divider", "heading"]
val tags = ["div", "button", "span", "input", "ul",
            "img", "hr", "h2"]
var i = 0
while i < kinds.len():
    val w = WidgetNode.new("w2d-tag-" + kinds[i], kinds[i])
    val dom = widget_to_dom(w, _plain_state(w))
    expect(dom.tag_name).to_equal(tags[i])
    i = i + 1
```

</details>

#### propagates widget ids into the id attribute, findable by id

- propagates widget ids into the id attribute, findable by id
   - Expected: dom.get_attr("id") equals `w2d-id-root`
   - Expected: dom.children.len() equals `1`
   - Expected: dom.children[0].get_attr("id") equals `w2d-id-child`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("propagates widget ids into the id attribute, findable by id")
val root = WidgetNode.new("w2d-id-root", "panel")
val child = WidgetNode.new("w2d-id-child", "button")
root.add_child(child)
val dom = widget_to_dom(root, _plain_state(root))
expect(dom.get_attr("id")).to_equal("w2d-id-root")
expect(dom.children.len()).to_equal(1)
expect(dom.children[0].get_attr("id")).to_equal("w2d-id-child")
match be_dom_find_by_id(dom, "w2d-id-child"):
    Some(found) => expect(found.tag_name).to_equal("button")
    nil => _fail("expected converted child via find_by_id")
```

</details>

#### adds the widget kind as a class and marks the focused root

- adds the widget kind as a class and marks the focused root
   - Expected: dom.get_attr("class") equals `panel focused`
   - Expected: dom.children[0].get_attr("class") equals `button`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("adds the widget kind as a class and marks the focused root")
val root = WidgetNode.new("w2d-cls-root", "panel")
val child = WidgetNode.new("w2d-cls-child", "button")
root.add_child(child)
val dom = widget_to_dom(root, _plain_state(root))
# UIState.new focuses the tree root.
expect(dom.get_attr("class")).to_equal("panel focused")
expect(dom.children[0].get_attr("class")).to_equal("button")
```

</details>

#### gives the focused root a solid focus ring

- gives the focused root a solid focus ring
   - Expected: dom.style.border_width equals `2.0`
   - Expected: dom.style.border_color equals `#58A6FF`
   - Expected: dom.style.border_style equals `solid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gives the focused root a solid focus ring")
val root = WidgetNode.new("w2d-focus-root", "panel")
val dom = widget_to_dom(root, _plain_state(root))
expect(dom.style.border_width).to_equal(2.0)
expect(dom.style.border_color).to_equal("#58A6FF")
expect(dom.style.border_style).to_equal("solid")
```

</details>

#### renders the text prop as a child text node

- renders the text prop as a child text node
   - Expected: button.children.len() equals `1`
   - Expected: button.children[0].tag_name equals `#text`
   - Expected: button.children[0].data equals `Click me`
   - Expected: be_dom_get_text_content(dom) equals `Click me`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders the text prop as a child text node")
val root = WidgetNode.new("w2d-text-root", "panel")
val child = WidgetNode.new("w2d-text-child", "button")
child.set_prop("text", "Click me")
root.add_child(child)
val dom = widget_to_dom(root, _plain_state(root))
val button = dom.children[0]
expect(button.children.len()).to_equal(1)
expect(button.children[0].tag_name).to_equal("#text")
expect(button.children[0].data).to_equal("Click me")
expect(be_dom_get_text_content(dom)).to_equal("Click me")
```

</details>

#### transfers title, value and placeholder props as attributes

- transfers title, value and placeholder props as attributes
   - Expected: input.get_attr("title") equals `Name`
   - Expected: input.get_attr("value") equals `simple`
   - Expected: input.get_attr("placeholder") equals `type here`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("transfers title, value and placeholder props as attributes")
val root = WidgetNode.new("w2d-attr-root", "panel")
val child = WidgetNode.new("w2d-attr-child", "input")
child.set_prop("title", "Name")
child.set_prop("value", "simple")
child.set_prop("placeholder", "type here")
root.add_child(child)
val dom = widget_to_dom(root, _plain_state(root))
val input = dom.children[0]
expect(input.get_attr("title")).to_equal("Name")
expect(input.get_attr("value")).to_equal("simple")
expect(input.get_attr("placeholder")).to_equal("type here")
```

</details>

#### maps widget layouts to flex and grid styles

- maps widget layouts to flex and grid styles
   - Expected: vdom.style.display equals `flex`
   - Expected: vdom.style.flex_direction equals `column`
   - Expected: hdom.style.display equals `flex`
   - Expected: hdom.style.flex_direction equals `row`
   - Expected: gdom.style.display equals `grid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("maps widget layouts to flex and grid styles")
val vbox = WidgetNode.new("w2d-layout-vbox", "panel")
val vdom = widget_to_dom(vbox, _plain_state(vbox))
expect(vdom.style.display).to_equal("flex")
expect(vdom.style.flex_direction).to_equal("column")
val hbox = WidgetNode.new("w2d-layout-hbox", "panel")
hbox.set_layout("hbox")
val hdom = widget_to_dom(hbox, _plain_state(hbox))
expect(hdom.style.display).to_equal("flex")
expect(hdom.style.flex_direction).to_equal("row")
val grid = WidgetNode.new("w2d-layout-grid", "panel")
grid.set_layout("grid")
val gdom = widget_to_dom(grid, _plain_state(grid))
expect(gdom.style.display).to_equal("grid")
```

</details>

#### hides invisible widgets with display none

- hides invisible widgets with display none
   - Expected: dom.children[0].style.display equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("hides invisible widgets with display none")
val root = WidgetNode.new("w2d-vis-root", "panel")
val child = WidgetNode.new("w2d-vis-child", "text")
child.set_visible(false)
root.add_child(child)
val dom = widget_to_dom(root, _plain_state(root))
expect(dom.children[0].style.display).to_equal("none")
```

</details>

#### applies background props to the background-color style

- applies background props to the background-color style
   - Expected: dom.children[0].style.background_color equals `#123456`
   - Expected: dom.children[1].style.background_color equals `#654321`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies background props to the background-color style")
val root = WidgetNode.new("w2d-bg-root", "panel")
val child = WidgetNode.new("w2d-bg-child", "scroll")
child.set_prop("background", "#123456")
val fallback = WidgetNode.new("w2d-bg-fallback", "scroll")
fallback.set_prop("bg", "#654321")
root.add_child(child)
root.add_child(fallback)
val dom = widget_to_dom(root, _plain_state(root))
expect(dom.children[0].style.background_color).to_equal("#123456")
expect(dom.children[1].style.background_color).to_equal("#654321")
```

</details>

#### converts nested children recursively in document order

- converts nested children recursively in document order
   - Expected: dom.children.len() equals `1`
   - Expected: row_dom.get_attr("id") equals `w2d-nest-row`
   - Expected: row_dom.children.len() equals `2`
   - Expected: row_dom.children[0].tag_name equals `button`
   - Expected: row_dom.children[0].get_attr("id") equals `w2d-nest-a`
   - Expected: row_dom.children[1].tag_name equals `span`
   - Expected: row_dom.children[1].get_attr("id") equals `w2d-nest-b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts nested children recursively in document order")
val root = WidgetNode.new("w2d-nest-root", "panel")
val row = WidgetNode.new("w2d-nest-row", "panel")
val leaf_a = WidgetNode.new("w2d-nest-a", "button")
val leaf_b = WidgetNode.new("w2d-nest-b", "text")
row.add_child(leaf_a)
row.add_child(leaf_b)
root.add_child(row)
val dom = widget_to_dom(root, _plain_state(root))
expect(dom.children.len()).to_equal(1)
val row_dom = dom.children[0]
expect(row_dom.get_attr("id")).to_equal("w2d-nest-row")
expect(row_dom.children.len()).to_equal(2)
expect(row_dom.children[0].tag_name).to_equal("button")
expect(row_dom.children[0].get_attr("id")).to_equal("w2d-nest-a")
expect(row_dom.children[1].tag_name).to_equal("span")
expect(row_dom.children[1].get_attr("id")).to_equal("w2d-nest-b")
```

</details>

#### ui_tree_to_dom wraps the converted root in a ui-root container

- ui_tree_to_dom wraps the converted root in a ui-root container
   - Expected: dom.get_attr("id") equals `ui-root`
   - Expected: dom.get_attr("class") equals `ui-container`
   - Expected: dom.style.display equals `flex`
   - Expected: dom.style.flex_direction equals `column`
   - Expected: dom.children.len() equals `1`
   - Expected: dom.children[0].get_attr("id") equals `w2d-tree-root`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("ui_tree_to_dom wraps the converted root in a ui-root container")
val root = WidgetNode.new("w2d-tree-root", "panel")
val tree = UITree.new(root).with_theme("plain")
val dom = ui_tree_to_dom(tree, UIState.new(tree))
expect(dom.get_attr("id")).to_equal("ui-root")
expect(dom.get_attr("class")).to_equal("ui-container")
expect(dom.style.display).to_equal("flex")
expect(dom.style.flex_direction).to_equal("column")
expect(dom.children.len()).to_equal(1)
expect(dom.children[0].get_attr("id")).to_equal("w2d-tree-root")
match be_dom_find_by_id(dom, "w2d-tree-root"):
    Some(found) => expect(found.tag_name).to_equal("div")
    nil => _fail("expected converted widget under ui-root")
```

</details>

#### applies glass theme classes and colors under the default theme

- applies glass theme classes and colors under the default theme
   - Expected: dom.get_attr("class") equals `panel widget-panel focused`
   - Expected: button.get_attr("class") equals `button widget-button`
   - Expected: button.style.background_color equals `#0A84FF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies glass theme classes and colors under the default theme")
val root = WidgetNode.new("w2d-glass-root", "panel")
val child = WidgetNode.new("w2d-glass-child", "button")
root.add_child(child)
# Default tree theme is glass_dark.
val state = UIState.new(UITree.new(root))
val dom = widget_to_dom(root, state)
expect(dom.get_attr("class")).to_equal("panel widget-panel focused")
val button = dom.children[0]
expect(button.get_attr("class")).to_equal("button widget-button")
expect(button.style.background_color).to_equal("#0A84FF")
```

</details>

### DOM identity index for GPU offload snapshots

#### rejects a non-positive document generation

- rejects a non-positive document generation


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a non-positive document generation")
match DomDocumentGeneration.create(0):
    Ok(_) => _fail("generation 0 must be rejected")
    Err(_) => expect(true).to_equal(true)
match dom_identity_index_build(_identity_doc(), DomDocumentGeneration(value: 0)):
    Ok(_) => _fail("build must reject generation 0")
    Err(msg) => expect(msg).to_equal("invalid_generation")
```

</details>

#### indexes every node and resolves author ids to routes

- indexes every node and resolves author ids to routes
   - Expected: index.counters.node_count equals `6`
   - Expected: index.counters.duplicate_author_id_count equals `0`
   - Expected: route.node_id equals `4`
   - Expected: dom_node_route_text(route) equals `dom-route-v1:1:4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("indexes every node and resolves author ids to routes")
val index = _built_index(1)
expect(index.counters.node_count).to_equal(6)
expect(index.counters.duplicate_author_id_count).to_equal(0)
match index.route_for_author_id("user"):
    Some(route) =>
        expect(route.node_id).to_equal(4)
        expect(dom_node_route_text(route)).to_equal("dom-route-v1:1:4")
    nil => _fail("expected route for #user")
match index.route_for_author_id("nonexistent"):
    Some(_) => _fail("must not resolve unknown author id")
    nil => expect(true).to_equal(true)
match index.route_for_author_id(""):
    Some(_) => _fail("empty author id must not resolve")
    nil => expect(true).to_equal(true)
```

</details>

#### round-trips author id and structural path through routes

- round-trips author id and structural path through routes
   - Expected: path.len() equals `2`
   - Expected: path[0] equals `0`
   - Expected: path[1] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips author id and structural path through routes")
val index = _built_index(1)
match index.route_for_author_id("login"):
    Some(form_route) =>
        match index.author_id_for_route(form_route):
            Some(author) => expect(author).to_equal("login")
            nil => _fail("expected author id for form route")
        match index.path_for_route(form_route):
            Some(path) =>
                expect(path.len()).to_equal(2)
                expect(path[0]).to_equal(0)
                expect(path[1]).to_equal(0)
            nil => _fail("expected path for form route")
    nil => _fail("expected route for #login")
```

</details>

#### produces a root-first event path for a nested control

- produces a root-first event path for a nested control
   - Expected: path.len() equals `4`
   - Expected: path[0].node_id equals `1`
   - Expected: path[1].node_id equals `2`
   - Expected: path[2].node_id equals `3`
   - Expected: path[3].node_id equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("produces a root-first event path for a nested control")
val index = _built_index(1)
match index.route_for_author_id("user"):
    Some(input_route) =>
        val path = index.event_path_for_route(input_route)
        expect(path.len()).to_equal(4)
        expect(path[0].node_id).to_equal(1)
        expect(path[1].node_id).to_equal(2)
        expect(path[2].node_id).to_equal(3)
        expect(path[3].node_id).to_equal(4)
    nil => _fail("expected route for #user")
```

</details>

#### resolves form ownership and explicit label association

- resolves form ownership and explicit label association
   - Expected: index.contains_route(label_route) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("resolves form ownership and explicit label association")
val index = _built_index(1)
match index.route_for_author_id("user"):
    Some(input_route) =>
        match index.form_owner_for_route(input_route):
            Some(owner) => expect(owner.node_id).to_equal(3)
            nil => _fail("expected form owner for input")
    nil => _fail("expected route for #user")
val label_route = DomNodeRoute(generation: _generation(1), node_id: 6)
expect(index.contains_route(label_route)).to_equal(true)
match index.control_for_label_route(label_route):
    Some(control) => expect(control.node_id).to_equal(4)
    nil => _fail("expected control for explicit label")
```

</details>

#### keeps routes stable across rebuilds of identical content

- keeps routes stable across rebuilds of identical content
   - Expected: second.contains_route(route_a) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps routes stable across rebuilds of identical content")
val first = _built_index(7)
val second = _built_index(7)
match first.route_for_author_id("user"):
    Some(route_a) =>
        match second.route_for_author_id("user"):
            Some(route_b) =>
                expect(dom_node_route_text(route_a))
                    .to_equal(dom_node_route_text(route_b))
                # A route captured from the first build resolves
                # against the rebuilt index of the same generation.
                expect(second.contains_route(route_a)).to_equal(true)
            nil => _fail("expected route in second build")
    nil => _fail("expected route in first build")
```

</details>

#### rejects routes captured from a replaced generation

- rejects routes captured from a replaced generation
   - Expected: new_index.contains_route(stale_route) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects routes captured from a replaced generation")
val old_index = _built_index(1)
val new_index = _built_index(2)
match old_index.route_for_author_id("user"):
    Some(stale_route) =>
        expect(new_index.contains_route(stale_route)).to_equal(false)
        match new_index.author_id_for_route(stale_route):
            Some(_) => _fail("stale route must not resolve")
            nil => expect(true).to_equal(true)
        match new_index.path_for_route(stale_route):
            Some(_) => _fail("stale route must have no path")
            nil => expect(true).to_equal(true)
    nil => _fail("expected route in old index")
```

</details>

#### serializes and parses routes with strict canonical form

- serializes and parses routes with strict canonical form
   - Expected: encoded equals `dom-route-v1:3:12`
   - Expected: parsed.generation.value equals `3`
   - Expected: parsed.node_id equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("serializes and parses routes with strict canonical form")
val route = DomNodeRoute(generation: _generation(3), node_id: 12)
val encoded = dom_node_route_text(route)
expect(encoded).to_equal("dom-route-v1:3:12")
match dom_node_route_parse(encoded):
    Ok(parsed) =>
        expect(parsed.generation.value).to_equal(3)
        expect(parsed.node_id).to_equal(12)
    Err(_) => _fail("expected round-trip parse")
match dom_node_route_parse("dom-route-v1:03:12"):
    Ok(_) => _fail("non-canonical generation must fail")
    Err(msg) => expect(msg).to_equal("invalid_route")
match dom_node_route_parse("dom-route-v2:1:2"):
    Ok(_) => _fail("unknown version must fail")
    Err(msg) => expect(msg).to_equal("invalid_route")
match dom_node_route_parse("dom-route-v1:1"):
    Ok(_) => _fail("missing segment must fail")
    Err(msg) => expect(msg).to_equal("invalid_route")
```

</details>

#### rejects a node with a non-positive node id at build time

- rejects a node with a non-positive node id at build time


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a node with a non-positive node id at build time")
var zero_child = BeDomNode.element("span")   # node_id 0
var bad_root = _el(1, "html")
bad_root.add_child(zero_child)
match dom_identity_index_build(bad_root, _generation(1)):
    Ok(_) => _fail("node_id 0 accepted by identity build")
    Err(msg) => expect(msg).to_equal("invalid_node_id")
```

</details>

#### rejects duplicate node ids at build time

- rejects duplicate node ids at build time


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects duplicate node ids at build time")
var dup_a = _el(2, "div")
var dup_b = _el(2, "span")
var root = _el(1, "html")
root.add_child(dup_a)
root.add_child(dup_b)
match dom_identity_index_build(root, _generation(1)):
    Ok(_) => _fail("duplicate node_id accepted by identity build")
    Err(msg) => expect(msg).to_equal("duplicate_node_id")
```

</details>

#### counts duplicate author ids and keeps the first binding

- counts duplicate author ids and keeps the first binding
   - Expected: index.counters.duplicate_author_id_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("counts duplicate author ids and keeps the first binding")
var first = _el(2, "div")
first.set_attr("id", "dup")
var second = _el(3, "span")
second.set_attr("id", "dup")
var root = _el(1, "html")
root.add_child(first)
root.add_child(second)
match dom_identity_index_build(root, _generation(1)):
    Ok(index) =>
        expect(index.counters.duplicate_author_id_count).to_equal(1)
        # First-wins: the duplicate never rebinds the route.
        match index.route_for_author_id("dup"):
            Some(route) => expect(route.node_id).to_equal(2)
            nil => _fail("expected route for duplicated author id")
    Err(msg) => _fail("identity build failed: " + msg)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 38 |
| Active scenarios | 38 |
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

- Canonical SPipe generation for source `7ec47ca384c6b14178d06e010303c956c37baba39d0494f8a0877f58347a64a8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7ec47ca384c6b14178d06e010303c956c37baba39d0494f8a0877f58347a64a8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7ec47ca384c6b14178d06e010303c956c37baba39d0494f8a0877f58347a64a8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_build_gpu_offload_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_build_gpu_offload_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_build_gpu_offload_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_build_gpu_offload_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_build_gpu_offload_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 46 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_build_gpu_offload_spec.spl:100:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates elements and text nodes with expected defaults' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_build_gpu_offload_spec.spl:126:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'add_child reparents a value copy of the child' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_build_gpu_offload_spec.spl:140:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'set_attr / get_attr / has_attr / remove_attr round-trip' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
