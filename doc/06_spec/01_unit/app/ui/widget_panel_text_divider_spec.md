# Widget Panel Text Divider Specification

> <details>

<!-- sdn-diagram:id=widget_panel_text_divider_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=widget_panel_text_divider_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

widget_panel_text_divider_spec -> common
widget_panel_text_divider_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=widget_panel_text_divider_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 68 | 68 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Widget Panel Text Divider Specification

## Scenarios

### Panel Widget

#### creation

#### creates a panel with kind panel and vbox layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = panel("panel_create_1", "Title", [])
expect p.kind to_equal "panel"
expect p.layout to_equal "vbox"
expect p.visible to_equal true
expect p.focused to_equal false
```

</details>

#### stores the title as a prop

1. expect p get prop
2. expect p has prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = panel("panel_title_2", "My Title", [])
expect p.get_prop("title") to_equal "My Title"
expect p.has_prop("title") to_equal true
```

</details>

#### assigns the given id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = panel("panel_id_3", "T", [])
expect p.id to_equal "panel_id_3"
```

</details>

#### children

#### has correct child count with two text children

1. expect p child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t1 = text_widget("panel_child_t1_4", "A")
val t2 = text_widget("panel_child_t2_4", "B")
val p = panel("panel_children_4", "P", [t1, t2])
expect p.child_count() to_equal 2
```

</details>

#### retrieves children in order

1. expect kids len


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t1 = text_widget("panel_order_t1_5", "First")
val t2 = text_widget("panel_order_t2_5", "Second")
val p = panel("panel_order_5", "P", [t1, t2])
val kids = p.children()
expect kids.len() to_equal 2
expect kids[0].id to_equal "panel_order_t1_5"
expect kids[1].id to_equal "panel_order_t2_5"
```

</details>

#### has zero children when created empty

1. expect p child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = panel("panel_empty_6", "Empty", [])
expect p.child_count() to_equal 0
```

</details>

#### layout override

#### changes layout from vbox to hbox via set_layout

1. var p = panel
2. p = p set layout


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = panel("panel_layout_7", "P", [])
p = p.set_layout("hbox")
expect p.layout to_equal "hbox"
```

</details>

#### preserves other fields after set_layout

1. var p = panel
2. p = p set layout


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = panel("panel_layout_keep_8", "Keep", [])
p = p.set_layout("grid")
expect p.kind to_equal "panel"
expect p.id to_equal "panel_layout_keep_8"
expect p.visible to_equal true
```

</details>

#### sizing modifiers

#### sets flex prop via with_flex

1. expect p2 get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = panel("panel_flex_9", "F", [])
val p2 = with_flex(p, 2)
expect p2.get_prop("flex") to_equal "2"
```

</details>

#### sets width prop via with_width

1. expect p2 get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = panel("panel_width_10", "W", [])
val p2 = with_width(p, 200)
expect p2.get_prop("width") to_equal "200"
```

</details>

#### sets height prop via with_height

1. expect p2 get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = panel("panel_height_11", "H", [])
val p2 = with_height(p, 100)
expect p2.get_prop("height") to_equal "100"
```

</details>

#### visibility

#### hides panel with set_visible false

1. var p = panel
2. p = p set visible


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = panel("panel_vis_12", "V", [])
p = p.set_visible(false)
expect p.visible to_equal false
```

</details>

#### shows panel with set_visible true

1. var p = panel
2. p = p set visible
3. p = p set visible


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = panel("panel_vis_show_13", "V", [])
p = p.set_visible(false)
p = p.set_visible(true)
expect p.visible to_equal true
```

</details>

#### nested panels

#### supports panel containing panel

1. expect outer child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inner = panel("panel_inner_14", "Inner", [])
val outer = panel("panel_outer_14", "Outer", [inner])
expect outer.child_count() to_equal 1
val child = outer.children()[0]
expect child.id to_equal "panel_inner_14"
expect child.kind to_equal "panel"
```

</details>

#### supports deeply nested panels

1. expect top child count
2. expect mid child child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deep = panel("panel_deep_15", "Deep", [])
val mid = panel("panel_mid_15", "Mid", [deep])
val top = panel("panel_top_15", "Top", [mid])
expect top.child_count() to_equal 1
val mid_child = top.children()[0]
expect mid_child.child_count() to_equal 1
val deep_child = mid_child.children()[0]
expect deep_child.id to_equal "panel_deep_15"
```

</details>

#### HTML rendering

#### contains widget-panel class

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = panel("panel_html_16", "TestTitle", [])
val tree = build_tree(p)
val state = init_state(tree)
val html = render_html_widget(p, state)
expect html to_contain "widget-panel"
```

</details>

#### contains panel-title with title text

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = panel("panel_html_title_17", "MyTitle", [])
val tree = build_tree(p)
val state = init_state(tree)
val html = render_html_widget(p, state)
expect html to_contain "panel-title"
expect html to_contain "MyTitle"
```

</details>

#### contains layout-vbox class for vbox layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = panel("panel_html_vbox_18", "V", [])
val tree = build_tree(p)
val state = init_state(tree)
val html = render_html_widget(p, state)
expect html to_contain "layout-vbox"
```

</details>

#### contains layout-hbox class for hbox layout

1. var p = panel
2. p = p set layout


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = panel("panel_html_hbox_19", "H", [])
p = p.set_layout("hbox")
val tree = build_tree(p)
val state = init_state(tree)
val html = render_html_widget(p, state)
expect html to_contain "layout-hbox"
```

</details>

#### contains focused class when focused

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = panel("panel_html_focus_20", "F", [])
val tree = build_tree(p)
val state = UIState(
    tree: tree,
    mode: UIMode.Normal,
    focused_id: "panel_html_focus_20",
    command_buffer: ""
)
val html = render_html_widget(p, state)
expect html to_contain "focused"
```

</details>

#### does not contain focused class when not focused

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = panel("panel_html_nofocus_21", "NF", [])
val tree = build_tree(p)
val state = UIState(
    tree: tree,
    mode: UIMode.Normal,
    focused_id: "other_widget",
    command_buffer: ""
)
val html = render_html_widget(p, state)
val has_focused = html.contains("focused")
expect has_focused to_equal false
```

</details>

#### renders children inside panel-content

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_widget("panel_html_child_t_22", "ChildText")
val p = panel("panel_html_child_22", "P", [t])
val tree = build_tree(p)
val state = init_state(tree)
val html = render_html_widget(p, state)
expect html to_contain "panel-content"
expect html to_contain "ChildText"
```

</details>

#### renders empty panel correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = panel("panel_html_empty_23", "Empty", [])
val tree = build_tree(p)
val state = init_state(tree)
val html = render_html_widget(p, state)
expect html to_contain "widget-panel"
expect html to_contain "Empty"
```

</details>

#### includes widget id attribute

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = panel("panel_html_id_24", "IdTest", [])
val tree = build_tree(p)
val state = init_state(tree)
val html = render_html_widget(p, state)
expect html to_contain "panel_html_id_24"
```

</details>

#### includes flex style when flex is set

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = panel("panel_html_flex_25", "Flex", [])
val p2 = with_flex(p, 3)
val tree = build_tree(p2)
val state = init_state(tree)
val html = render_html_widget(p2, state)
expect html to_contain "flex: 3"
```

</details>

#### includes width style when width is set

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = panel("panel_html_width_26", "W", [])
val p2 = with_width(p, 250)
val tree = build_tree(p2)
val state = init_state(tree)
val html = render_html_widget(p2, state)
expect html to_contain "width: 250px"
```

</details>

#### layout computation

#### computes inner area with 1-char border

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_widget("panel_layout_t_27", "Content")
val p = panel("panel_layout_27", "P", [t])
val rects = compute_layout(p, 0, 0, 80, 24)
# Panel itself occupies full area
val panel_rect = find_rect(rects, "panel_layout_27")
expect panel_rect != nil to_equal true
expect panel_rect.x to_equal 0
expect panel_rect.y to_equal 0
expect panel_rect.w to_equal 80
expect panel_rect.h to_equal 24
# Child is inside the 1-char border: (1, 1, 78, 22)
val child_rect = find_rect(rects, "panel_layout_t_27")
expect child_rect != nil to_equal true
expect child_rect.x to_equal 1
expect child_rect.y to_equal 1
expect child_rect.w to_equal 78
expect child_rect.h to_equal 22
```

</details>

#### returns only panel rect when panel has no children

1. expect rects len


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = panel("panel_layout_empty_28", "E", [])
val rects = compute_layout(p, 5, 10, 40, 20)
expect rects.len() to_equal 1
val r = rects[0]
expect r.id to_equal "panel_layout_empty_28"
expect r.x to_equal 5
expect r.y to_equal 10
expect r.w to_equal 40
expect r.h to_equal 20
```

</details>

### Text Widget

#### creation

#### creates a text widget with kind text

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_widget("text_create_30", "Hello")
expect t.kind to_equal "text"
expect t.id to_equal "text_create_30"
expect t.visible to_equal true
```

</details>

#### stores content as a prop

1. expect t get prop
2. expect t has prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_widget("text_content_31", "Hello World")
expect t.get_prop("content") to_equal "Hello World"
expect t.has_prop("content") to_equal true
```

</details>

#### content prop

#### returns content via get_prop

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_widget("text_getprop_32", "Some text here")
val content = t.get_prop("content")
expect content to_equal "Some text here"
```

</details>

#### handles empty content

1. expect t get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_widget("text_empty_33", "")
expect t.get_prop("content") to_equal ""
```

</details>

#### handles content with special characters

1. expect t get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_widget("text_special_34", "a < b > c & d")
expect t.get_prop("content") to_equal "a < b > c & d"
```

</details>

#### handles long content

1. expect t get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val long_text = "This is a much longer piece of text that spans many characters for testing purposes."
val t = text_widget("text_long_35", long_text)
expect t.get_prop("content") to_equal long_text
```

</details>

#### label widget

#### creates a text widget with label prop

1. expect l get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = label("label_create_36", "My Label")
expect l.kind to_equal "text"
expect l.get_prop("label") to_equal "My Label"
```

</details>

#### does not set content prop for label

1. expect l get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = label("label_nocontent_37", "Label Text")
expect l.get_prop("content") to_equal ""
```

</details>

#### label prop is separate from content prop

1. expect l has prop
2. expect l has prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = label("label_separate_38", "LabelVal")
expect l.has_prop("label") to_equal true
expect l.has_prop("content") to_equal false
```

</details>

#### HTML rendering

#### contains widget-text class

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_widget("text_html_39", "Hello")
val tree = build_tree(t)
val state = init_state(tree)
val html = render_html_widget(t, state)
expect html to_contain "widget-text"
```

</details>

#### contains the content text

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_widget("text_html_content_40", "Rendered Content")
val tree = build_tree(t)
val state = init_state(tree)
val html = render_html_widget(t, state)
expect html to_contain "Rendered Content"
```

</details>

#### contains focused class when focused

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_widget("text_html_focus_41", "Focused")
val tree = build_tree(t)
val state = UIState(
    tree: tree,
    mode: UIMode.Normal,
    focused_id: "text_html_focus_41",
    command_buffer: ""
)
val html = render_html_widget(t, state)
expect html to_contain "focused"
```

</details>

#### does not contain focused class when not focused

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_widget("text_html_nofocus_42", "NotFocused")
val tree = build_tree(t)
val state = UIState(
    tree: tree,
    mode: UIMode.Normal,
    focused_id: "some_other_id",
    command_buffer: ""
)
val html = render_html_widget(t, state)
val has_focused = html.contains("focused")
expect has_focused to_equal false
```

</details>

#### uses label when content is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = label("text_html_label_43", "LabelDisplay")
val tree = build_tree(l)
val state = init_state(tree)
val html = render_html_widget(l, state)
expect html to_contain "LabelDisplay"
```

</details>

#### prefers content over label

1. var t = text widget
2. t = t set prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = text_widget("text_html_prefer_44", "ContentVal")
t = t.set_prop("label", "LabelVal")
val tree = build_tree(t)
val state = init_state(tree)
val html = render_html_widget(t, state)
expect html to_contain "ContentVal"
```

</details>

#### includes widget id attribute

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_widget("text_html_id_45", "IdCheck")
val tree = build_tree(t)
val state = init_state(tree)
val html = render_html_widget(t, state)
expect html to_contain "text_html_id_45"
```

</details>

#### renders empty content as empty div

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_widget("text_html_empty_46", "")
val tree = build_tree(t)
val state = init_state(tree)
val html = render_html_widget(t, state)
expect html to_contain "widget-text"
expect html to_contain "text_html_empty_46"
```

</details>

#### prop manipulation

#### updates content via set_prop

1. var t = text widget
2. t = t set prop
3. expect t get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = text_widget("text_setprop_47", "Original")
t = t.set_prop("content", "Updated")
expect t.get_prop("content") to_equal "Updated"
```

</details>

#### adds custom props

1. var t = text widget
2. t = t set prop
3. expect t get prop
4. expect t has prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = text_widget("text_customprop_48", "Text")
t = t.set_prop("style", "bold")
expect t.get_prop("style") to_equal "bold"
expect t.has_prop("style") to_equal true
```

</details>

### Divider Widget

#### creation

#### creates a divider with kind divider

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = divider("divider_create_50")
expect d.kind to_equal "divider"
expect d.id to_equal "divider_create_50"
```

</details>

#### is visible by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = divider("divider_visible_51")
expect d.visible to_equal true
```

</details>

#### is not focused by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = divider("divider_focused_52")
expect d.focused to_equal false
```

</details>

#### has vbox as default layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = divider("divider_layout_53")
expect d.layout to_equal "vbox"
```

</details>

#### properties

#### has no custom properties by default

1. expect keys len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = divider("divider_noprops_54")
val keys = d.prop_keys()
expect keys.len() to_equal 0
```

</details>

#### can accept custom props via set_prop

1. var d = divider
2. d = d set prop
3. expect d get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = divider("divider_customprop_55")
d = d.set_prop("orientation", "horizontal")
expect d.get_prop("orientation") to_equal "horizontal"
```

</details>

#### HTML rendering

#### contains widget-divider class

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = divider("divider_html_56")
val tree = build_tree(d)
val state = init_state(tree)
val html = render_html_widget(d, state)
expect html to_contain "widget-divider"
```

</details>

#### renders as an hr tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = divider("divider_html_hr_57")
val tree = build_tree(d)
val state = init_state(tree)
val html = render_html_widget(d, state)
expect html to_contain "<hr"
```

</details>

#### includes the widget id

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = divider("divider_html_id_58")
val tree = build_tree(d)
val state = init_state(tree)
val html = render_html_widget(d, state)
expect html to_contain "divider_html_id_58"
```

</details>

#### is a self-closing tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = divider("divider_html_close_59")
val tree = build_tree(d)
val state = init_state(tree)
val html = render_html_widget(d, state)
expect html to_end_with "/>"
```

</details>

#### in panel

#### can be placed between text widgets in a panel

1. expect p child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t1 = text_widget("divider_panel_t1_60", "Above")
val sep = divider("divider_panel_sep_60")
val t2 = text_widget("divider_panel_t2_60", "Below")
val p = panel("divider_panel_60", "Split", [t1, sep, t2])
expect p.child_count() to_equal 3
val kids = p.children()
expect kids[0].kind to_equal "text"
expect kids[1].kind to_equal "divider"
expect kids[2].kind to_equal "text"
```

</details>

#### renders inside panel HTML output

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t1 = text_widget("divider_inpanel_t_61", "Content")
val sep = divider("divider_inpanel_sep_61")
val p = panel("divider_inpanel_61", "Panel", [t1, sep])
val tree = build_tree(p)
val state = init_state(tree)
val html = render_html_widget(p, state)
expect html to_contain "widget-divider"
expect html to_contain "widget-text"
expect html to_contain "widget-panel"
```

</details>

### Widget Integration

#### mixed widget trees

#### builds a tree with panel, text, and divider

1. expect ids len


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header = text_widget("integ_header_70", "Header")
val sep = divider("integ_sep_70")
val body = text_widget("integ_body_70", "Body")
val root = panel("integ_root_70", "App", [header, sep, body])
val tree = build_tree(root)
expect tree.title to_equal "Simple UI"
val ids = tree.all_widget_ids()
expect ids.len() to_be_greater_than 3
```

</details>

#### renders full tree with all widget types in HTML

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val title = text_widget("integ_title_71", "Welcome")
val sep = divider("integ_div_71")
val content = text_widget("integ_content_71", "Main content")
val root = panel("integ_panel_71", "Main", [title, sep, content])
val tree = build_tree(root)
val state = init_state(tree)
val html = render_html_widget(root, state)
expect html to_contain "widget-panel"
expect html to_contain "widget-text"
expect html to_contain "widget-divider"
expect html to_contain "Welcome"
expect html to_contain "Main content"
```

</details>

#### layout with mixed widgets

#### computes layout for panel with text and divider children

1. expect rects len


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_widget("integ_layout_t_72", "Text")
val d = divider("integ_layout_d_72")
val p = panel("integ_layout_p_72", "P", [t, d])
val rects = compute_layout(p, 0, 0, 80, 24)
# Panel rect + 2 child rects
expect rects.len() to_be_greater_than 2
val panel_rect = find_rect(rects, "integ_layout_p_72")
expect panel_rect != nil to_equal true
val text_rect = find_rect(rects, "integ_layout_t_72")
expect text_rect != nil to_equal true
val div_rect = find_rect(rects, "integ_layout_d_72")
expect div_rect != nil to_equal true
```

</details>

#### row and column containers

#### row creates hbox panel with children

1. expect r child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t1 = text_widget("integ_row_t1_73", "Left")
val t2 = text_widget("integ_row_t2_73", "Right")
val r = row("integ_row_73", [t1, t2])
expect r.kind to_equal "panel"
expect r.layout to_equal "hbox"
expect r.child_count() to_equal 2
```

</details>

#### column creates vbox panel with children

1. expect c child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t1 = text_widget("integ_col_t1_74", "Top")
val t2 = text_widget("integ_col_t2_74", "Bottom")
val c = column("integ_col_74", [t1, t2])
expect c.kind to_equal "panel"
expect c.layout to_equal "vbox"
expect c.child_count() to_equal 2
```

</details>

#### state initialization

#### creates state with focused id set to root

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = panel("integ_state_75", "Root", [])
val tree = build_tree(root)
val state = init_state(tree)
expect state.focused_id to_equal "integ_state_75"
```

</details>

#### creates state in normal mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = panel("integ_state_mode_76", "Root", [])
val tree = build_tree(root)
val state = init_state(tree)
val mode_name = state.mode_name()
expect mode_name to_equal "NORMAL"
```

</details>

#### find_by_id

#### finds nested widget by id

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deep_text = text_widget("integ_find_deep_77", "Deep")
val inner = panel("integ_find_inner_77", "Inner", [deep_text])
val outer = panel("integ_find_outer_77", "Outer", [inner])
val found = outer.find_by_id("integ_find_deep_77")
expect found != nil to_equal true
expect found.kind to_equal "text"
```

</details>

#### returns nil for non-existent id

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = panel("integ_find_none_78", "P", [])
val found = p.find_by_id("no_such_widget")
expect found to_be_nil
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/widget_panel_text_divider_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Panel Widget
- Text Widget
- Divider Widget
- Widget Integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 68 |
| Active scenarios | 68 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
