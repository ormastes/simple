# Widget Menubar Statusbar Specification

> <details>

<!-- sdn-diagram:id=widget_menubar_statusbar_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=widget_menubar_statusbar_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

widget_menubar_statusbar_spec -> common
widget_menubar_statusbar_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=widget_menubar_statusbar_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 64 | 64 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Widget Menubar Statusbar Specification

## Scenarios

### MenuBar creation

#### creates a menubar with correct kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = menubar("menu_create_1", ["File", "Edit", "View"])
expect bar.kind to_equal "menubar"
```

</details>

#### creates a menubar with correct id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = menubar("menu_create_2", ["File", "Edit", "View"])
expect bar.id to_equal "menu_create_2"
```

</details>

#### defaults visible to true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = menubar("menu_create_3", ["File"])
expect bar.visible to_equal true
```

</details>

#### defaults focused to false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = menubar("menu_create_4", ["File"])
expect bar.focused to_equal false
```

</details>

### MenuBar children

#### has correct child count for three items

1. expect bar child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = menubar("menu_child_1", ["File", "Edit", "View"])
expect bar.child_count() to_equal 3
```

</details>

#### first child has label File

1. expect first get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = menubar("menu_child_2", ["File", "Edit", "View"])
val first = bar.child_at(0)
expect first != nil to_equal true
expect first.get_prop("label") to_equal "File"
```

</details>

#### second child has label Edit

1. expect second get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = menubar("menu_child_3", ["File", "Edit", "View"])
val second = bar.child_at(1)
expect second != nil to_equal true
expect second.get_prop("label") to_equal "Edit"
```

</details>

#### third child has label View

1. expect third get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = menubar("menu_child_4", ["File", "Edit", "View"])
val third = bar.child_at(2)
expect third != nil to_equal true
expect third.get_prop("label") to_equal "View"
```

</details>

#### children are text widgets

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = menubar("menu_child_5", ["File", "Edit"])
val first = bar.child_at(0)
expect first.kind to_equal "text"
```

</details>

#### child ids follow naming convention

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = menubar("menu_child_6", ["File", "Edit"])
val first = bar.child_at(0)
expect first.id to_equal "menu_child_6_menu_0"
```

</details>

#### second child id has index 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = menubar("menu_child_7", ["File", "Edit"])
val second = bar.child_at(1)
expect second.id to_equal "menu_child_7_menu_1"
```

</details>

#### empty menubar has zero children

1. expect bar child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = menubar("menu_child_8", [])
expect bar.child_count() to_equal 0
```

</details>

#### single item menubar has one child

1. expect bar child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = menubar("menu_child_9", ["Help"])
expect bar.child_count() to_equal 1
```

</details>

#### single item child has correct label

1. expect first get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = menubar("menu_child_10", ["Help"])
val first = bar.child_at(0)
expect first.get_prop("label") to_equal "Help"
```

</details>

#### children list matches child_count

1. expect kids len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = menubar("menu_child_11", ["A", "B", "C", "D"])
val kids = bar.children()
expect kids.len() to_equal 4
```

</details>

#### child_at out of range returns nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = menubar("menu_child_12", ["File"])
val oob = bar.child_at(5)
expect oob to_be_nil
```

</details>

### MenuBar layout

#### gets fixed height of 1 by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = menubar("menu_layout_1", ["File", "Edit"])
val h = get_fixed_height(bar)
expect h to_equal 1
```

</details>

#### compute_layout assigns correct rect

1. expect rects len


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = menubar("menu_layout_2", ["File"])
val rects = compute_layout(bar, 0, 0, 80, 1)
expect rects.len() to_be_greater_than 0
val first_rect = rects[0]
expect first_rect.id to_equal "menu_layout_2"
expect first_rect.x to_equal 0
expect first_rect.y to_equal 0
expect first_rect.w to_equal 80
expect first_rect.h to_equal 1
```

</details>

#### menubar height consumed in vbox layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = menubar("menu_layout_3", ["File"])
val content = WidgetNode.new("menu_layout_3_content", "panel")
val root = column("menu_layout_3_root", [bar, content])
val rects = compute_layout(root, 0, 0, 80, 24)
# menubar should be at y=0 with h=1
var bar_rect: WidgetRect? = nil
for rect in rects:
    if rect.id == "menu_layout_3":
        bar_rect = rect
expect bar_rect != nil to_equal true
expect bar_rect.h to_equal 1
```

</details>

### MenuBar HTML rendering

#### output contains widget-menubar class

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = menubar("menu_html_1", ["File", "Edit"])
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_contain "widget-menubar"
```

</details>

#### output contains the menubar id

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = menubar("menu_html_2", ["File"])
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_contain "menu_html_2"
```

</details>

#### output contains menu-item span for each item

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = menubar("menu_html_3", ["File", "Edit", "View"])
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_contain "menu-item"
```

</details>

#### output contains label text File

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = menubar("menu_html_4", ["File", "Edit"])
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_contain "File"
```

</details>

#### output contains label text Edit

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = menubar("menu_html_5", ["File", "Edit"])
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_contain "Edit"
```

</details>

#### output is a div element

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = menubar("menu_html_6", ["File"])
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_start_with "<div"
expect html to_end_with "</div>"
```

</details>

#### empty menubar renders with no menu-item spans

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = menubar("menu_html_7", [])
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_contain "widget-menubar"
```

</details>

#### renders span elements for each menu item

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = menubar("menu_html_8", ["Help"])
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_contain "<span class=\"menu-item\">"
expect html to_contain "Help"
expect html to_contain "</span>"
```

</details>

### StatusBar creation

#### creates a statusbar with correct kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = statusbar("status_create_1", "MODE: Normal", "My App")
expect bar.kind to_equal "statusbar"
```

</details>

#### creates a statusbar with correct id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = statusbar("status_create_2", "left text", "right text")
expect bar.id to_equal "status_create_2"
```

</details>

#### defaults visible to true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = statusbar("status_create_3", "left", "right")
expect bar.visible to_equal true
```

</details>

#### defaults focused to false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = statusbar("status_create_4", "left", "right")
expect bar.focused to_equal false
```

</details>

### StatusBar properties

#### left prop returns left text

1. expect bar get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = statusbar("status_prop_1", "MODE: Normal", "My App")
expect bar.get_prop("left") to_equal "MODE: Normal"
```

</details>

#### right prop returns right text

1. expect bar get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = statusbar("status_prop_2", "MODE: Normal", "My App")
expect bar.get_prop("right") to_equal "My App"
```

</details>

#### empty left is preserved

1. expect bar get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = statusbar("status_prop_3", "", "right side")
expect bar.get_prop("left") to_equal ""
```

</details>

#### empty right is preserved

1. expect bar get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = statusbar("status_prop_4", "left side", "")
expect bar.get_prop("right") to_equal ""
```

</details>

#### both empty strings are valid

1. expect bar get prop
2. expect bar get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = statusbar("status_prop_5", "", "")
expect bar.get_prop("left") to_equal ""
expect bar.get_prop("right") to_equal ""
```

</details>

#### has_prop returns true for left

1. expect bar has prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = statusbar("status_prop_6", "L", "R")
expect bar.has_prop("left") to_equal true
```

</details>

#### has_prop returns true for right

1. expect bar has prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = statusbar("status_prop_7", "L", "R")
expect bar.has_prop("right") to_equal true
```

</details>

#### has_prop returns false for unknown key

1. expect bar has prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = statusbar("status_prop_8", "L", "R")
expect bar.has_prop("center") to_equal false
```

</details>

#### statusbar has no children

1. expect bar child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = statusbar("status_prop_9", "left", "right")
expect bar.child_count() to_equal 0
```

</details>

### StatusBar layout

#### gets fixed height of 1 by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = statusbar("status_layout_1", "left", "right")
val h = get_fixed_height(bar)
expect h to_equal 1
```

</details>

#### compute_layout assigns correct rect

1. expect rects len


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = statusbar("status_layout_2", "left", "right")
val rects = compute_layout(bar, 0, 23, 80, 1)
expect rects.len() to_be_greater_than 0
val first_rect = rects[0]
expect first_rect.id to_equal "status_layout_2"
expect first_rect.x to_equal 0
expect first_rect.y to_equal 23
expect first_rect.w to_equal 80
expect first_rect.h to_equal 1
```

</details>

#### statusbar height consumed in vbox layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = WidgetNode.new("status_layout_3_content", "panel")
val bar = statusbar("status_layout_3", "left", "right")
val root = column("status_layout_3_root", [content, bar])
val rects = compute_layout(root, 0, 0, 80, 24)
var bar_rect: WidgetRect? = nil
for rect in rects:
    if rect.id == "status_layout_3":
        bar_rect = rect
expect bar_rect != nil to_equal true
expect bar_rect.h to_equal 1
```

</details>

### StatusBar HTML rendering

#### output contains widget-statusbar class

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = statusbar("status_html_1", "Left", "Right")
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_contain "widget-statusbar"
```

</details>

#### output contains the statusbar id

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = statusbar("status_html_2", "Left", "Right")
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_contain "status_html_2"
```

</details>

#### output contains status-left span

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = statusbar("status_html_3", "Left Text", "Right Text")
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_contain "status-left"
```

</details>

#### output contains status-right span

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = statusbar("status_html_4", "Left Text", "Right Text")
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_contain "status-right"
```

</details>

#### output contains left text content

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = statusbar("status_html_5", "MODE: Normal", "My App")
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_contain "MODE: Normal"
```

</details>

#### output contains right text content

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = statusbar("status_html_6", "MODE: Normal", "My App")
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_contain "My App"
```

</details>

#### output is a div element

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = statusbar("status_html_7", "left", "right")
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_start_with "<div"
expect html to_end_with "</div>"
```

</details>

#### renders both span elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = statusbar("status_html_8", "L", "R")
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_contain "<span class=\"status-left\">"
expect html to_contain "<span class=\"status-right\">"
```

</details>

### StatusBar template expansion

#### expands app.mode to NORMAL in left text

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ph_mode = "{" + "app.mode" + "}"
val bar = statusbar("status_tpl_1", ph_mode, "Title")
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_contain "NORMAL"
```

</details>

#### expands app.title to tree title in right text

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ph_title = "{" + "app.title" + "}"
val bar = statusbar("status_tpl_2", "Mode", ph_title)
val root = bar
val tree = build_tree_with_title(root, "My Editor", "dark")
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_contain "My Editor"
```

</details>

#### expands both placeholders simultaneously

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ph_mode = "{" + "app.mode" + "}"
val ph_title = "{" + "app.title" + "}"
val bar = statusbar("status_tpl_3", ph_mode, ph_title)
val tree = build_tree_with_title(bar, "Test App", "dark")
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_contain "NORMAL"
expect html to_contain "Test App"
```

</details>

#### leaves plain text unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = statusbar("status_tpl_4", "static left", "static right")
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_contain "static left"
expect html to_contain "static right"
```

</details>

#### expand_template returns NORMAL for app.mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ph_mode = "{" + "app.mode" + "}"
val bar = statusbar("status_tpl_5", "x", "y")
val tree = build_tree(bar)
val state = init_state(tree)
val result = expand_template(ph_mode, state)
expect result to_equal "NORMAL"
```

</details>

#### expand_template returns tree title for app.title

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ph_title = "{" + "app.title" + "}"
val bar = statusbar("status_tpl_6", "x", "y")
val tree = build_tree_with_title(bar, "Code Editor", "dark")
val state = init_state(tree)
val result = expand_template(ph_title, state)
expect result to_equal "Code Editor"
```

</details>

#### expand_template returns empty string for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = statusbar("status_tpl_7", "x", "y")
val tree = build_tree(bar)
val state = init_state(tree)
val result = expand_template("", state)
expect result to_equal ""
```

</details>

#### expand_template preserves text without placeholders

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = statusbar("status_tpl_8", "x", "y")
val tree = build_tree(bar)
val state = init_state(tree)
val result = expand_template("hello world", state)
expect result to_equal "hello world"
```

</details>

#### renders expanded mode in status-left span

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ph_mode = "{" + "app.mode" + "}"
val bar = statusbar("status_tpl_9", ph_mode, "right")
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_contain "<span class=\"status-left\">NORMAL</span>"
```

</details>

#### renders expanded title in status-right span

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ph_title = "{" + "app.title" + "}"
val bar = statusbar("status_tpl_10", "left", ph_title)
val tree = build_tree_with_title(bar, "My Title", "dark")
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_contain "<span class=\"status-right\">My Title</span>"
```

</details>

### MenuBar and StatusBar combined

#### both widgets coexist in a column layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val menu = menubar("combined_menu_1", ["File", "Edit"])
val content = WidgetNode.new("combined_content_1", "panel")
val status = statusbar("combined_status_1", "NORMAL", "App")
val root = column("combined_root_1", [menu, content, status])
val rects = compute_layout(root, 0, 0, 80, 24)
var menu_rect: WidgetRect? = nil
var status_rect: WidgetRect? = nil
for rect in rects:
    if rect.id == "combined_menu_1":
        menu_rect = rect
    if rect.id == "combined_status_1":
        status_rect = rect
expect menu_rect != nil to_equal true
expect status_rect != nil to_equal true
expect menu_rect.h to_equal 1
expect status_rect.h to_equal 1
```

</details>

#### menubar is above statusbar in vbox order

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val menu = menubar("combined_menu_2", ["File"])
val content = WidgetNode.new("combined_content_2", "panel")
val status = statusbar("combined_status_2", "L", "R")
val root = column("combined_root_2", [menu, content, status])
val rects = compute_layout(root, 0, 0, 80, 24)
var menu_y = -1
var status_y = -1
for rect in rects:
    if rect.id == "combined_menu_2":
        menu_y = rect.y
    if rect.id == "combined_status_2":
        status_y = rect.y
expect menu_y to_be_less_than status_y
```

</details>

#### tree finds both widgets by id

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val menu = menubar("combined_menu_3", ["File"])
val status = statusbar("combined_status_3", "L", "R")
val root = column("combined_root_3", [menu, status])
val tree = build_tree(root)
val found_menu = tree.find_widget("combined_menu_3")
val found_status = tree.find_widget("combined_status_3")
expect found_menu != nil to_equal true
expect found_status != nil to_equal true
expect found_menu.kind to_equal "menubar"
expect found_status.kind to_equal "statusbar"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/widget_menubar_statusbar_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MenuBar creation
- MenuBar children
- MenuBar layout
- MenuBar HTML rendering
- StatusBar creation
- StatusBar properties
- StatusBar layout
- StatusBar HTML rendering
- StatusBar template expansion
- MenuBar and StatusBar combined

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 64 |
| Active scenarios | 64 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
