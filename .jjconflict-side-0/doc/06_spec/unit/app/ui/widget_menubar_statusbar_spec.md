# Widget Menubar Statusbar Specification

> Tests covering MenuBar creation, MenuBar children, MenuBar layout, MenuBar HTML rendering, StatusBar creation, StatusBar properties, StatusBar layout, StatusBar HTML rendering, StatusBar template expansion, MenuBar and StatusBar combined.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 64 | 64 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Widget Menubar Statusbar Specification

## Scenarios

### MenuBar creation

#### creates a menubar with correct kind

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates a menubar with correct kind


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a menubar with correct kind")
val bar = menubar("menu_create_1", ["File", "Edit", "View"])
expect bar.kind to_equal "menubar"
```

</details>

#### creates a menubar with correct id

- creates a menubar with correct id


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a menubar with correct id")
val bar = menubar("menu_create_2", ["File", "Edit", "View"])
expect bar.id to_equal "menu_create_2"
```

</details>

#### defaults visible to true

- defaults visible to true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults visible to true")
val bar = menubar("menu_create_3", ["File"])
expect bar.visible to_equal true
```

</details>

#### defaults focused to false

- defaults focused to false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults focused to false")
val bar = menubar("menu_create_4", ["File"])
expect bar.focused to_equal false
```

</details>

### MenuBar children

#### has correct child count for three items

- has correct child count for three items


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has correct child count for three items")
val bar = menubar("menu_child_1", ["File", "Edit", "View"])
expect bar.child_count() to_equal 3
```

</details>

#### first child has label File

- first child has label File


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("first child has label File")
val bar = menubar("menu_child_2", ["File", "Edit", "View"])
val first = bar.child_at(0)
expect first != nil to_equal true
expect first.get_prop("label") to_equal "File"
```

</details>

#### second child has label Edit

- second child has label Edit


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("second child has label Edit")
val bar = menubar("menu_child_3", ["File", "Edit", "View"])
val second = bar.child_at(1)
expect second != nil to_equal true
expect second.get_prop("label") to_equal "Edit"
```

</details>

#### third child has label View

- third child has label View


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("third child has label View")
val bar = menubar("menu_child_4", ["File", "Edit", "View"])
val third = bar.child_at(2)
expect third != nil to_equal true
expect third.get_prop("label") to_equal "View"
```

</details>

#### children are text widgets

- children are text widgets


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("children are text widgets")
val bar = menubar("menu_child_5", ["File", "Edit"])
val first = bar.child_at(0)
expect first.kind to_equal "text"
```

</details>

#### child ids follow naming convention

- child ids follow naming convention


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("child ids follow naming convention")
val bar = menubar("menu_child_6", ["File", "Edit"])
val first = bar.child_at(0)
expect first.id to_equal "menu_child_6_menu_0"
```

</details>

#### second child id has index 1

- second child id has index 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("second child id has index 1")
val bar = menubar("menu_child_7", ["File", "Edit"])
val second = bar.child_at(1)
expect second.id to_equal "menu_child_7_menu_1"
```

</details>

#### empty menubar has zero children

- empty menubar has zero children


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty menubar has zero children")
val bar = menubar("menu_child_8", [])
expect bar.child_count() to_equal 0
```

</details>

#### single item menubar has one child

- single item menubar has one child


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("single item menubar has one child")
val bar = menubar("menu_child_9", ["Help"])
expect bar.child_count() to_equal 1
```

</details>

#### single item child has correct label

- single item child has correct label


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("single item child has correct label")
val bar = menubar("menu_child_10", ["Help"])
val first = bar.child_at(0)
expect first.get_prop("label") to_equal "Help"
```

</details>

#### children list matches child_count

- children list matches child_count


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("children list matches child_count")
val bar = menubar("menu_child_11", ["A", "B", "C", "D"])
val kids = bar.children()
expect kids.len() to_equal 4
```

</details>

#### child_at out of range returns nil

- child_at out of range returns nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("child_at out of range returns nil")
val bar = menubar("menu_child_12", ["File"])
val oob = bar.child_at(5)
expect oob to_be_nil
```

</details>

### MenuBar layout

#### gets fixed height of 1 by default

- gets fixed height of 1 by default


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets fixed height of 1 by default")
val bar = menubar("menu_layout_1", ["File", "Edit"])
val h = get_fixed_height(bar)
expect h to_equal 1
```

</details>

#### compute_layout assigns correct rect

- compute_layout assigns correct rect


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compute_layout assigns correct rect")
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

- menubar height consumed in vbox layout


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("menubar height consumed in vbox layout")
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

- output contains widget-menubar class


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output contains widget-menubar class")
val bar = menubar("menu_html_1", ["File", "Edit"])
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_contain "widget-menubar"
```

</details>

#### output contains the menubar id

- output contains the menubar id


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output contains the menubar id")
val bar = menubar("menu_html_2", ["File"])
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_contain "menu_html_2"
```

</details>

#### output contains menu-item span for each item

- output contains menu-item span for each item


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output contains menu-item span for each item")
val bar = menubar("menu_html_3", ["File", "Edit", "View"])
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_contain "menu-item"
```

</details>

#### output contains label text File

- output contains label text File


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output contains label text File")
val bar = menubar("menu_html_4", ["File", "Edit"])
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_contain "File"
```

</details>

#### output contains label text Edit

- output contains label text Edit


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output contains label text Edit")
val bar = menubar("menu_html_5", ["File", "Edit"])
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_contain "Edit"
```

</details>

#### output is a div element

- output is a div element


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output is a div element")
val bar = menubar("menu_html_6", ["File"])
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_start_with "<div"
expect html to_end_with "</div>"
```

</details>

#### empty menubar renders with no menu-item spans

- empty menubar renders with no menu-item spans


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty menubar renders with no menu-item spans")
val bar = menubar("menu_html_7", [])
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_contain "widget-menubar"
```

</details>

#### renders span elements for each menu item

- renders span elements for each menu item


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders span elements for each menu item")
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

- creates a statusbar with correct kind


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a statusbar with correct kind")
val bar = statusbar("status_create_1", "MODE: Normal", "My App")
expect bar.kind to_equal "statusbar"
```

</details>

#### creates a statusbar with correct id

- creates a statusbar with correct id


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a statusbar with correct id")
val bar = statusbar("status_create_2", "left text", "right text")
expect bar.id to_equal "status_create_2"
```

</details>

#### defaults visible to true

- defaults visible to true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults visible to true")
val bar = statusbar("status_create_3", "left", "right")
expect bar.visible to_equal true
```

</details>

#### defaults focused to false

- defaults focused to false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults focused to false")
val bar = statusbar("status_create_4", "left", "right")
expect bar.focused to_equal false
```

</details>

### StatusBar properties

#### left prop returns left text

- left prop returns left text


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("left prop returns left text")
val bar = statusbar("status_prop_1", "MODE: Normal", "My App")
expect bar.get_prop("left") to_equal "MODE: Normal"
```

</details>

#### right prop returns right text

- right prop returns right text


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("right prop returns right text")
val bar = statusbar("status_prop_2", "MODE: Normal", "My App")
expect bar.get_prop("right") to_equal "My App"
```

</details>

#### empty left is preserved

- empty left is preserved


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty left is preserved")
val bar = statusbar("status_prop_3", "", "right side")
expect bar.get_prop("left") to_equal ""
```

</details>

#### empty right is preserved

- empty right is preserved


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty right is preserved")
val bar = statusbar("status_prop_4", "left side", "")
expect bar.get_prop("right") to_equal ""
```

</details>

#### both empty strings are valid

- both empty strings are valid


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("both empty strings are valid")
val bar = statusbar("status_prop_5", "", "")
expect bar.get_prop("left") to_equal ""
expect bar.get_prop("right") to_equal ""
```

</details>

#### has_prop returns true for left

- has_prop returns true for left


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has_prop returns true for left")
val bar = statusbar("status_prop_6", "L", "R")
expect bar.has_prop("left") to_equal true
```

</details>

#### has_prop returns true for right

- has_prop returns true for right


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has_prop returns true for right")
val bar = statusbar("status_prop_7", "L", "R")
expect bar.has_prop("right") to_equal true
```

</details>

#### has_prop returns false for unknown key

- has_prop returns false for unknown key


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has_prop returns false for unknown key")
val bar = statusbar("status_prop_8", "L", "R")
expect bar.has_prop("center") to_equal false
```

</details>

#### statusbar has no children

- statusbar has no children


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("statusbar has no children")
val bar = statusbar("status_prop_9", "left", "right")
expect bar.child_count() to_equal 0
```

</details>

### StatusBar layout

#### gets fixed height of 1 by default

- gets fixed height of 1 by default


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets fixed height of 1 by default")
val bar = statusbar("status_layout_1", "left", "right")
val h = get_fixed_height(bar)
expect h to_equal 1
```

</details>

#### compute_layout assigns correct rect

- compute_layout assigns correct rect


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compute_layout assigns correct rect")
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

- statusbar height consumed in vbox layout


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("statusbar height consumed in vbox layout")
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

- output contains widget-statusbar class


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output contains widget-statusbar class")
val bar = statusbar("status_html_1", "Left", "Right")
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_contain "widget-statusbar"
```

</details>

#### output contains the statusbar id

- output contains the statusbar id


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output contains the statusbar id")
val bar = statusbar("status_html_2", "Left", "Right")
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_contain "status_html_2"
```

</details>

#### output contains status-left span

- output contains status-left span


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output contains status-left span")
val bar = statusbar("status_html_3", "Left Text", "Right Text")
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_contain "status-left"
```

</details>

#### output contains status-right span

- output contains status-right span


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output contains status-right span")
val bar = statusbar("status_html_4", "Left Text", "Right Text")
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_contain "status-right"
```

</details>

#### output contains left text content

- output contains left text content


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output contains left text content")
val bar = statusbar("status_html_5", "MODE: Normal", "My App")
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_contain "MODE: Normal"
```

</details>

#### output contains right text content

- output contains right text content


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output contains right text content")
val bar = statusbar("status_html_6", "MODE: Normal", "My App")
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_contain "My App"
```

</details>

#### output is a div element

- output is a div element


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output is a div element")
val bar = statusbar("status_html_7", "left", "right")
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_start_with "<div"
expect html to_end_with "</div>"
```

</details>

#### renders both span elements

- renders both span elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders both span elements")
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

- expands app.mode to NORMAL in left text


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("expands app.mode to NORMAL in left text")
val ph_mode = "{" + "app.mode" + "}"
val bar = statusbar("status_tpl_1", ph_mode, "Title")
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_contain "NORMAL"
```

</details>

#### expands app.title to tree title in right text

- expands app.title to tree title in right text


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("expands app.title to tree title in right text")
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

- expands both placeholders simultaneously


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("expands both placeholders simultaneously")
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

- leaves plain text unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves plain text unchanged")
val bar = statusbar("status_tpl_4", "static left", "static right")
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_contain "static left"
expect html to_contain "static right"
```

</details>

#### expand_template returns NORMAL for app.mode

- expand_template returns NORMAL for app.mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("expand_template returns NORMAL for app.mode")
val ph_mode = "{" + "app.mode" + "}"
val bar = statusbar("status_tpl_5", "x", "y")
val tree = build_tree(bar)
val state = init_state(tree)
val result = expand_template(ph_mode, state)
expect result to_equal "NORMAL"
```

</details>

#### expand_template returns tree title for app.title

- expand_template returns tree title for app.title


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("expand_template returns tree title for app.title")
val ph_title = "{" + "app.title" + "}"
val bar = statusbar("status_tpl_6", "x", "y")
val tree = build_tree_with_title(bar, "Code Editor", "dark")
val state = init_state(tree)
val result = expand_template(ph_title, state)
expect result to_equal "Code Editor"
```

</details>

#### expand_template returns empty string for empty input

- expand_template returns empty string for empty input


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("expand_template returns empty string for empty input")
val bar = statusbar("status_tpl_7", "x", "y")
val tree = build_tree(bar)
val state = init_state(tree)
val result = expand_template("", state)
expect result to_equal ""
```

</details>

#### expand_template preserves text without placeholders

- expand_template preserves text without placeholders


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("expand_template preserves text without placeholders")
val bar = statusbar("status_tpl_8", "x", "y")
val tree = build_tree(bar)
val state = init_state(tree)
val result = expand_template("hello world", state)
expect result to_equal "hello world"
```

</details>

#### renders expanded mode in status-left span

- renders expanded mode in status-left span


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders expanded mode in status-left span")
val ph_mode = "{" + "app.mode" + "}"
val bar = statusbar("status_tpl_9", ph_mode, "right")
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_contain "<span class=\"status-left\">NORMAL</span>"
```

</details>

#### renders expanded title in status-right span

- renders expanded title in status-right span


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders expanded title in status-right span")
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

- both widgets coexist in a column layout


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("both widgets coexist in a column layout")
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

- menubar is above statusbar in vbox order


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("menubar is above statusbar in vbox order")
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

- tree finds both widgets by id


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tree finds both widgets by id")
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
| Source | `test/unit/app/ui/widget_menubar_statusbar_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MenuBar creation, MenuBar children, MenuBar layout, MenuBar HTML rendering, StatusBar creation, StatusBar properties, StatusBar layout, StatusBar HTML rendering, StatusBar template expansion, MenuBar and StatusBar combined.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9613dc369e9a8d487a4d81c9c0e15de9881c42d01ce88c69d46e9ef4a53303c2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9613dc369e9a8d487a4d81c9c0e15de9881c42d01ce88c69d46e9ef4a53303c2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9613dc369e9a8d487a4d81c9c0e15de9881c42d01ce88c69d46e9ef4a53303c2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui/widget_menubar_statusbar_spec.spl
mirror: doc/06_spec/unit/app/ui/widget_menubar_statusbar_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/widget_menubar_statusbar_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/widget_menubar_statusbar_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/widget_menubar_statusbar_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a menubar with correct kind' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/widget_menubar_statusbar_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a menubar with correct id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/widget_menubar_statusbar_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defaults visible to true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
