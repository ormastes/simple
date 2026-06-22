# Widget Tabs List Dialog Specification

> <details>

<!-- sdn-diagram:id=widget_tabs_list_dialog_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=widget_tabs_list_dialog_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

widget_tabs_list_dialog_spec -> common
widget_tabs_list_dialog_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=widget_tabs_list_dialog_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 71 | 71 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Widget Tabs List Dialog Specification

## Scenarios

### Tabs widget creation

#### creates a widget with kind tabs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = tabs("tabs_create_1", ["Tab1", "Tab2", "Tab3"])
expect t.kind to_equal "tabs"
```

</details>

#### assigns the correct id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = tabs("tabs_id_1", ["A", "B"])
expect t.id to_equal "tabs_id_1"
```

</details>

#### has correct child count for three tabs

1. expect t child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = tabs("tabs_count_1", ["Tab1", "Tab2", "Tab3"])
expect t.child_count() to_equal 3
```

</details>

#### first child has correct label prop

1. expect first get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = tabs("tabs_label_1", ["Tab1", "Tab2", "Tab3"])
val first = t.child_at(0)
expect first != nil to_equal true
expect first.get_prop("label") to_equal "Tab1"
```

</details>

#### second child has correct label prop

1. expect second get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = tabs("tabs_label_2", ["Alpha", "Beta", "Gamma"])
val second = t.child_at(1)
expect second != nil to_equal true
expect second.get_prop("label") to_equal "Beta"
```

</details>

#### third child has correct label prop

1. expect third get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = tabs("tabs_label_3", ["X", "Y", "Z"])
val third = t.child_at(2)
expect third != nil to_equal true
expect third.get_prop("label") to_equal "Z"
```

</details>

#### children are text kind widgets

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = tabs("tabs_childkind_1", ["Home", "Settings"])
val child = t.child_at(0)
expect child != nil to_equal true
expect child.kind to_equal "text"
```

</details>

#### child ids follow naming convention

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = tabs("tabs_childid_1", ["One", "Two"])
val first = t.child_at(0)
expect first != nil to_equal true
expect first.id to_equal "tabs_childid_1_tab_0"
```

</details>

### Tabs widget edge cases

#### empty tabs has zero children

1. expect t child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = tabs("tabs_empty_1", [])
expect t.child_count() to_equal 0
```

</details>

#### empty tabs still has kind tabs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = tabs("tabs_empty_2", [])
expect t.kind to_equal "tabs"
```

</details>

#### single tab has one child

1. expect t child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = tabs("tabs_single_1", ["Only"])
expect t.child_count() to_equal 1
```

</details>

#### single tab child has correct label

1. expect child get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = tabs("tabs_single_2", ["Alone"])
val child = t.child_at(0)
expect child != nil to_equal true
expect child.get_prop("label") to_equal "Alone"
```

</details>

#### many tabs have correct count

1. expect t child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = tabs("tabs_many_1", ["A", "B", "C", "D", "E"])
expect t.child_count() to_equal 5
```

</details>

### Tabs HTML rendering

#### output contains widget-tabs class

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = tabs("tabs_html_1", ["Tab1", "Tab2"])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "widget-tabs"
```

</details>

#### output starts with div tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = tabs("tabs_html_2", ["Tab1"])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_start_with "<div"
```

</details>

#### output contains tab-item spans

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = tabs("tabs_html_3", ["Home", "About"])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "tab-item"
```

</details>

#### output contains tab label text

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = tabs("tabs_html_4", ["Dashboard", "Reports"])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "Dashboard"
expect html to_contain "Reports"
```

</details>

#### first tab has active class

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = tabs("tabs_html_5", ["First", "Second", "Third"])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "tab-item active"
```

</details>

#### output contains all tab labels

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = tabs("tabs_html_6", ["A", "B", "C"])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain ">A</span>"
expect html to_contain ">B</span>"
expect html to_contain ">C</span>"
```

</details>

#### empty tabs renders widget-tabs class with no tab-items

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = tabs("tabs_html_7", [])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "widget-tabs"
```

</details>

#### focused tabs widget has focused class

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = tabs("tabs_html_8", ["Tab1"])
val tree = UITree.new(node)
val state = init_state(tree)
# init_state sets focused_id to first widget (the root = tabs node)
expect state.focused_id to_equal "tabs_html_8"
val html = render_html_widget(node, state)
expect html to_contain "focused"
```

</details>

#### output includes widget id attribute

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = tabs("tabs_html_9", ["One"])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "id=\"tabs_html_9\""
```

</details>

### List widget creation

#### creates a widget with kind list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lw = list_widget("list_create_1", ["Apple", "Banana", "Cherry"])
expect lw.kind to_equal "list"
```

</details>

#### assigns the correct id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lw = list_widget("list_id_1", ["X"])
expect lw.id to_equal "list_id_1"
```

</details>

#### has correct child count for three items

1. expect lw child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lw = list_widget("list_count_1", ["Apple", "Banana", "Cherry"])
expect lw.child_count() to_equal 3
```

</details>

#### first child has correct label prop

1. expect first get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lw = list_widget("list_label_1", ["Apple", "Banana", "Cherry"])
val first = lw.child_at(0)
expect first != nil to_equal true
expect first.get_prop("label") to_equal "Apple"
```

</details>

#### second child has correct label prop

1. expect second get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lw = list_widget("list_label_2", ["Red", "Green", "Blue"])
val second = lw.child_at(1)
expect second != nil to_equal true
expect second.get_prop("label") to_equal "Green"
```

</details>

#### third child has correct label prop

1. expect third get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lw = list_widget("list_label_3", ["One", "Two", "Three"])
val third = lw.child_at(2)
expect third != nil to_equal true
expect third.get_prop("label") to_equal "Three"
```

</details>

#### children are text kind widgets

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lw = list_widget("list_childkind_1", ["Item"])
val child = lw.child_at(0)
expect child != nil to_equal true
expect child.kind to_equal "text"
```

</details>

#### child ids follow naming convention

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lw = list_widget("list_childid_1", ["First", "Second"])
val first = lw.child_at(0)
expect first != nil to_equal true
expect first.id to_equal "list_childid_1_item_0"
```

</details>

### List widget edge cases

#### empty list has zero children

1. expect lw child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lw = list_widget("list_empty_1", [])
expect lw.child_count() to_equal 0
```

</details>

#### empty list still has kind list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lw = list_widget("list_empty_2", [])
expect lw.kind to_equal "list"
```

</details>

#### single item list has one child

1. expect lw child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lw = list_widget("list_single_1", ["Only"])
expect lw.child_count() to_equal 1
```

</details>

#### single item child has correct label

1. expect child get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lw = list_widget("list_single_2", ["Sole"])
val child = lw.child_at(0)
expect child != nil to_equal true
expect child.get_prop("label") to_equal "Sole"
```

</details>

#### many items have correct count

1. expect lw child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lw = list_widget("list_many_1", ["A", "B", "C", "D", "E", "F"])
expect lw.child_count() to_equal 6
```

</details>

### List HTML rendering

#### output contains widget-list class

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = list_widget("list_html_1", ["Apple", "Banana"])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "widget-list"
```

</details>

#### output starts with ul tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = list_widget("list_html_2", ["Item1"])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_start_with "<ul"
```

</details>

#### output contains li tags

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = list_widget("list_html_3", ["Alpha", "Beta"])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "<li>"
```

</details>

#### output contains item label text

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = list_widget("list_html_4", ["Apple", "Banana", "Cherry"])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "Apple"
expect html to_contain "Banana"
expect html to_contain "Cherry"
```

</details>

#### each item is wrapped in li tags

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = list_widget("list_html_5", ["Dog", "Cat"])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "<li>Dog</li>"
expect html to_contain "<li>Cat</li>"
```

</details>

#### empty list renders ul with widget-list class

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = list_widget("list_html_6", [])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "widget-list"
expect html to_start_with "<ul"
```

</details>

#### focused list widget has focused class

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = list_widget("list_html_7", ["Item"])
val tree = UITree.new(node)
val state = init_state(tree)
expect state.focused_id to_equal "list_html_7"
val html = render_html_widget(node, state)
expect html to_contain "focused"
```

</details>

#### output includes widget id attribute

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = list_widget("list_html_8", ["X"])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "id=\"list_html_8\""
```

</details>

#### output ends with closing ul tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = list_widget("list_html_9", ["A"])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_end_with "</ul>"
```

</details>

### Dialog widget creation

#### creates a widget with kind dialog

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = dialog("dlg_create_1", "Confirm?", [])
expect d.kind to_equal "dialog"
```

</details>

#### assigns the correct id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = dialog("dlg_id_1", "Alert", [])
expect d.id to_equal "dlg_id_1"
```

</details>

#### title prop returns the dialog title

1. expect d get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = dialog("dlg_title_1", "Confirm?", [])
expect d.get_prop("title") to_equal "Confirm?"
```

</details>

#### has vbox layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = dialog("dlg_layout_1", "Layout Test", [])
expect d.layout to_equal "vbox"
```

</details>

#### is visible by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = dialog("dlg_visible_1", "Visible", [])
expect d.visible to_equal true
```

</details>

#### is not focused by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = dialog("dlg_focus_1", "Focus", [])
expect d.focused to_equal false
```

</details>

### Dialog widget with children

#### dialog with one text child has child_count 1

1. expect d child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val child = text_widget("dlg_child_txt_1", "Hello")
val d = dialog("dlg_children_1", "Info", [child])
expect d.child_count() to_equal 1
```

</details>

#### dialog with button child has child_count 1

1. expect d child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val btn = button("dlg_child_btn_1", "OK", "confirm")
val d = dialog("dlg_children_2", "Confirm", [btn])
expect d.child_count() to_equal 1
```

</details>

#### dialog with multiple children has correct count

1. expect d child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = text_widget("dlg_mc_txt_1", "Are you sure?")
val b = button("dlg_mc_btn_1", "Yes", "yes_action")
val d = dialog("dlg_children_3", "Question", [t, b])
expect d.child_count() to_equal 2
```

</details>

#### child widget is accessible via child_at

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val child = text_widget("dlg_at_txt_1", "Content")
val d = dialog("dlg_children_4", "Access", [child])
val retrieved = d.child_at(0)
expect retrieved != nil to_equal true
expect retrieved.id to_equal "dlg_at_txt_1"
```

</details>

#### empty dialog has zero children

1. expect d child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = dialog("dlg_empty_1", "Empty", [])
expect d.child_count() to_equal 0
```

</details>

### Dialog widget edge cases

#### empty title results in empty title prop

1. expect d get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = dialog("dlg_emptytitle_1", "", [])
expect d.get_prop("title") to_equal ""
```

</details>

#### title with special characters is preserved

1. expect d get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = dialog("dlg_special_1", "Save changes?", [])
expect d.get_prop("title") to_equal "Save changes?"
```

</details>

#### title with spaces is preserved

1. expect d get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = dialog("dlg_spaces_1", "Are you sure you want to quit", [])
expect d.get_prop("title") to_equal "Are you sure you want to quit"
```

</details>

### Dialog HTML rendering

#### output contains widget-dialog class

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = dialog("dlg_html_1", "Confirm", [])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "widget-dialog"
```

</details>

#### output starts with div tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = dialog("dlg_html_2", "Alert", [])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_start_with "<div"
```

</details>

#### output contains dialog-title div

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = dialog("dlg_html_3", "My Title", [])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "dialog-title"
```

</details>

#### output contains title text inside dialog-title

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = dialog("dlg_html_4", "Delete file?", [])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "Delete file?"
```

</details>

#### output contains dialog-content div

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = dialog("dlg_html_5", "Content Area", [])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "dialog-content"
```

</details>

#### focused dialog has focused class

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = dialog("dlg_html_6", "Focused Dialog", [])
val tree = UITree.new(node)
val state = init_state(tree)
expect state.focused_id to_equal "dlg_html_6"
val html = render_html_widget(node, state)
expect html to_contain "focused"
```

</details>

#### output includes widget id attribute

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = dialog("dlg_html_7", "ID Test", [])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "id=\"dlg_html_7\""
```

</details>

#### dialog with button child renders nested button in content

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val btn = button("dlg_html_btn_1", "OK", "ok_action")
val node = dialog("dlg_html_8", "Confirm Action", [btn])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "widget-dialog"
expect html to_contain "dialog-content"
expect html to_contain "widget-button"
expect html to_contain "OK"
```

</details>

#### dialog with text child renders text in content

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val txt = text_widget("dlg_html_txt_1", "Important message")
val node = dialog("dlg_html_9", "Notice", [txt])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "dialog-content"
expect html to_contain "Important message"
expect html to_contain "widget-text"
```

</details>

#### empty title dialog renders empty dialog-title

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = dialog("dlg_html_10", "", [])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "dialog-title"
expect html to_contain "dialog-content"
```

</details>

### Dialog with nested widgets

#### dialog containing tabs renders both widget types

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tab_bar = tabs("dlg_nested_tabs_1", ["General", "Advanced"])
val node = dialog("dlg_nested_1", "Settings", [tab_bar])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "widget-dialog"
expect html to_contain "widget-tabs"
expect html to_contain "General"
expect html to_contain "Advanced"
```

</details>

#### dialog containing list renders both widget types

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = list_widget("dlg_nested_list_1", ["Option A", "Option B"])
val node = dialog("dlg_nested_2", "Select Item", [items])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "widget-dialog"
expect html to_contain "widget-list"
expect html to_contain "Option A"
expect html to_contain "Option B"
```

</details>

#### dialog with tabs and list renders all nested widgets

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tab_bar = tabs("dlg_nested_tabs_2", ["Tab1", "Tab2"])
val items = list_widget("dlg_nested_list_2", ["Item1", "Item2"])
val node = dialog("dlg_nested_3", "Complex Dialog", [tab_bar, items])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "widget-dialog"
expect html to_contain "widget-tabs"
expect html to_contain "widget-list"
expect html to_contain "Tab1"
expect html to_contain "Item1"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/widget_tabs_list_dialog_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Tabs widget creation
- Tabs widget edge cases
- Tabs HTML rendering
- List widget creation
- List widget edge cases
- List HTML rendering
- Dialog widget creation
- Dialog widget with children
- Dialog widget edge cases
- Dialog HTML rendering
- Dialog with nested widgets

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 71 |
| Active scenarios | 71 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
