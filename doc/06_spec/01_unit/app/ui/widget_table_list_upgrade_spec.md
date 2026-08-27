# Widget Table List Upgrade Specification

> 1. expect t kind name

<!-- sdn-diagram:id=widget_table_list_upgrade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=widget_table_list_upgrade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

widget_table_list_upgrade_spec -> common
widget_table_list_upgrade_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=widget_table_list_upgrade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Widget Table List Upgrade Specification

## Scenarios

### table_widget creation

#### creates a widget with kind table

1. expect t kind name


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = table_widget("tbl_kind_1", ["A", "B"], [["1", "2"]])
expect t.kind_name() to_equal "table"
```

</details>

#### assigns the correct id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = table_widget("tbl_id_1", ["X"], [["Y"]])
expect t.id to_equal "tbl_id_1"
```

</details>

#### headers prop is joined by pipe

1. expect t get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = table_widget("tbl_hdr_1", ["Name", "Age", "City"], [])
expect t.get_prop("headers") to_equal "Name|Age|City"
```

</details>

#### single header has no pipe

1. expect t get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = table_widget("tbl_hdr_2", ["Only"], [])
expect t.get_prop("headers") to_equal "Only"
```

</details>

#### sort_column defaults to empty

1. expect t get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = table_widget("tbl_sort_1", ["A"], [])
expect t.get_prop("sort_column") to_equal ""
```

</details>

#### sort_dir defaults to asc

1. expect t get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = table_widget("tbl_sort_2", ["A"], [])
expect t.get_prop("sort_dir") to_equal "asc"
```

</details>

#### filter_text defaults to empty

1. expect t get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = table_widget("tbl_filter_1", ["A"], [])
expect t.get_prop("filter_text") to_equal ""
```

</details>

#### row children have label with cells joined by pipe

1. expect first get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = table_widget("tbl_row_1", ["H1", "H2"], [["a", "b"], ["c", "d"]])
val first = t.child_at(0)
expect first != nil to_equal true
expect first.get_prop("label") to_equal "a|b"
```

</details>

#### second row child has correct label

1. expect second get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = table_widget("tbl_row_2", ["H1", "H2"], [["x", "y"], ["p", "q"]])
val second = t.child_at(1)
expect second != nil to_equal true
expect second.get_prop("label") to_equal "p|q"
```

</details>

#### has correct child count matching row count

1. expect t child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = table_widget("tbl_count_1", ["A"], [["1"], ["2"], ["3"]])
expect t.child_count() to_equal 3
```

</details>

#### empty rows produce zero children

1. expect t child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = table_widget("tbl_empty_1", ["A", "B"], [])
expect t.child_count() to_equal 0
```

</details>

### table_row helper

#### creates text kind node

1. expect r kind name


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = table_row("tr_kind_1", ["a", "b"])
expect r.kind_name() to_equal "text"
```

</details>

#### label is cells joined by pipe

1. expect r get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = table_row("tr_label_1", ["hello", "world"])
expect r.get_prop("label") to_equal "hello|world"
```

</details>

#### single cell has no pipe

1. expect r get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = table_row("tr_single_1", ["only"])
expect r.get_prop("label") to_equal "only"
```

</details>

### table HTML rendering

#### output contains th tags for headers

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = table_widget("tbl_html_1", ["Name", "Age"], [["Alice", "30"]])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "<th"
```

</details>

#### output contains thead element

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = table_widget("tbl_html_2", ["Col1"], [["val1"]])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "<thead>"
```

</details>

#### output contains tbody element

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = table_widget("tbl_html_3", ["Col1"], [["val1"]])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "<tbody>"
```

</details>

#### output contains table-filter input

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = table_widget("tbl_html_4", ["A"], [["x"]])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "table-filter"
```

</details>

#### output contains widget-table class

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = table_widget("tbl_html_5", ["A"], [])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "widget-table"
```

</details>

#### output contains header text

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = table_widget("tbl_html_6", ["Name", "Score"], [])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "Name"
expect html to_contain "Score"
```

</details>

#### output contains td tags for cell data

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = table_widget("tbl_html_7", ["A"], [["hello"]])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "<td>"
```

</details>

#### output contains data-action for sort on headers

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = table_widget("tbl_html_8", ["Col1", "Col2"], [])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "data-action=\"sort_col_0\""
expect html to_contain "data-action=\"sort_col_1\""
```

</details>

#### output includes filter data-action with table id

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = table_widget("tbl_html_9", ["X"], [])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "data-action=\"filter_tbl_html_9\""
```

</details>

### with_selected modifier

#### sets selected_index prop

1. var lw = list widget
2. lw = with selected
3. expect lw get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lw = list_widget("ls_sel_1", ["A", "B", "C"])
lw = with_selected(lw, 1)
expect lw.get_prop("selected_index") to_equal "1"
```

</details>

#### default list has no selected_index

1. expect lw get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lw = list_widget("ls_nosel_1", ["A", "B"])
expect lw.get_prop("selected_index") to_equal ""
```

</details>

#### selected_index zero is valid

1. var lw = list widget
2. lw = with selected
3. expect lw get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lw = list_widget("ls_sel_2", ["First"])
lw = with_selected(lw, 0)
expect lw.get_prop("selected_index") to_equal "0"
```

</details>

#### can change selected index

1. var lw = list widget
2. lw = with selected
3. expect lw get prop
4. lw = with selected
5. expect lw get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lw = list_widget("ls_sel_3", ["A", "B", "C"])
lw = with_selected(lw, 0)
expect lw.get_prop("selected_index") to_equal "0"
lw = with_selected(lw, 2)
expect lw.get_prop("selected_index") to_equal "2"
```

</details>

### list HTML rendering with selection

#### selected item has selected class

1. var node = list widget
2. node = with selected


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = list_widget("ls_html_1", ["Apple", "Banana", "Cherry"])
node = with_selected(node, 1)
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "selected"
```

</details>

#### selected item has list-item selected class

1. var node = list widget
2. node = with selected


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = list_widget("ls_html_2", ["X", "Y"])
node = with_selected(node, 0)
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "list-item selected"
```

</details>

#### non-selected items have list-item class only

1. var node = list widget
2. node = with selected


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = list_widget("ls_html_3", ["A", "B"])
node = with_selected(node, 0)
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "list-item\""
```

</details>

#### no selection means no selected class

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = list_widget("ls_html_4", ["One", "Two"])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
# All items should be "list-item" without "selected"
expect html to_contain "list-item"
```

</details>

#### output still contains widget-list class

1. var node = list widget
2. node = with selected


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = list_widget("ls_html_5", ["Item"])
node = with_selected(node, 0)
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "widget-list"
```

</details>

#### output starts with ul tag

1. var node = list widget
2. node = with selected


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = list_widget("ls_html_6", ["A"])
node = with_selected(node, 0)
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_start_with "<ul"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/widget_table_list_upgrade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- table_widget creation
- table_row helper
- table HTML rendering
- with_selected modifier
- list HTML rendering with selection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
