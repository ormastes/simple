# Widget Menu Tooltip Specification

> 1. expect sep kind name

<!-- sdn-diagram:id=widget_menu_tooltip_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=widget_menu_tooltip_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

widget_menu_tooltip_spec -> common
widget_menu_tooltip_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=widget_menu_tooltip_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Widget Menu Tooltip Specification

## Scenarios

### menu_separator builder

#### creates a text widget

1. expect sep kind name


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sep = menu_separator("msep_kind_1")
expect sep.kind_name() to_equal "text"
```

</details>

#### has is_separator prop set to true

1. expect sep get prop


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sep = menu_separator("msep_prop_1")
expect sep.get_prop("is_separator") to_equal "true"
```

</details>

#### has label set to pipe character

1. expect sep get prop


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sep = menu_separator("msep_label_1")
expect sep.get_prop("label") to_equal "|"
```

</details>

#### has correct id

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sep = menu_separator("msep_id_1")
expect sep.id to_equal "msep_id_1"
```

</details>

#### has no children

1. expect sep child count


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sep = menu_separator("msep_child_1")
expect sep.child_count() to_equal 0
```

</details>

### menu_with_submenu builder

#### creates a text widget

1. expect sub kind name


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sub = menu_with_submenu("msub_kind_1", "Edit", [])
expect sub.kind_name() to_equal "text"
```

</details>

#### has has_submenu prop set to true

1. expect sub get prop


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sub = menu_with_submenu("msub_prop_1", "Edit", [])
expect sub.get_prop("has_submenu") to_equal "true"
```

</details>

#### has label set to given text

1. expect sub get prop


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sub = menu_with_submenu("msub_label_1", "Edit", [])
expect sub.get_prop("label") to_equal "Edit"
```

</details>

#### stores children as submenu items

1. expect sub child count


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cut = label("msub_cut_1", "Cut")
val copy = label("msub_copy_1", "Copy")
val sub = menu_with_submenu("msub_children_1", "Edit", [cut, copy])
expect sub.child_count() to_equal 2
```

</details>

#### first child has correct label

1. expect first get prop


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cut = label("msub_cut_2", "Cut")
val copy = label("msub_copy_2", "Copy")
val sub = menu_with_submenu("msub_children_2", "Edit", [cut, copy])
val first = sub.child_at(0)
expect first.get_prop("label") to_equal "Cut"
```

</details>

#### has correct id

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sub = menu_with_submenu("msub_id_1", "View", [])
expect sub.id to_equal "msub_id_1"
```

</details>

### menubar_rich builder

#### creates a menubar kind widget

1. expect bar kind name


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = menubar_rich("mrich_kind_1", [])
expect bar.kind_name() to_equal "menubar"
```

</details>

#### accepts mixed items

1. expect bar child count


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file_item = label("mrich_file_1", "File")
val sep = menu_separator("mrich_sep_1")
val edit_cut = label("mrich_edit_cut_1", "Cut")
val edit_sub = menu_with_submenu("mrich_edit_1", "Edit", [edit_cut])
val bar = menubar_rich("mrich_mixed_1", [file_item, sep, edit_sub])
expect bar.child_count() to_equal 3
```

</details>

#### first child is a normal item

1. expect first get prop


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file_item = label("mrich_file_2", "File")
val sep = menu_separator("mrich_sep_2")
val bar = menubar_rich("mrich_order_1", [file_item, sep])
val first = bar.child_at(0)
expect first.get_prop("label") to_equal "File"
```

</details>

#### second child is a separator

1. expect second get prop


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file_item = label("mrich_file_3", "File")
val sep = menu_separator("mrich_sep_3")
val bar = menubar_rich("mrich_order_2", [file_item, sep])
val second = bar.child_at(1)
expect second.get_prop("is_separator") to_equal "true"
```

</details>

#### third child is a submenu

1. expect third get prop


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file_item = label("mrich_file_4", "File")
val sep = menu_separator("mrich_sep_4")
val edit_sub = menu_with_submenu("mrich_edit_4", "Edit", [])
val bar = menubar_rich("mrich_order_3", [file_item, sep, edit_sub])
val third = bar.child_at(2)
expect third.get_prop("has_submenu") to_equal "true"
```

</details>

### TUI menubar separator rendering

#### separator shows pipe character in output

1. var screen = Screen new

2. screen = render tui menubar


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file_item = label("tui_sep_file_1", "File")
val sep = menu_separator("tui_sep_sep_1")
val view_item = label("tui_sep_view_1", "View")
val bar = menubar_rich("tui_sep_bar_1", [file_item, sep, view_item])
val rect = WidgetRect(id: "tui_sep_bar_1", x: 0, y: 0, w: 80, h: 1)
var screen = Screen.new(80, 1)
screen = render_tui_menubar(screen, bar, rect)
val row_text = screen.buffer[0]
expect row_text to_contain "|"
```

</details>

#### submenu label appears in output

1. var screen = Screen new

2. screen = render tui menubar


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val edit_sub = menu_with_submenu("tui_sub_edit_1", "Edit", [])
val bar = menubar_rich("tui_sub_bar_1", [edit_sub])
val rect = WidgetRect(id: "tui_sub_bar_1", x: 0, y: 0, w: 80, h: 1)
var screen = Screen.new(80, 1)
screen = render_tui_menubar(screen, bar, rect)
val row_text = screen.buffer[0]
expect row_text to_contain "Edit"
```

</details>

#### normal items still render correctly

1. var screen = Screen new

2. screen = render tui menubar


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file_item = label("tui_norm_file_1", "File")
val bar = menubar_rich("tui_norm_bar_1", [file_item])
val rect = WidgetRect(id: "tui_norm_bar_1", x: 0, y: 0, w: 80, h: 1)
var screen = Screen.new(80, 1)
screen = render_tui_menubar(screen, bar, rect)
val row_text = screen.buffer[0]
expect row_text to_contain "File"
```

</details>

### HTML menubar separator rendering

#### separator has menu-separator class

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file_item = label("html_sep_file_1", "File")
val sep = menu_separator("html_sep_sep_1")
val bar = menubar_rich("html_sep_bar_1", [file_item, sep])
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_contain "menu-separator"
```

</details>

#### submenu has submenu class

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cut = label("html_sub_cut_1", "Cut")
val edit_sub = menu_with_submenu("html_sub_edit_1", "Edit", [cut])
val bar = menubar_rich("html_sub_bar_1", [edit_sub])
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_contain "submenu"
```

</details>

#### submenu has has-submenu class on menu-item

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cut = label("html_sub_cut_2", "Cut")
val edit_sub = menu_with_submenu("html_sub_edit_2", "Edit", [cut])
val bar = menubar_rich("html_sub_bar_2", [edit_sub])
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_contain "has-submenu"
```

</details>

#### normal items still have menu-item class

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file_item = label("html_norm_file_1", "File")
val bar = menubar_rich("html_norm_bar_1", [file_item])
val tree = build_tree(bar)
val state = init_state(tree)
val html = render_html_widget(bar, state)
expect html to_contain "menu-item"
```

</details>

### Tooltip builder

#### creates widget with content and target props

1. expect tt get prop

2. expect tt get prop


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tt = tooltip("tt_build_1", "Help text", "btn_1")
expect tt.get_prop("content") to_equal "Help text"
expect tt.get_prop("target") to_equal "btn_1"
```

</details>

#### has kind tooltip

1. expect tt kind name


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tt = tooltip("tt_build_2", "Info", "link_1")
expect tt.kind_name() to_equal "tooltip"
```

</details>

### TUI tooltip rendering

#### output is NOT empty after fix

1. var screen = Screen new

2. screen = render tui tooltip


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tt = tooltip("tui_tt_fix_1", "Click to submit", "submit_btn")
val rect = WidgetRect(id: "tui_tt_fix_1", x: 0, y: 0, w: 80, h: 1)
var screen = Screen.new(80, 1)
screen = render_tui_tooltip(screen, tt, rect)
val row_text = screen.buffer[0]
expect row_text to_contain "[?]"
```

</details>

#### output contains content text

1. var screen = Screen new

2. screen = render tui tooltip


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tt = tooltip("tui_tt_fix_2", "Click to submit", "submit_btn_2")
val rect = WidgetRect(id: "tui_tt_fix_2", x: 0, y: 0, w: 80, h: 1)
var screen = Screen.new(80, 1)
screen = render_tui_tooltip(screen, tt, rect)
val row_text = screen.buffer[0]
expect row_text to_contain "Click to submit"
```

</details>

#### renders at correct position

1. var screen = Screen new

2. screen = render tui tooltip


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tt = tooltip("tui_tt_pos_1", "Tip", "tgt_1")
val rect = WidgetRect(id: "tui_tt_pos_1", x: 5, y: 2, w: 40, h: 1)
var screen = Screen.new(80, 5)
screen = render_tui_tooltip(screen, tt, rect)
val row_text = screen.buffer[2]
expect row_text to_contain "[?]"
```

</details>

### HTML tooltip rendering

#### contains tooltip-trigger span

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tt = tooltip("html_tt_trig_1", "Info here", "info_btn")
val tree = build_tree(tt)
val state = init_state(tree)
val html = render_html_widget(tt, state)
expect html to_contain "tooltip-trigger"
```

</details>

#### contains tooltip-content span

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tt = tooltip("html_tt_cont_1", "Info here", "info_btn_2")
val tree = build_tree(tt)
val state = init_state(tree)
val html = render_html_widget(tt, state)
expect html to_contain "tooltip-content"
```

</details>

#### trigger contains question mark

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tt = tooltip("html_tt_qmark_1", "Details", "det_btn")
val tree = build_tree(tt)
val state = init_state(tree)
val html = render_html_widget(tt, state)
expect html to_contain "[?]"
```

</details>

#### content span contains tooltip text

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tt = tooltip("html_tt_text_1", "Press Enter to save", "save_btn")
val tree = build_tree(tt)
val state = init_state(tree)
val html = render_html_widget(tt, state)
expect html to_contain "Press Enter to save"
```

</details>

#### output contains data-target attribute

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tt = tooltip("html_tt_dtar_1", "Tip", "my_target")
val tree = build_tree(tt)
val state = init_state(tree)
val html = render_html_widget(tt, state)
expect html to_contain "data-target=\"my_target\""
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/widget_menu_tooltip_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- menu_separator builder
- menu_with_submenu builder
- menubar_rich builder
- TUI menubar separator rendering
- HTML menubar separator rendering
- Tooltip builder
- TUI tooltip rendering
- HTML tooltip rendering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
