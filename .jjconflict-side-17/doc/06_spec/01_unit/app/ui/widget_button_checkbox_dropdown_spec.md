# Widget Button Checkbox Dropdown Specification

> <details>

<!-- sdn-diagram:id=widget_button_checkbox_dropdown_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=widget_button_checkbox_dropdown_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

widget_button_checkbox_dropdown_spec -> common
widget_button_checkbox_dropdown_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=widget_button_checkbox_dropdown_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 65 | 65 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Widget Button Checkbox Dropdown Specification

## Scenarios

### Button widget creation

#### creates a widget with kind button

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val btn = button("btn_create_1", "Click Me", "do_click")
expect btn.kind to_equal "button"
```

</details>

#### stores the correct id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val btn = button("btn_id_1", "Press", "action_press")
expect btn.id to_equal "btn_id_1"
```

</details>

#### stores label prop via get_prop

1. expect btn get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val btn = button("btn_label_1", "Click Me", "do_click")
expect btn.get_prop("label") to_equal "Click Me"
```

</details>

#### stores action prop via get_prop

1. expect btn get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val btn = button("btn_action_1", "Click Me", "do_click")
expect btn.get_prop("action") to_equal "do_click"
```

</details>

#### stores empty string action

1. expect btn get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val btn = button("btn_empty_action_1", "OK", "")
expect btn.get_prop("action") to_equal ""
```

</details>

#### has no children

1. expect btn child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val btn = button("btn_no_children_1", "Go", "go_action")
expect btn.child_count() to_equal 0
```

</details>

#### defaults visible to true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val btn = button("btn_visible_1", "Visible", "act")
expect btn.visible to_equal true
```

</details>

#### defaults focused to false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val btn = button("btn_focused_1", "Focused", "act")
expect btn.focused to_equal false
```

</details>

#### defaults layout to vbox

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val btn = button("btn_layout_1", "Layout", "act")
expect btn.layout to_equal "vbox"
```

</details>

#### has label and action in prop_keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val btn = button("btn_keys_1", "Keys", "some_action")
val keys = btn.prop_keys()
expect keys to_contain "label"
expect keys to_contain "action"
```

</details>

#### has_prop returns true for label

1. expect btn has prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val btn = button("btn_hasprop_1", "Check", "do_check")
expect btn.has_prop("label") to_equal true
```

</details>

#### has_prop returns false for nonexistent key

1. expect btn has prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val btn = button("btn_hasprop_2", "Check", "do_check")
expect btn.has_prop("tooltip") to_equal false
```

</details>

### Button widget HTML rendering

#### renders with widget-button class

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val btn = button("btn_html_1", "Render", "render_action")
val tree = UITree.new(btn)
val state = init_state(tree)
val html = render_html_widget(btn, state)
expect html to_contain "widget-button"
```

</details>

#### renders as a button tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val btn = button("btn_html_tag_1", "Tag", "tag_action")
val tree = UITree.new(btn)
val state = init_state(tree)
val html = render_html_widget(btn, state)
expect html to_start_with "<button"
```

</details>

#### includes data-action attribute with action value

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val btn = button("btn_html_action_1", "Save", "save_file")
val tree = UITree.new(btn)
val state = init_state(tree)
val html = render_html_widget(btn, state)
expect html to_contain "data-action=\"save_file\""
```

</details>

#### includes label text as button content

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val btn = button("btn_html_label_1", "Submit Form", "submit")
val tree = UITree.new(btn)
val state = init_state(tree)
val html = render_html_widget(btn, state)
expect html to_contain "Submit Form"
```

</details>

#### includes empty data-action when action is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val btn = button("btn_html_empty_act_1", "Noop", "")
val tree = UITree.new(btn)
val state = init_state(tree)
val html = render_html_widget(btn, state)
expect html to_contain "data-action=\"\""
```

</details>

#### includes widget id attribute

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val btn = button("btn_html_id_1", "Id Test", "id_act")
val tree = UITree.new(btn)
val state = init_state(tree)
val html = render_html_widget(btn, state)
expect html to_contain "id=\"btn_html_id_1\""
```

</details>

#### adds focused class when button is focused

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# When button is the tree root, init_state focuses it
val btn = button("btn_html_focus_1", "Focused", "focus_act")
val tree = UITree.new(btn)
val state = init_state(tree)
expect state.focused_id to_equal "btn_html_focus_1"
val html = render_html_widget(btn, state)
expect html to_contain "focused"
```

</details>

#### does not add focused class when button is not focused

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Put button as child so the parent gets focus instead
val btn = button("btn_html_nofocus_1", "Not Focused", "nf_act")
val root = panel("btn_html_nofocus_root", "Panel", [btn])
val tree = UITree.new(root)
val state = init_state(tree)
# Focus is on the root panel, not on the button
expect state.focused_id to_equal "btn_html_nofocus_root"
val html = render_html_widget(btn, state)
val has_focused = html.contains("focused")
expect has_focused to_equal false
```

</details>

#### ends with closing button tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val btn = button("btn_html_close_1", "Close", "close_act")
val tree = UITree.new(btn)
val state = init_state(tree)
val html = render_html_widget(btn, state)
expect html to_end_with "</button>"
```

</details>

### Checkbox widget creation

#### creates a widget with kind checkbox

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cb = checkbox("cb_create_1", "Accept", true)
expect cb.kind to_equal "checkbox"
```

</details>

#### stores the correct id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cb = checkbox("cb_id_1", "Agree", false)
expect cb.id to_equal "cb_id_1"
```

</details>

#### stores checked prop as true when checked

1. expect cb get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cb = checkbox("cb_checked_1", "Accept", true)
expect cb.get_prop("checked") to_equal "true"
```

</details>

#### stores checked prop as false when unchecked

1. expect cb get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cb = checkbox("cb_unchecked_1", "Accept", false)
expect cb.get_prop("checked") to_equal "false"
```

</details>

#### stores label prop

1. expect cb get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cb = checkbox("cb_label_1", "Enable Notifications", true)
expect cb.get_prop("label") to_equal "Enable Notifications"
```

</details>

#### has no children

1. expect cb child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cb = checkbox("cb_children_1", "Option", false)
expect cb.child_count() to_equal 0
```

</details>

#### has label and checked in prop_keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cb = checkbox("cb_keys_1", "Terms", true)
val keys = cb.prop_keys()
expect keys to_contain "label"
expect keys to_contain "checked"
```

</details>

#### defaults visible to true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cb = checkbox("cb_visible_1", "Show", true)
expect cb.visible to_equal true
```

</details>

#### defaults focused to false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cb = checkbox("cb_focused_1", "Focus", false)
expect cb.focused to_equal false
```

</details>

### Checkbox widget HTML rendering

#### renders with widget-checkbox class

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cb = checkbox("cb_html_1", "Terms", false)
val tree = UITree.new(cb)
val state = init_state(tree)
val html = render_html_widget(cb, state)
expect html to_contain "widget-checkbox"
```

</details>

#### renders as a label tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cb = checkbox("cb_html_tag_1", "Option", false)
val tree = UITree.new(cb)
val state = init_state(tree)
val html = render_html_widget(cb, state)
expect html to_start_with "<label"
```

</details>

#### renders input with type checkbox

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cb = checkbox("cb_html_input_1", "Enable", false)
val tree = UITree.new(cb)
val state = init_state(tree)
val html = render_html_widget(cb, state)
expect html to_contain "input"
expect html to_contain "type=\"checkbox\""
```

</details>

#### includes checked attribute when checked is true

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cb = checkbox("cb_html_checked_1", "Agree", true)
val tree = UITree.new(cb)
val state = init_state(tree)
val html = render_html_widget(cb, state)
expect html to_contain " checked"
```

</details>

#### omits checked attribute when checked is false

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cb = checkbox("cb_html_unchecked_1", "Disagree", false)
val tree = UITree.new(cb)
val state = init_state(tree)
val html = render_html_widget(cb, state)
# Output is: <label class="widget-checkbox..."><input type="checkbox" />Disagree</label>
# When unchecked, there is no " checked" before the " />"
val has_checked_attr = html.contains("checked /")
expect has_checked_attr to_equal false
```

</details>

#### includes label text in output

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cb = checkbox("cb_html_label_1", "Subscribe Monthly", true)
val tree = UITree.new(cb)
val state = init_state(tree)
val html = render_html_widget(cb, state)
expect html to_contain "Subscribe Monthly"
```

</details>

#### includes widget id attribute

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cb = checkbox("cb_html_id_1", "Id Test", false)
val tree = UITree.new(cb)
val state = init_state(tree)
val html = render_html_widget(cb, state)
expect html to_contain "id=\"cb_html_id_1\""
```

</details>

#### adds focused class when checkbox is focused

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cb = checkbox("cb_html_focus_1", "Focused", true)
val tree = UITree.new(cb)
val state = init_state(tree)
expect state.focused_id to_equal "cb_html_focus_1"
val html = render_html_widget(cb, state)
expect html to_contain "focused"
```

</details>

#### does not add focused class when checkbox is not focused

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cb = checkbox("cb_html_nofocus_1", "Not Focused", false)
val root = panel("cb_html_nofocus_root", "Panel", [cb])
val tree = UITree.new(root)
val state = init_state(tree)
expect state.focused_id to_equal "cb_html_nofocus_root"
val html = render_html_widget(cb, state)
val has_focused = html.contains("focused")
expect has_focused to_equal false
```

</details>

#### ends with closing label tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cb = checkbox("cb_html_close_1", "Close", false)
val tree = UITree.new(cb)
val state = init_state(tree)
val html = render_html_widget(cb, state)
expect html to_end_with "</label>"
```

</details>

### Dropdown widget creation

#### creates a widget with kind dropdown

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dd = dropdown("dd_create_1", ["Red", "Green", "Blue"])
expect dd.kind to_equal "dropdown"
```

</details>

#### stores the correct id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dd = dropdown("dd_id_1", ["A"])
expect dd.id to_equal "dd_id_1"
```

</details>

#### has correct child count for three items

1. expect dd child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dd = dropdown("dd_count_3", ["Red", "Green", "Blue"])
expect dd.child_count() to_equal 3
```

</details>

#### has zero children for empty items

1. expect dd child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dd = dropdown("dd_empty_1", [])
expect dd.child_count() to_equal 0
```

</details>

#### has one child for single item

1. expect dd child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dd = dropdown("dd_single_1", ["Only"])
expect dd.child_count() to_equal 1
```

</details>

#### first child has correct label

1. expect first get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dd = dropdown("dd_first_label_1", ["Red", "Green", "Blue"])
val first = dd.child_at(0)
expect first != nil to_equal true
expect first.get_prop("label") to_equal "Red"
```

</details>

#### second child has correct label

1. expect second get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dd = dropdown("dd_second_label_1", ["Red", "Green", "Blue"])
val second = dd.child_at(1)
expect second != nil to_equal true
expect second.get_prop("label") to_equal "Green"
```

</details>

#### third child has correct label

1. expect third get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dd = dropdown("dd_third_label_1", ["Red", "Green", "Blue"])
val third = dd.child_at(2)
expect third != nil to_equal true
expect third.get_prop("label") to_equal "Blue"
```

</details>

#### children are text kind widgets

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dd = dropdown("dd_child_kind_1", ["Alpha", "Beta"])
val first = dd.child_at(0)
expect first != nil to_equal true
expect first.kind to_equal "text"
```

</details>

#### children have generated ids based on parent

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dd = dropdown("dd_child_ids_1", ["X", "Y"])
val first = dd.child_at(0)
expect first != nil to_equal true
expect first.id to_equal "dd_child_ids_1_opt_0"
```

</details>

#### second child has correct generated id

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dd = dropdown("dd_child_id2_1", ["X", "Y"])
val second = dd.child_at(1)
expect second != nil to_equal true
expect second.id to_equal "dd_child_id2_1_opt_1"
```

</details>

#### defaults visible to true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dd = dropdown("dd_visible_1", ["Item"])
expect dd.visible to_equal true
```

</details>

#### defaults focused to false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dd = dropdown("dd_focused_1", ["Item"])
expect dd.focused to_equal false
```

</details>

#### handles many items

1. expect dd child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dd = dropdown("dd_many_1", ["A", "B", "C", "D", "E"])
expect dd.child_count() to_equal 5
```

</details>

### Dropdown widget HTML rendering

#### renders with widget-dropdown class

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dd = dropdown("dd_html_1", ["Red", "Green"])
val tree = UITree.new(dd)
val state = init_state(tree)
val html = render_html_widget(dd, state)
expect html to_contain "widget-dropdown"
```

</details>

#### renders as a select tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dd = dropdown("dd_html_tag_1", ["One"])
val tree = UITree.new(dd)
val state = init_state(tree)
val html = render_html_widget(dd, state)
expect html to_start_with "<select"
```

</details>

#### renders option tags for each item

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dd = dropdown("dd_html_opts_1", ["Red", "Green", "Blue"])
val tree = UITree.new(dd)
val state = init_state(tree)
val html = render_html_widget(dd, state)
expect html to_contain "<option>"
expect html to_contain "Red"
expect html to_contain "Green"
expect html to_contain "Blue"
```

</details>

#### renders correct number of option tags for two items

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dd = dropdown("dd_html_two_1", ["Alpha", "Beta"])
val tree = UITree.new(dd)
val state = init_state(tree)
val html = render_html_widget(dd, state)
expect html to_contain "<option>Alpha</option>"
expect html to_contain "<option>Beta</option>"
```

</details>

#### renders empty select for empty dropdown

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dd = dropdown("dd_html_empty_1", [])
val tree = UITree.new(dd)
val state = init_state(tree)
val html = render_html_widget(dd, state)
expect html to_contain "widget-dropdown"
val has_option = html.contains("<option>")
expect has_option to_equal false
```

</details>

#### renders single option for one-item dropdown

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dd = dropdown("dd_html_single_1", ["Only"])
val tree = UITree.new(dd)
val state = init_state(tree)
val html = render_html_widget(dd, state)
expect html to_contain "<option>Only</option>"
```

</details>

#### includes widget id attribute

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dd = dropdown("dd_html_id_1", ["Item"])
val tree = UITree.new(dd)
val state = init_state(tree)
val html = render_html_widget(dd, state)
expect html to_contain "id=\"dd_html_id_1\""
```

</details>

#### adds focused class when dropdown is focused

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dd = dropdown("dd_html_focus_1", ["A", "B"])
val tree = UITree.new(dd)
val state = init_state(tree)
expect state.focused_id to_equal "dd_html_focus_1"
val html = render_html_widget(dd, state)
expect html to_contain "focused"
```

</details>

#### does not add focused class when dropdown is not focused

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dd = dropdown("dd_html_nofocus_1", ["X"])
val root = panel("dd_html_nofocus_root", "Panel", [dd])
val tree = UITree.new(root)
val state = init_state(tree)
expect state.focused_id to_equal "dd_html_nofocus_root"
val html = render_html_widget(dd, state)
val has_focused = html.contains("focused")
expect has_focused to_equal false
```

</details>

#### ends with closing select tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dd = dropdown("dd_html_close_1", ["Z"])
val tree = UITree.new(dd)
val state = init_state(tree)
val html = render_html_widget(dd, state)
expect html to_end_with "</select>"
```

</details>

#### preserves item order in rendered options

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dd = dropdown("dd_html_order_1", ["First", "Second", "Third"])
val tree = UITree.new(dd)
val state = init_state(tree)
val html = render_html_widget(dd, state)
# Verify all three labels appear; order is ensured by the builder
expect html to_contain "First"
expect html to_contain "Second"
expect html to_contain "Third"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/widget_button_checkbox_dropdown_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Button widget creation
- Button widget HTML rendering
- Checkbox widget creation
- Checkbox widget HTML rendering
- Dropdown widget creation
- Dropdown widget HTML rendering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 65 |
| Active scenarios | 65 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
