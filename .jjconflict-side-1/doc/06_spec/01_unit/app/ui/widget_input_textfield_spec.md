# Widget Input Textfield Specification

> <details>

<!-- sdn-diagram:id=widget_input_textfield_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=widget_input_textfield_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

widget_input_textfield_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=widget_input_textfield_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 46 | 46 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Widget Input Textfield Specification

## Scenarios

### Input widget

#### creation

#### creates a widget with kind input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_input("inp_create_1", "Type here...")
expect w.kind to_equal "input"
```

</details>

#### assigns the correct id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_input("inp_create_2", "Search...")
expect w.id to_equal "inp_create_2"
```

</details>

#### is visible by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_input("inp_visible_1", "Prompt")
expect w.visible to_equal true
```

</details>

#### is not focused by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_input("inp_focus_1", "Prompt")
expect w.focused to_equal false
```

</details>

#### placeholder property

#### stores the placeholder text

1. expect w get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_input("inp_ph_1", "Type here...")
expect w.get_prop("placeholder") to_equal "Type here..."
```

</details>

#### stores an empty placeholder

1. expect w get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_input("inp_ph_2", "")
expect w.get_prop("placeholder") to_equal ""
```

</details>

#### stores a long placeholder string

1. expect w get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_input("inp_ph_3", "Enter your full name and email address")
expect w.get_prop("placeholder") to_equal "Enter your full name and email address"
```

</details>

#### children

#### has no children

1. expect w child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_input("inp_child_1", "Search...")
expect w.child_count() to_equal 0
```

</details>

#### property inspection

#### reports placeholder via has_prop

1. expect w has prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_input("inp_hasprop_1", "Hint text")
expect w.has_prop("placeholder") to_equal true
```

</details>

#### reports false for absent properties

1. expect w has prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_input("inp_hasprop_2", "Hint text")
expect w.has_prop("value") to_equal false
```

</details>

#### lists placeholder in prop_keys

1. expect keys contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_input("inp_keys_1", "Hint")
val keys = w.prop_keys()
expect keys.contains("placeholder") to_equal true
```

</details>

#### HTML rendering

#### contains widget-input class

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_input("inp_html_1", "Search...")
val state = make_state_unfocused(w)
val html = render_html_widget(w, state)
expect html to_contain "widget-input"
```

</details>

#### contains placeholder attribute

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_input("inp_html_2", "Type here...")
val state = make_state_unfocused(w)
val html = render_html_widget(w, state)
expect html to_contain "placeholder"
```

</details>

#### contains the placeholder value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_input("inp_html_3", "Search files...")
val state = make_state_unfocused(w)
val html = render_html_widget(w, state)
expect html to_contain "Search files..."
```

</details>

#### contains the widget id

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_input("inp_html_4", "Prompt")
val state = make_state_unfocused(w)
val html = render_html_widget(w, state)
expect html to_contain "inp_html_4"
```

</details>

#### renders as a self-closing input tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_input("inp_html_5", "Go")
val state = make_state_unfocused(w)
val html = render_html_widget(w, state)
expect html to_contain "/>"
```

</details>

#### contains focused class when focused

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_input("inp_html_focus_1", "Enter query")
val state = make_state_focused(w)
val html = render_html_widget(w, state)
expect html to_contain "focused"
```

</details>

#### does not contain focused class when unfocused

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_input("inp_html_focus_2", "Enter query")
val state = make_state_unfocused(w)
val html = render_html_widget(w, state)
val has_focused = html.contains("focused")
expect has_focused to_equal false
```

</details>

### TextField widget

#### creation

#### creates a widget with kind textfield

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_field("tf_create_1", "hello", "Enter text")
expect w.kind to_equal "textfield"
```

</details>

#### assigns the correct id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_field("tf_create_2", "data", "Hint")
expect w.id to_equal "tf_create_2"
```

</details>

#### is visible by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_field("tf_visible_1", "v", "p")
expect w.visible to_equal true
```

</details>

#### is not focused by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_field("tf_focus_1", "v", "p")
expect w.focused to_equal false
```

</details>

#### value property

#### stores the value

1. expect w get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_field("tf_val_1", "hello", "Enter text")
expect w.get_prop("value") to_equal "hello"
```

</details>

#### stores an empty value

1. expect w get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_field("tf_val_2", "", "Hint")
expect w.get_prop("value") to_equal ""
```

</details>

#### stores a long value string

1. expect w get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_field("tf_val_3", "The quick brown fox jumps over the lazy dog", "Type")
expect w.get_prop("value") to_equal "The quick brown fox jumps over the lazy dog"
```

</details>

#### placeholder property

#### stores the placeholder text

1. expect w get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_field("tf_ph_1", "hello", "Enter text")
expect w.get_prop("placeholder") to_equal "Enter text"
```

</details>

#### stores an empty placeholder

1. expect w get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_field("tf_ph_2", "val", "")
expect w.get_prop("placeholder") to_equal ""
```

</details>

#### both properties empty

#### stores both as empty strings

1. expect w get prop
2. expect w get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_field("tf_both_1", "", "")
expect w.get_prop("value") to_equal ""
expect w.get_prop("placeholder") to_equal ""
```

</details>

#### property inspection

#### reports value via has_prop

1. expect w has prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_field("tf_hasprop_1", "data", "Hint")
expect w.has_prop("value") to_equal true
```

</details>

#### reports placeholder via has_prop

1. expect w has prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_field("tf_hasprop_2", "data", "Hint")
expect w.has_prop("placeholder") to_equal true
```

</details>

#### reports false for absent properties

1. expect w has prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_field("tf_hasprop_3", "data", "Hint")
expect w.has_prop("action") to_equal false
```

</details>

#### lists both value and placeholder in prop_keys

1. expect keys contains
2. expect keys contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_field("tf_keys_1", "x", "y")
val keys = w.prop_keys()
expect keys.contains("value") to_equal true
expect keys.contains("placeholder") to_equal true
```

</details>

#### children

#### has no children

1. expect w child count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_field("tf_child_1", "v", "p")
expect w.child_count() to_equal 0
```

</details>

#### HTML rendering

#### contains widget-textfield class

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_field("tf_html_1", "hello", "Enter text")
val state = make_state_unfocused(w)
val html = render_html_widget(w, state)
expect html to_contain "widget-textfield"
```

</details>

#### contains type text attribute

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_field("tf_html_2", "hello", "Enter text")
val state = make_state_unfocused(w)
val html = render_html_widget(w, state)
expect html to_contain "type=\"text\""
```

</details>

#### contains the value in the value attribute

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_field("tf_html_3", "my_value", "Hint")
val state = make_state_unfocused(w)
val html = render_html_widget(w, state)
expect html to_contain "my_value"
```

</details>

#### contains the placeholder attribute

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_field("tf_html_4", "v", "Enter name")
val state = make_state_unfocused(w)
val html = render_html_widget(w, state)
expect html to_contain "placeholder"
```

</details>

#### contains the placeholder value text

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_field("tf_html_5", "v", "Enter name")
val state = make_state_unfocused(w)
val html = render_html_widget(w, state)
expect html to_contain "Enter name"
```

</details>

#### contains the widget id

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_field("tf_html_6", "v", "p")
val state = make_state_unfocused(w)
val html = render_html_widget(w, state)
expect html to_contain "tf_html_6"
```

</details>

#### renders value attribute with correct format

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_field("tf_html_7", "test_data", "Hint")
val state = make_state_unfocused(w)
val html = render_html_widget(w, state)
expect html to_contain "value=\"test_data\""
```

</details>

#### renders placeholder attribute with correct format

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_field("tf_html_8", "v", "Search here")
val state = make_state_unfocused(w)
val html = render_html_widget(w, state)
expect html to_contain "placeholder=\"Search here\""
```

</details>

#### renders as a self-closing input tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_field("tf_html_9", "v", "p")
val state = make_state_unfocused(w)
val html = render_html_widget(w, state)
expect html to_contain "/>"
```

</details>

#### contains focused class when focused

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_field("tf_html_focus_1", "val", "hint")
val state = make_state_focused(w)
val html = render_html_widget(w, state)
expect html to_contain "focused"
```

</details>

#### does not contain focused class when unfocused

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_field("tf_html_focus_2", "val", "hint")
val state = make_state_unfocused(w)
val html = render_html_widget(w, state)
val has_focused = html.contains("focused")
expect has_focused to_equal false
```

</details>

#### renders empty value correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_field("tf_html_empty_1", "", "Hint")
val state = make_state_unfocused(w)
val html = render_html_widget(w, state)
expect html to_contain "value=\"\""
```

</details>

#### renders empty placeholder correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = text_field("tf_html_empty_2", "data", "")
val state = make_state_unfocused(w)
val html = render_html_widget(w, state)
expect html to_contain "placeholder=\"\""
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/widget_input_textfield_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Input widget
- TextField widget

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 46 |
| Active scenarios | 46 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
