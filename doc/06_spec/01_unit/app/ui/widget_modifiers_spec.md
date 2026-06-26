# Widget Modifiers Specification

> 1. var node = button

<!-- sdn-diagram:id=widget_modifiers_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=widget_modifiers_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

widget_modifiers_spec -> common
widget_modifiers_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=widget_modifiers_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Widget Modifiers Specification

## Scenarios

### with_disabled modifier

#### sets disabled prop to true

1. var node = button
2. node = with disabled
3. expect node get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = button("wm_dis_1", "Save", "save")
node = with_disabled(node)
expect node.get_prop("disabled") to_equal "true"
```

</details>

#### works on input widget

1. var node = text input
2. node = with disabled
3. expect node get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = text_input("wm_dis_inp_1", "Type here")
node = with_disabled(node)
expect node.get_prop("disabled") to_equal "true"
```

</details>

#### works on checkbox widget

1. var node = checkbox
2. node = with disabled
3. expect node get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = checkbox("wm_dis_cb_1", "Accept", false)
node = with_disabled(node)
expect node.get_prop("disabled") to_equal "true"
```

</details>

### with_readonly modifier

#### sets readonly prop to true

1. var node = text field
2. node = with readonly
3. expect node get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = text_field("wm_ro_1", "initial", "placeholder")
node = with_readonly(node)
expect node.get_prop("readonly") to_equal "true"
```

</details>

#### works on input widget

1. var node = text input
2. node = with readonly
3. expect node get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = text_input("wm_ro_inp_1", "Read only")
node = with_readonly(node)
expect node.get_prop("readonly") to_equal "true"
```

</details>

### with_error modifier

#### sets error prop to true

1. var node = text input
2. node = with error
3. expect node get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = text_input("wm_err_1", "Email")
node = with_error(node, "Invalid email format")
expect node.get_prop("error") to_equal "true"
```

</details>

#### sets error_message prop

1. var node = text input
2. node = with error
3. expect node get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = text_input("wm_err_msg_1", "Email")
node = with_error(node, "Invalid email format")
expect node.get_prop("error_message") to_equal "Invalid email format"
```

</details>

#### works with empty message

1. var node = text input
2. node = with error
3. expect node get prop
4. expect node get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = text_input("wm_err_empty_1", "Field")
node = with_error(node, "")
expect node.get_prop("error") to_equal "true"
expect node.get_prop("error_message") to_equal ""
```

</details>

### with_validator modifier

#### sets validator pattern

1. var node = text input
2. node = with validator
3. expect node get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = text_input("wm_val_1", "Email")
node = with_validator(node, "^[a-zA-Z0-9+_.-]+@[a-zA-Z0-9.-]+$")
expect node.get_prop("validator") to_equal "^[a-zA-Z0-9+_.-]+@[a-zA-Z0-9.-]+$"
```

</details>

### with_required modifier

#### sets required prop to true

1. var node = text input
2. node = with required
3. expect node get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = text_input("wm_req_1", "Name")
node = with_required(node)
expect node.get_prop("required") to_equal "true"
```

</details>

### with_max_length modifier

#### sets max_length prop

1. var node = text input
2. node = with max length
3. expect node get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = text_input("wm_ml_1", "Username")
node = with_max_length(node, 50)
expect node.get_prop("max_length") to_equal "50"
```

</details>

#### sets max_length to zero

1. var node = text input
2. node = with max length
3. expect node get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = text_input("wm_ml_zero_1", "Code")
node = with_max_length(node, 0)
expect node.get_prop("max_length") to_equal "0"
```

</details>

### with_tooltip_text modifier

#### sets tooltip prop

1. var node = button
2. node = with tooltip text
3. expect node get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var node = button("wm_tt_1", "Help", "help_action")
node = with_tooltip_text(node, "Click for help")
expect node.get_prop("tooltip") to_equal "Click for help"
```

</details>

### Disabled button HTML rendering

#### contains disabled attribute

1. var btn = button
2. btn = with disabled


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var btn = button("wm_html_dis_btn_1", "Submit", "submit")
btn = with_disabled(btn)
val tree = UITree.new(btn)
val state = init_state(tree)
val html = render_html_widget(btn, state)
expect html to_contain "disabled"
```

</details>

#### contains disabled class

1. var btn = button
2. btn = with disabled


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var btn = button("wm_html_dis_cls_1", "Submit", "submit")
btn = with_disabled(btn)
val tree = UITree.new(btn)
val state = init_state(tree)
val html = render_html_widget(btn, state)
expect html to_contain "disabled"
```

</details>

### Error input HTML rendering

#### contains has-error class

1. var inp = text input
2. inp = with error


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var inp = text_input("wm_html_err_inp_1", "Email")
inp = with_error(inp, "Invalid email format")
val tree = UITree.new(inp)
val state = init_state(tree)
val html = render_html_widget(inp, state)
expect html to_contain "has-error"
```

</details>

#### contains error message span

1. var inp = text input
2. inp = with error


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var inp = text_input("wm_html_err_msg_1", "Email")
inp = with_error(inp, "Invalid email format")
val tree = UITree.new(inp)
val state = init_state(tree)
val html = render_html_widget(inp, state)
expect html to_contain "error-message"
expect html to_contain "Invalid email format"
```

</details>

### Readonly textfield HTML rendering

#### contains readonly attribute

1. var tf = text field
2. tf = with readonly


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tf = text_field("wm_html_ro_tf_1", "System ID", "")
tf = with_readonly(tf)
val tree = UITree.new(tf)
val state = init_state(tree)
val html = render_html_widget(tf, state)
expect html to_contain "readonly"
```

</details>

#### contains readonly class

1. var tf = text field
2. tf = with readonly


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tf = text_field("wm_html_ro_cls_1", "System ID", "")
tf = with_readonly(tf)
val tree = UITree.new(tf)
val state = init_state(tree)
val html = render_html_widget(tf, state)
expect html to_contain "readonly"
```

</details>

### Required input HTML rendering

#### contains required attribute

1. var inp = text input
2. inp = with required


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var inp = text_input("wm_html_req_inp_1", "Name")
inp = with_required(inp)
val tree = UITree.new(inp)
val state = init_state(tree)
val html = render_html_widget(inp, state)
expect html to_contain "required"
```

</details>

#### contains required indicator

1. var inp = text input
2. inp = with required


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var inp = text_input("wm_html_req_ind_1", "Name")
inp = with_required(inp)
val tree = UITree.new(inp)
val state = init_state(tree)
val html = render_html_widget(inp, state)
expect html to_contain "required-indicator"
```

</details>

### Modifier chaining

#### applies both disabled and error on button

1. var btn = button
2. btn = with error
3. btn = with disabled
4. expect btn get prop
5. expect btn get prop
6. expect btn get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var btn = button("wm_chain_1", "Submit", "submit")
btn = with_error(btn, "Cannot submit")
btn = with_disabled(btn)
expect btn.get_prop("disabled") to_equal "true"
expect btn.get_prop("error") to_equal "true"
expect btn.get_prop("error_message") to_equal "Cannot submit"
```

</details>

#### applies multiple modifiers on input

1. var inp = text input
2. inp = with required
3. inp = with validator
4. inp = with max length
5. expect inp get prop
6. expect inp get prop
7. expect inp get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var inp = text_input("wm_chain_inp_1", "Email")
inp = with_required(inp)
inp = with_validator(inp, "^.+@.+$")
inp = with_max_length(inp, 100)
expect inp.get_prop("required") to_equal "true"
expect inp.get_prop("validator") to_equal "^.+@.+$"
expect inp.get_prop("max_length") to_equal "100"
```

</details>

### Non-interactive widget modifiers

#### with_disabled on text widget still sets prop

1. var tw = text widget
2. tw = with disabled
3. expect tw get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tw = text_widget("wm_ni_txt_1", "Hello")
tw = with_disabled(tw)
expect tw.get_prop("disabled") to_equal "true"
```

</details>

#### with_tooltip_text on text widget sets prop

1. var tw = text widget
2. tw = with tooltip text
3. expect tw get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tw = text_widget("wm_ni_tt_1", "Info")
tw = with_tooltip_text(tw, "Some info tooltip")
expect tw.get_prop("tooltip") to_equal "Some info tooltip"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/widget_modifiers_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- with_disabled modifier
- with_readonly modifier
- with_error modifier
- with_validator modifier
- with_required modifier
- with_max_length modifier
- with_tooltip_text modifier
- Disabled button HTML rendering
- Error input HTML rendering
- Readonly textfield HTML rendering
- Required input HTML rendering
- Modifier chaining
- Non-interactive widget modifiers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
