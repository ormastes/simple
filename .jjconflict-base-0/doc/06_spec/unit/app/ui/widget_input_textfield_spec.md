# Widget Input Textfield Specification

> Tests covering Input widget, TextField widget.

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

- creates a widget with kind input


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a widget with kind input")
val w = text_input("inp_create_1", "Type here...")
expect w.kind to_equal "input"
```

</details>

#### assigns the correct id

- assigns the correct id


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns the correct id")
val w = text_input("inp_create_2", "Search...")
expect w.id to_equal "inp_create_2"
```

</details>

#### is visible by default

- is visible by default


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is visible by default")
val w = text_input("inp_visible_1", "Prompt")
expect w.visible to_equal true
```

</details>

#### is not focused by default

- is not focused by default


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is not focused by default")
val w = text_input("inp_focus_1", "Prompt")
expect w.focused to_equal false
```

</details>

#### placeholder property

#### stores the placeholder text

- stores the placeholder text


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores the placeholder text")
val w = text_input("inp_ph_1", "Type here...")
expect w.get_prop("placeholder") to_equal "Type here..."
```

</details>

#### stores an empty placeholder

- stores an empty placeholder


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores an empty placeholder")
val w = text_input("inp_ph_2", "")
expect w.get_prop("placeholder") to_equal ""
```

</details>

#### stores a long placeholder string

- stores a long placeholder string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores a long placeholder string")
val w = text_input("inp_ph_3", "Enter your full name and email address")
expect w.get_prop("placeholder") to_equal "Enter your full name and email address"
```

</details>

#### children

#### has no children

- has no children


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has no children")
val w = text_input("inp_child_1", "Search...")
expect w.child_count() to_equal 0
```

</details>

#### property inspection

#### reports placeholder via has_prop

- reports placeholder via has_prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports placeholder via has_prop")
val w = text_input("inp_hasprop_1", "Hint text")
expect w.has_prop("placeholder") to_equal true
```

</details>

#### reports false for absent properties

- reports false for absent properties


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports false for absent properties")
val w = text_input("inp_hasprop_2", "Hint text")
expect w.has_prop("value") to_equal false
```

</details>

#### lists placeholder in prop_keys

- lists placeholder in prop_keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists placeholder in prop_keys")
val w = text_input("inp_keys_1", "Hint")
val keys = w.prop_keys()
expect keys.contains("placeholder") to_equal true
```

</details>

#### HTML rendering

#### contains widget-input class

- contains widget-input class


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains widget-input class")
val w = text_input("inp_html_1", "Search...")
val state = make_state_unfocused(w)
val html = render_html_widget(w, state)
expect html to_contain "widget-input"
```

</details>

#### contains placeholder attribute

- contains placeholder attribute


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains placeholder attribute")
val w = text_input("inp_html_2", "Type here...")
val state = make_state_unfocused(w)
val html = render_html_widget(w, state)
expect html to_contain "placeholder"
```

</details>

#### contains the placeholder value

- contains the placeholder value


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains the placeholder value")
val w = text_input("inp_html_3", "Search files...")
val state = make_state_unfocused(w)
val html = render_html_widget(w, state)
expect html to_contain "Search files..."
```

</details>

#### contains the widget id

- contains the widget id


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains the widget id")
val w = text_input("inp_html_4", "Prompt")
val state = make_state_unfocused(w)
val html = render_html_widget(w, state)
expect html to_contain "inp_html_4"
```

</details>

#### renders as a self-closing input tag

- renders as a self-closing input tag


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders as a self-closing input tag")
val w = text_input("inp_html_5", "Go")
val state = make_state_unfocused(w)
val html = render_html_widget(w, state)
expect html to_contain "/>"
```

</details>

#### contains focused class when focused

- contains focused class when focused


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains focused class when focused")
val w = text_input("inp_html_focus_1", "Enter query")
val state = make_state_focused(w)
val html = render_html_widget(w, state)
expect html to_contain "focused"
```

</details>

#### does not contain focused class when unfocused

- does not contain focused class when unfocused


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not contain focused class when unfocused")
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

- creates a widget with kind textfield


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a widget with kind textfield")
val w = text_field("tf_create_1", "hello", "Enter text")
expect w.kind to_equal "textfield"
```

</details>

#### assigns the correct id

- assigns the correct id


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns the correct id")
val w = text_field("tf_create_2", "data", "Hint")
expect w.id to_equal "tf_create_2"
```

</details>

#### is visible by default

- is visible by default


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is visible by default")
val w = text_field("tf_visible_1", "v", "p")
expect w.visible to_equal true
```

</details>

#### is not focused by default

- is not focused by default


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is not focused by default")
val w = text_field("tf_focus_1", "v", "p")
expect w.focused to_equal false
```

</details>

#### value property

#### stores the value

- stores the value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores the value")
val w = text_field("tf_val_1", "hello", "Enter text")
expect w.get_prop("value") to_equal "hello"
```

</details>

#### stores an empty value

- stores an empty value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores an empty value")
val w = text_field("tf_val_2", "", "Hint")
expect w.get_prop("value") to_equal ""
```

</details>

#### stores a long value string

- stores a long value string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores a long value string")
val w = text_field("tf_val_3", "The quick brown fox jumps over the lazy dog", "Type")
expect w.get_prop("value") to_equal "The quick brown fox jumps over the lazy dog"
```

</details>

#### placeholder property

#### stores the placeholder text

- stores the placeholder text


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores the placeholder text")
val w = text_field("tf_ph_1", "hello", "Enter text")
expect w.get_prop("placeholder") to_equal "Enter text"
```

</details>

#### stores an empty placeholder

- stores an empty placeholder


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores an empty placeholder")
val w = text_field("tf_ph_2", "val", "")
expect w.get_prop("placeholder") to_equal ""
```

</details>

#### both properties empty

#### stores both as empty strings

- stores both as empty strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores both as empty strings")
val w = text_field("tf_both_1", "", "")
expect w.get_prop("value") to_equal ""
expect w.get_prop("placeholder") to_equal ""
```

</details>

#### property inspection

#### reports value via has_prop

- reports value via has_prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports value via has_prop")
val w = text_field("tf_hasprop_1", "data", "Hint")
expect w.has_prop("value") to_equal true
```

</details>

#### reports placeholder via has_prop

- reports placeholder via has_prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports placeholder via has_prop")
val w = text_field("tf_hasprop_2", "data", "Hint")
expect w.has_prop("placeholder") to_equal true
```

</details>

#### reports false for absent properties

- reports false for absent properties


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports false for absent properties")
val w = text_field("tf_hasprop_3", "data", "Hint")
expect w.has_prop("action") to_equal false
```

</details>

#### lists both value and placeholder in prop_keys

- lists both value and placeholder in prop_keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists both value and placeholder in prop_keys")
val w = text_field("tf_keys_1", "x", "y")
val keys = w.prop_keys()
expect keys.contains("value") to_equal true
expect keys.contains("placeholder") to_equal true
```

</details>

#### children

#### has no children

- has no children


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has no children")
val w = text_field("tf_child_1", "v", "p")
expect w.child_count() to_equal 0
```

</details>

#### HTML rendering

#### contains widget-textfield class

- contains widget-textfield class


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains widget-textfield class")
val w = text_field("tf_html_1", "hello", "Enter text")
val state = make_state_unfocused(w)
val html = render_html_widget(w, state)
expect html to_contain "widget-textfield"
```

</details>

#### contains type text attribute

- contains type text attribute


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains type text attribute")
val w = text_field("tf_html_2", "hello", "Enter text")
val state = make_state_unfocused(w)
val html = render_html_widget(w, state)
expect html to_contain "type=\"text\""
```

</details>

#### contains the value in the value attribute

- contains the value in the value attribute


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains the value in the value attribute")
val w = text_field("tf_html_3", "my_value", "Hint")
val state = make_state_unfocused(w)
val html = render_html_widget(w, state)
expect html to_contain "my_value"
```

</details>

#### contains the placeholder attribute

- contains the placeholder attribute


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains the placeholder attribute")
val w = text_field("tf_html_4", "v", "Enter name")
val state = make_state_unfocused(w)
val html = render_html_widget(w, state)
expect html to_contain "placeholder"
```

</details>

#### contains the placeholder value text

- contains the placeholder value text


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains the placeholder value text")
val w = text_field("tf_html_5", "v", "Enter name")
val state = make_state_unfocused(w)
val html = render_html_widget(w, state)
expect html to_contain "Enter name"
```

</details>

#### contains the widget id

- contains the widget id


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains the widget id")
val w = text_field("tf_html_6", "v", "p")
val state = make_state_unfocused(w)
val html = render_html_widget(w, state)
expect html to_contain "tf_html_6"
```

</details>

#### renders value attribute with correct format

- renders value attribute with correct format


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders value attribute with correct format")
val w = text_field("tf_html_7", "test_data", "Hint")
val state = make_state_unfocused(w)
val html = render_html_widget(w, state)
expect html to_contain "value=\"test_data\""
```

</details>

#### renders placeholder attribute with correct format

- renders placeholder attribute with correct format


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders placeholder attribute with correct format")
val w = text_field("tf_html_8", "v", "Search here")
val state = make_state_unfocused(w)
val html = render_html_widget(w, state)
expect html to_contain "placeholder=\"Search here\""
```

</details>

#### renders as a self-closing input tag

- renders as a self-closing input tag


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders as a self-closing input tag")
val w = text_field("tf_html_9", "v", "p")
val state = make_state_unfocused(w)
val html = render_html_widget(w, state)
expect html to_contain "/>"
```

</details>

#### contains focused class when focused

- contains focused class when focused


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains focused class when focused")
val w = text_field("tf_html_focus_1", "val", "hint")
val state = make_state_focused(w)
val html = render_html_widget(w, state)
expect html to_contain "focused"
```

</details>

#### does not contain focused class when unfocused

- does not contain focused class when unfocused


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not contain focused class when unfocused")
val w = text_field("tf_html_focus_2", "val", "hint")
val state = make_state_unfocused(w)
val html = render_html_widget(w, state)
val has_focused = html.contains("focused")
expect has_focused to_equal false
```

</details>

#### renders empty value correctly

- renders empty value correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders empty value correctly")
val w = text_field("tf_html_empty_1", "", "Hint")
val state = make_state_unfocused(w)
val html = render_html_widget(w, state)
expect html to_contain "value=\"\""
```

</details>

#### renders empty placeholder correctly

- renders empty placeholder correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders empty placeholder correctly")
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
| Source | `test/unit/app/ui/widget_input_textfield_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Input widget, TextField widget.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3e01547ef770364f6fed8225eb34d02d7d771b5b8616f05b38f0b0b92a3f0d37`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3e01547ef770364f6fed8225eb34d02d7d771b5b8616f05b38f0b0b92a3f0d37`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3e01547ef770364f6fed8225eb34d02d7d771b5b8616f05b38f0b0b92a3f0d37`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui/widget_input_textfield_spec.spl
mirror: doc/06_spec/unit/app/ui/widget_input_textfield_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/widget_input_textfield_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/widget_input_textfield_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/widget_input_textfield_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a widget with kind input' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/widget_input_textfield_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'assigns the correct id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/widget_input_textfield_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is visible by default' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
