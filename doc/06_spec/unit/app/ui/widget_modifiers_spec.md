# Widget Modifiers Specification

> Tests covering with_disabled modifier, with_readonly modifier, with_error modifier, with_validator modifier, with_required modifier, with_max_length modifier, with_tooltip_text modifier, Disabled button HTML rendering, Error input HTML rendering, Readonly textfield HTML rendering, Required input HTML rendering, Modifier chaining, Non-interactive widget modifiers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Widget Modifiers Specification

## Scenarios

### with_disabled modifier

#### sets disabled prop to true

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- sets disabled prop to true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets disabled prop to true")
var node = button("wm_dis_1", "Save", "save")
node = with_disabled(node)
expect node.get_prop("disabled") to_equal "true"
```

</details>

#### works on input widget

- works on input widget


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("works on input widget")
var node = text_input("wm_dis_inp_1", "Type here")
node = with_disabled(node)
expect node.get_prop("disabled") to_equal "true"
```

</details>

#### works on checkbox widget

- works on checkbox widget


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("works on checkbox widget")
var node = checkbox("wm_dis_cb_1", "Accept", false)
node = with_disabled(node)
expect node.get_prop("disabled") to_equal "true"
```

</details>

### with_readonly modifier

#### sets readonly prop to true

- sets readonly prop to true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets readonly prop to true")
var node = text_field("wm_ro_1", "initial", "placeholder")
node = with_readonly(node)
expect node.get_prop("readonly") to_equal "true"
```

</details>

#### works on input widget

- works on input widget


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("works on input widget")
var node = text_input("wm_ro_inp_1", "Read only")
node = with_readonly(node)
expect node.get_prop("readonly") to_equal "true"
```

</details>

### with_error modifier

#### sets error prop to true

- sets error prop to true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets error prop to true")
var node = text_input("wm_err_1", "Email")
node = with_error(node, "Invalid email format")
expect node.get_prop("error") to_equal "true"
```

</details>

#### sets error_message prop

- sets error_message prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets error_message prop")
var node = text_input("wm_err_msg_1", "Email")
node = with_error(node, "Invalid email format")
expect node.get_prop("error_message") to_equal "Invalid email format"
```

</details>

#### works with empty message

- works with empty message


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("works with empty message")
var node = text_input("wm_err_empty_1", "Field")
node = with_error(node, "")
expect node.get_prop("error") to_equal "true"
expect node.get_prop("error_message") to_equal ""
```

</details>

### with_validator modifier

#### sets validator pattern

- sets validator pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets validator pattern")
var node = text_input("wm_val_1", "Email")
node = with_validator(node, "^[a-zA-Z0-9+_.-]+@[a-zA-Z0-9.-]+$")
expect node.get_prop("validator") to_equal "^[a-zA-Z0-9+_.-]+@[a-zA-Z0-9.-]+$"
```

</details>

### with_required modifier

#### sets required prop to true

- sets required prop to true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets required prop to true")
var node = text_input("wm_req_1", "Name")
node = with_required(node)
expect node.get_prop("required") to_equal "true"
```

</details>

### with_max_length modifier

#### sets max_length prop

- sets max_length prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets max_length prop")
var node = text_input("wm_ml_1", "Username")
node = with_max_length(node, 50)
expect node.get_prop("max_length") to_equal "50"
```

</details>

#### sets max_length to zero

- sets max_length to zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets max_length to zero")
var node = text_input("wm_ml_zero_1", "Code")
node = with_max_length(node, 0)
expect node.get_prop("max_length") to_equal "0"
```

</details>

### with_tooltip_text modifier

#### sets tooltip prop

- sets tooltip prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets tooltip prop")
var node = button("wm_tt_1", "Help", "help_action")
node = with_tooltip_text(node, "Click for help")
expect node.get_prop("tooltip") to_equal "Click for help"
```

</details>

### Disabled button HTML rendering

#### contains disabled attribute

- contains disabled attribute


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains disabled attribute")
var btn = button("wm_html_dis_btn_1", "Submit", "submit")
btn = with_disabled(btn)
val tree = UITree.new(btn)
val state = init_state(tree)
val html = render_html_widget(btn, state)
expect html to_contain "disabled"
```

</details>

#### contains disabled class

- contains disabled class


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains disabled class")
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

- contains has-error class


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains has-error class")
var inp = text_input("wm_html_err_inp_1", "Email")
inp = with_error(inp, "Invalid email format")
val tree = UITree.new(inp)
val state = init_state(tree)
val html = render_html_widget(inp, state)
expect html to_contain "has-error"
```

</details>

#### contains error message span

- contains error message span


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains error message span")
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

- contains readonly attribute


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains readonly attribute")
var tf = text_field("wm_html_ro_tf_1", "System ID", "")
tf = with_readonly(tf)
val tree = UITree.new(tf)
val state = init_state(tree)
val html = render_html_widget(tf, state)
expect html to_contain "readonly"
```

</details>

#### contains readonly class

- contains readonly class


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains readonly class")
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

- contains required attribute


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains required attribute")
var inp = text_input("wm_html_req_inp_1", "Name")
inp = with_required(inp)
val tree = UITree.new(inp)
val state = init_state(tree)
val html = render_html_widget(inp, state)
expect html to_contain "required"
```

</details>

#### contains required indicator

- contains required indicator


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains required indicator")
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

- applies both disabled and error on button


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies both disabled and error on button")
var btn = button("wm_chain_1", "Submit", "submit")
btn = with_error(btn, "Cannot submit")
btn = with_disabled(btn)
expect btn.get_prop("disabled") to_equal "true"
expect btn.get_prop("error") to_equal "true"
expect btn.get_prop("error_message") to_equal "Cannot submit"
```

</details>

#### applies multiple modifiers on input

- applies multiple modifiers on input


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies multiple modifiers on input")
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

- with_disabled on text widget still sets prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("with_disabled on text widget still sets prop")
var tw = text_widget("wm_ni_txt_1", "Hello")
tw = with_disabled(tw)
expect tw.get_prop("disabled") to_equal "true"
```

</details>

#### with_tooltip_text on text widget sets prop

- with_tooltip_text on text widget sets prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("with_tooltip_text on text widget sets prop")
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
| Source | `test/unit/app/ui/widget_modifiers_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering with_disabled modifier, with_readonly modifier, with_error modifier, with_validator modifier, with_required modifier, with_max_length modifier, with_tooltip_text modifier, Disabled button HTML rendering, Error input HTML rendering, Readonly textfield HTML rendering, Required input HTML rendering, Modifier chaining, Non-interactive widget modifiers.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cada6987993ac369eda05cc05313af4568b3a2997269c816d75004e8a1b4306e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cada6987993ac369eda05cc05313af4568b3a2997269c816d75004e8a1b4306e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cada6987993ac369eda05cc05313af4568b3a2997269c816d75004e8a1b4306e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui/widget_modifiers_spec.spl
mirror: doc/06_spec/unit/app/ui/widget_modifiers_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/widget_modifiers_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/widget_modifiers_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/widget_modifiers_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sets disabled prop to true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/widget_modifiers_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'works on input widget' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/widget_modifiers_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'works on checkbox widget' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
