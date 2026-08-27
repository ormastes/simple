# Html Render Specification

> Tests covering render_html_widget text, render_html_widget button, render_html_widget panel, render_html_widget progress, render_html_widget checkbox, render_html_widget image, render_html_widget divider, render_html_widget focus, render_html_tree.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Html Render Specification

## Scenarios

### render_html_widget text

#### renders div with class widget-text

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- renders div with class widget-text


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders div with class widget-text")
val node = text_widget("txt1", "Hello World")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "widget-text"
```

</details>

#### renders content inside the div

- renders content inside the div


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders content inside the div")
val node = text_widget("txt2", "Some content")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "Some content"
```

</details>

#### renders as a div tag

- renders as a div tag


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders as a div tag")
val node = text_widget("txt3", "Test")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html.starts_with("<div") to_equal true
```

</details>

### render_html_widget button

#### renders button tag with class widget-button

- renders button tag with class widget-button


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders button tag with class widget-button")
val node = button("btn1", "Click Me", "do_click")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "widget-button"
```

</details>

#### renders as a button tag

- renders as a button tag


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders as a button tag")
val node = button("btn2", "OK", "confirm")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html.starts_with("<button") to_equal true
```

</details>

#### includes data-action attribute

- includes data-action attribute


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes data-action attribute")
val node = button("btn3", "Save", "save_file")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "data-action=\"save_file\""
```

</details>

#### includes label text as content

- includes label text as content


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes label text as content")
val node = button("btn4", "Submit", "submit")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "Submit"
```

</details>

### render_html_widget panel

#### renders div with class widget-panel

- renders div with class widget-panel


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders div with class widget-panel")
val node = panel("pnl1", "My Panel", [])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "widget-panel"
```

</details>

#### renders children inside panel

- renders children inside panel


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders children inside panel")
val child = text_widget("pnl_child", "Inner text")
val node = panel("pnl2", "Parent", [child])
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "Inner text"
expect html to_contain "widget-text"
```

</details>

### render_html_widget progress

#### renders div with class widget-progress

- renders div with class widget-progress


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders div with class widget-progress")
val node = progress("prog1", 75)
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "widget-progress"
```

</details>

#### includes percentage in style

- includes percentage in style


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes percentage in style")
val node = progress("prog2", 42)
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "width: 42%"
```

</details>

#### includes percentage text

- includes percentage text


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes percentage text")
val node = progress("prog3", 90)
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "90%"
```

</details>

### render_html_widget checkbox

#### renders label with class widget-checkbox

- renders label with class widget-checkbox


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders label with class widget-checkbox")
val node = checkbox("chk1", "Accept terms", false)
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "widget-checkbox"
```

</details>

#### renders input with type checkbox

- renders input with type checkbox


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders input with type checkbox")
val node = checkbox("chk2", "Enable feature", false)
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "check-box"
```

</details>

#### renders as a div tag

- renders as a div tag


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders as a div tag")
val node = checkbox("chk3", "Option", false)
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html.starts_with("<div") to_equal true
```

</details>

#### includes checked attribute when checked is true

- includes checked attribute when checked is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes checked attribute when checked is true")
val node = checkbox("chk4", "Agree", true)
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain " checked"
```

</details>

#### omits checked attribute when checked is false

- omits checked attribute when checked is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("omits checked attribute when checked is false")
val node = checkbox("chk5", "Disagree", false)
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
# The unchecked checkbox should not have the checked attribute
# The output contains type="checkbox" but NOT an extra " checked" attr
val has_checked_attr = html.contains("checked /")
expect has_checked_attr to_equal false
```

</details>

### render_html_widget image

#### renders img tag with class widget-image

- renders img tag with class widget-image


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders img tag with class widget-image")
val node = image("img1", "logo.png", "Logo")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "widget-image"
```

</details>

#### renders as an img tag

- renders as an img tag


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders as an img tag")
val node = image("img2", "photo.jpg", "Photo")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html.starts_with("<img") to_equal true
```

</details>

#### includes src attribute

- includes src attribute


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes src attribute")
val node = image("img3", "banner.png", "Banner")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "src=\"banner.png\""
```

</details>

#### includes alt attribute

- includes alt attribute


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes alt attribute")
val node = image("img4", "icon.svg", "App Icon")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "alt=\"App Icon\""
```

</details>

### render_html_widget divider

#### renders hr tag with class widget-divider

- renders hr tag with class widget-divider


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders hr tag with class widget-divider")
val node = divider("div1")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html to_contain "widget-divider"
```

</details>

#### renders as an hr tag

- renders as an hr tag


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders as an hr tag")
val node = divider("div2")
val tree = UITree.new(node)
val state = init_state(tree)
val html = render_html_widget(node, state)
expect html.starts_with("<hr") to_equal true
```

</details>

### render_html_widget focus

#### adds focused class when widget is focused

- adds focused class when widget is focused


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds focused class when widget is focused")
val node = text_widget("foc1", "Focused text")
val tree = UITree.new(node)
# init_state sets focused_id to the first widget id (the root)
val state = init_state(tree)
# foc1 is the root so it gets focus
expect state.focused_id to_equal "foc1"
val html = render_html_widget(node, state)
expect html to_contain " focused"
```

</details>

#### does not add focused class when widget is not focused

- does not add focused class when widget is not focused


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not add focused class when widget is not focused")
# Create a tree where the focused widget is NOT the one we render
val root = text_widget("foc_root", "Root")
val other = text_widget("foc_other", "Other")
var parent = panel("foc_parent", "Panel", [root, other])
val tree = UITree.new(parent)
val state = init_state(tree)
# state.focused_id will be "foc_parent" (the tree root)
# Render a non-focused child
val html = render_html_widget(other, state)
val class_segment = "widget-text\""
# The class should be widget-text" without focused
expect html to_contain class_segment
```

</details>

### render_html_tree

#### recursively renders full tree with nested elements

- recursively renders full tree with nested elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recursively renders full tree with nested elements")
val child1 = text_widget("tree_txt", "Hello from tree")
val child2 = button("tree_btn", "Go", "go_action")
val root = panel("tree_root", "Tree Panel", [child1, child2])
val tree = UITree.new(root)
val state = init_state(tree)
val html = render_html_tree(root, state)
expect html to_contain "widget-panel"
expect html to_contain "widget-text"
expect html to_contain "Hello from tree"
expect html to_contain "widget-button"
expect html to_contain "Go"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/html_render_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering render_html_widget text, render_html_widget button, render_html_widget panel, render_html_widget progress, render_html_widget checkbox, render_html_widget image, render_html_widget divider, render_html_widget focus, render_html_tree.
- render_html_widget text
- render_html_widget button
- render_html_widget panel
- render_html_widget progress
- render_html_widget checkbox
- render_html_widget image
- render_html_widget divider
- render_html_widget focus
- render_html_tree

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
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

- Canonical SPipe generation for source `7dc05560e391555f85573ca51bb273f201de97ee18f8c7c2e383b81c70ab11e4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7dc05560e391555f85573ca51bb273f201de97ee18f8c7c2e383b81c70ab11e4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7dc05560e391555f85573ca51bb273f201de97ee18f8c7c2e383b81c70ab11e4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui/html_render_spec.spl
mirror: doc/06_spec/unit/app/ui/html_render_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/html_render_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/html_render_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/html_render_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders div with class widget-text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/html_render_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders content inside the div' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/html_render_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders as a div tag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
