# Widget Coverage Specification

> Tests covering Widget Coverage.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Widget Coverage Specification

## Scenarios

### Widget Coverage

#### parses the kitchen sink demo without error

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses the kitchen sink demo without error


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses the kitchen sink demo without error")
match result:
    case Ok(h):
        expect h.len() > 0 to_equal true
    case Err(e):
        expect e to_equal ""
```

</details>

#### contains panel widget

- contains panel widget


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("contains panel widget")
expect html to_contain "widget panel"
```

</details>

#### contains text widget with content

- contains text widget with content


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("contains text widget with content")
expect html to_contain "Kitchen Sink Demo"
```

</details>

#### contains button widget

- contains button widget


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("contains button widget")
expect html to_contain "id=\"action_btn\""
```

</details>

#### contains checkbox widget

- contains checkbox widget


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("contains checkbox widget")
expect html to_contain "id=\"option_a\""
```

</details>

#### contains input widget

- contains input widget


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("contains input widget")
expect html to_contain "id=\"search_input\""
```

</details>

#### contains textfield widget

- contains textfield widget


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("contains textfield widget")
expect html to_contain "id=\"edit_field\""
```

</details>

#### contains textarea widget

- contains textarea widget


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("contains textarea widget")
expect html to_contain "id=\"notes_area\""
```

</details>

#### contains dropdown widget

- contains dropdown widget


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("contains dropdown widget")
expect html to_contain "id=\"mode_dropdown\""
```

</details>

#### contains list widget

- contains list widget


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("contains list widget")
expect html to_contain "class=\"list\""
```

</details>

#### contains table widget

- contains table widget


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("contains table widget")
expect html to_contain "id=\"data_table\""
```

</details>

#### contains tree widget

- contains tree widget


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("contains tree widget")
expect html to_contain "id=\"file_tree\""
```

</details>

#### contains treenode widget

- contains treenode widget


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("contains treenode widget")
expect html to_contain "id=\"d_src\""
```

</details>

#### contains tabs widget

- contains tabs widget


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("contains tabs widget")
expect html to_contain "id=\"nav_tabs\""
```

</details>

#### contains menubar widget

- contains menubar widget


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("contains menubar widget")
expect html to_contain "menubar"
```

</details>

#### contains statusbar widget

- contains statusbar widget


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("contains statusbar widget")
expect html to_contain "statusbar"
```

</details>

#### contains progress widget

- contains progress widget


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("contains progress widget")
expect html to_contain "class=\"progress\""
```

</details>

#### contains image widget

- contains image widget


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("contains image widget")
expect html to_contain "id=\"app_icon\""
```

</details>

#### contains divider widget

- contains divider widget


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("contains divider widget")
expect html to_contain "id=\"sidebar_divider\""
```

</details>

#### contains tooltip widget

- contains tooltip widget


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("contains tooltip widget")
expect html to_contain "id=\"search_tip\""
```

</details>

#### contains dialog widget

- contains dialog widget


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("contains dialog widget")
expect html to_contain "id=\"modal_dialog\""
```

</details>

#### contains scroll widget

- contains scroll widget


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("contains scroll widget")
expect html to_contain "id=\"scroll_area\""
```

</details>

#### has all 21 widget types present

- has all 21 widget types present


<details>
<summary>Executable SSpec</summary>

Runnable source: 56 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has all 21 widget types present")
# Verify key structural markers from each category are present
# Panels
val has_panel = html.contains("widget panel")
# Text content
val has_text = html.contains("Kitchen Sink Demo")
# Interactive controls
val has_button = html.contains("id=\"action_btn\"")
val has_checkbox = html.contains("id=\"option_a\"")
val has_input = html.contains("id=\"search_input\"")
val has_textfield = html.contains("id=\"edit_field\"")
val has_textarea = html.contains("id=\"notes_area\"")
val has_dropdown = html.contains("id=\"mode_dropdown\"")
# Collections
val has_list = html.contains("class=\"list\"")
val has_table = html.contains("id=\"data_table\"")
val has_tree = html.contains("id=\"file_tree\"")
val has_treenode = html.contains("id=\"d_src\"")
# Navigation
val has_tabs = html.contains("id=\"nav_tabs\"")
val has_menubar = html.contains("menubar")
val has_statusbar = html.contains("statusbar")
# Display
val has_progress = html.contains("class=\"progress\"")
val has_image = html.contains("id=\"app_icon\"")
val has_divider = html.contains("id=\"sidebar_divider\"")
val has_tooltip = html.contains("id=\"search_tip\"")
# Overlay / Container
val has_dialog = html.contains("id=\"modal_dialog\"")
val has_scroll = html.contains("id=\"scroll_area\"")

var count = 0
if has_panel: count = count + 1
if has_text: count = count + 1
if has_button: count = count + 1
if has_checkbox: count = count + 1
if has_input: count = count + 1
if has_textfield: count = count + 1
if has_textarea: count = count + 1
if has_dropdown: count = count + 1
if has_list: count = count + 1
if has_table: count = count + 1
if has_tree: count = count + 1
if has_treenode: count = count + 1
if has_tabs: count = count + 1
if has_menubar: count = count + 1
if has_statusbar: count = count + 1
if has_progress: count = count + 1
if has_image: count = count + 1
if has_divider: count = count + 1
if has_tooltip: count = count + 1
if has_dialog: count = count + 1
if has_scroll: count = count + 1

expect count to_equal 21
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/ui/widget_coverage_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Widget Coverage.
- Widget Coverage

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6caa0ef6f82ebbd7e8993c8e540babb27fb8b1eb920f11f2bbb07e786c3a454f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6caa0ef6f82ebbd7e8993c8e540babb27fb8b1eb920f11f2bbb07e786c3a454f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6caa0ef6f82ebbd7e8993c8e540babb27fb8b1eb920f11f2bbb07e786c3a454f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/gui/ui/widget_coverage_spec.spl
mirror: doc/06_spec/03_system/gui/ui/widget_coverage_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/ui/widget_coverage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/ui/widget_coverage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/ui/widget_coverage_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses the kitchen sink demo without error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/ui/widget_coverage_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'contains panel widget' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/ui/widget_coverage_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'contains text widget with content' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
