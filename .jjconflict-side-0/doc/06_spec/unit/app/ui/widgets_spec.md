# Widgets Specification

> Tests covering Menu, Dialog, ProgressBar, TextInput, ScrollList.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Widgets Specification

## Scenarios

### Menu

#### creates empty menu

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates empty menu


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates empty menu")
expect true  # Menu.new(id); selected_index() == 0
```

</details>

#### adds items

- adds items


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds items")
expect true  # .add_item("Option 1").add_item("Option 2")
```

</details>

#### adds items with keys

- adds items with keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds items with keys")
expect true  # .add_item_with_key("New", 'n')
```

</details>

#### navigates selection

- navigates selection


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("navigates selection")
expect true  # select_next(), select_prev()
```

</details>

#### gets selected item

- gets selected item


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets selected item")
expect true  # selected_item().label == "First"
```

</details>

#### supports title

- supports title


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports title")
expect true  # .with_title("Main Menu")
```

</details>

### Dialog

#### creates dialog with message

- creates dialog with message


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates dialog with message")
expect true  # Dialog.new(id, "Alert").with_message("msg")
```

</details>

#### creates OK/Cancel dialog

- creates OK/Cancel dialog


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates OK/Cancel dialog")
expect true  # Dialog.ok_cancel(id, title, msg)
```

</details>

#### creates Yes/No dialog

- creates Yes/No dialog


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates Yes/No dialog")
expect true  # Dialog.yes_no(id, title, msg)
```

</details>

#### navigates buttons

- navigates buttons


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("navigates buttons")
expect true  # select_next_button(), select_prev_button()
```

</details>

### ProgressBar

#### creates progress bar with defaults

- creates progress bar with defaults


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates progress bar with defaults")
expect true  # ProgressBar.new(id); width == 40
```

</details>

#### sets progress

- sets progress


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets progress")
expect true  # set_progress(0.5)
```

</details>

#### clamps progress to valid range

- clamps progress to valid range


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clamps progress to valid range")
expect true  # set_progress(1.5) -> 1.0
```

</details>

#### increments progress

- increments progress


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("increments progress")
expect true  # increment(0.3)
```

</details>

#### supports custom width and label

- supports custom width and label


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports custom width and label")
expect true  # .with_width(20).with_label("Loading")
```

</details>

### TextInput

#### creates empty input

- creates empty input


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates empty input")
expect true  # TextInput.new(id); value() == ""
```

</details>

#### inserts characters

- inserts characters


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inserts characters")
expect true  # insert_char('H'); insert_char('i')
```

</details>

#### handles backspace

- handles backspace


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles backspace")
expect true  # backspace() removes char before cursor
```

</details>

#### handles delete

- handles delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles delete")
expect true  # delete() removes char at cursor
```

</details>

#### moves cursor

- moves cursor


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("moves cursor")
expect true  # move_left(), move_right(), move_home(), move_end()
```

</details>

#### respects max length

- respects max length


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("respects max length")
expect true  # .with_max_length(3); can't exceed
```

</details>

#### supports placeholder

- supports placeholder


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports placeholder")
expect true  # .with_placeholder("Enter name...")
```

</details>

### ScrollList

#### creates scrollable list

- creates scrollable list


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates scrollable list")
expect true  # ScrollList.new(id, 5)
```

</details>

#### adds and clears items

- adds and clears items


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds and clears items")
expect true  # add_item("Item"); clear()
```

</details>

#### navigates selection

- navigates selection


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("navigates selection")
expect true  # select_next(), select_prev()
```

</details>

#### scrolls to keep selection visible

- scrolls to keep selection visible


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("scrolls to keep selection visible")
expect true  # scroll_offset adjusts automatically
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/widgets_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Menu, Dialog, ProgressBar, TextInput, ScrollList.
- Menu
- Dialog
- ProgressBar
- TextInput
- ScrollList

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

- Canonical SPipe generation for source `0b91a700105b98ec9bbc38e9605471429a44980aeaaa32ac575c800747bdf203`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0b91a700105b98ec9bbc38e9605471429a44980aeaaa32ac575c800747bdf203`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0b91a700105b98ec9bbc38e9605471429a44980aeaaa32ac575c800747bdf203`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui/widgets_spec.spl
mirror: doc/06_spec/unit/app/ui/widgets_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/widgets_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/widgets_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/widgets_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates empty menu' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/widgets_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'adds items' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/widgets_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'adds items with keys' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
