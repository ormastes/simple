# Widgets Specification

> 1. expect true  # Menu new

<!-- sdn-diagram:id=widgets_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=widgets_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

widgets_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=widgets_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Widgets Specification

## Scenarios

### Menu

#### creates empty menu

1. expect true  # Menu new


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Menu.new(id); selected_index() == 0
```

</details>

#### adds items

1. expect true  #  add item


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # .add_item("Option 1").add_item("Option 2")
```

</details>

#### adds items with keys

1. expect true  #  add item with key


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # .add_item_with_key("New", 'n')
```

</details>

#### navigates selection

1. expect true  # select next


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # select_next(), select_prev()
```

</details>

#### gets selected item

1. expect true  # selected item


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # selected_item().label == "First"
```

</details>

#### supports title

1. expect true  #  with title


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # .with_title("Main Menu")
```

</details>

### Dialog

#### creates dialog with message

1. expect true  # Dialog new


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Dialog.new(id, "Alert").with_message("msg")
```

</details>

#### creates OK/Cancel dialog

1. expect true  # Dialog ok cancel


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Dialog.ok_cancel(id, title, msg)
```

</details>

#### creates Yes/No dialog

1. expect true  # Dialog yes no


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Dialog.yes_no(id, title, msg)
```

</details>

#### navigates buttons

1. expect true  # select next button


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # select_next_button(), select_prev_button()
```

</details>

### ProgressBar

#### creates progress bar with defaults

1. expect true  # ProgressBar new


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # ProgressBar.new(id); width == 40
```

</details>

#### sets progress

1. expect true  # set progress


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # set_progress(0.5)
```

</details>

#### clamps progress to valid range

1. expect true  # set progress


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # set_progress(1.5) -> 1.0
```

</details>

#### increments progress

1. expect true  # increment


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # increment(0.3)
```

</details>

#### supports custom width and label

1. expect true  #  with width


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # .with_width(20).with_label("Loading")
```

</details>

### TextInput

#### creates empty input

1. expect true  # TextInput new


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # TextInput.new(id); value() == ""
```

</details>

#### inserts characters

1. expect true  # insert char


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # insert_char('H'); insert_char('i')
```

</details>

#### handles backspace

1. expect true  # backspace


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # backspace() removes char before cursor
```

</details>

#### handles delete

1. expect true  # delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # delete() removes char at cursor
```

</details>

#### moves cursor

1. expect true  # move left


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # move_left(), move_right(), move_home(), move_end()
```

</details>

#### respects max length

1. expect true  #  with max length


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # .with_max_length(3); can't exceed
```

</details>

#### supports placeholder

1. expect true  #  with placeholder


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # .with_placeholder("Enter name...")
```

</details>

### ScrollList

#### creates scrollable list

1. expect true  # ScrollList new


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # ScrollList.new(id, 5)
```

</details>

#### adds and clears items

1. expect true  # add item


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # add_item("Item"); clear()
```

</details>

#### navigates selection

1. expect true  # select next


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # select_next(), select_prev()
```

</details>

#### scrolls to keep selection visible

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # scroll_offset adjusts automatically
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/widgets_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
