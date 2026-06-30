# Dock Specification

> <details>

<!-- sdn-diagram:id=dock_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dock_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dock_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dock_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 34 | 34 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dock Specification

## Scenarios

### Dock

#### creates with screen dimensions

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dock = _make_test_dock()
expect(dock.screen_width).to_equal(1024)
expect(dock.screen_height).to_equal(768)
assert_true(dock.visible)
```

</details>

#### starts with selected_index at 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dock = _make_test_dock()
expect(dock.selected_index).to_equal(0)
```

</details>

#### has auto_hide enabled

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dock = _make_test_dock()
assert_true(dock.auto_hide)
```

</details>

#### has 5 default items

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dock = _make_test_dock()
expect(dock.items.len()).to_equal(5)
```

</details>

### DockItem defaults

#### first item is Terminal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dock = _make_test_dock()
expect(dock.items[0].app_name).to_equal("Terminal")
expect(dock.items[0].icon_char).to_equal(">")
```

</details>

#### all items are pinned

- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dock = _make_test_dock()
assert_true(dock.items[0].is_pinned)
assert_true(dock.items[4].is_pinned)
```

</details>

#### no items are running

- assert false
   - Expected: dock.items[0].window_id equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dock = _make_test_dock()
assert_false(dock.items[0].is_running)
expect(dock.items[0].window_id).to_equal(-1)
```

</details>

### Dock add_pinned

#### adds a pinned item

- var dock =  make test dock
- dock add pinned
   - Expected: dock.items.len() equals `before + 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dock = _make_test_dock()
val before = dock.items.len()
dock.add_pinned("Browser", "B")
expect(dock.items.len()).to_equal(before + 1)
```

</details>

#### new pinned item is not running

- var dock =  make test dock
- dock add pinned
- assert true
- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dock = _make_test_dock()
dock.add_pinned("Browser", "B")
val last = dock.items[dock.items.len() - 1]
assert_true(last.is_pinned)
assert_false(last.is_running)
```

</details>

### Dock add_running

#### marks existing pinned item as running

- var dock =  make test dock
- dock add running
- assert true
   - Expected: dock.items[0].window_id equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dock = _make_test_dock()
dock.add_running("Terminal", ">", 42)
assert_true(dock.items[0].is_running)
expect(dock.items[0].window_id).to_equal(42)
```

</details>

#### adds new unpinned running item

- var dock =  make test dock
- dock add running
   - Expected: dock.items.len() equals `before + 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dock = _make_test_dock()
val before = dock.items.len()
dock.add_running("Browser", "B", 99)
expect(dock.items.len()).to_equal(before + 1)
```

</details>

### Dock remove_running

#### marks pinned item as not running

- var dock =  make test dock
- dock add running
- dock remove running
- assert false
   - Expected: dock.items[0].window_id equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dock = _make_test_dock()
dock.add_running("Terminal", ">", 42)
dock.remove_running(42)
assert_false(dock.items[0].is_running)
expect(dock.items[0].window_id).to_equal(-1)
```

</details>

#### removes unpinned running item entirely

- var dock =  make test dock
- dock add running
   - Expected: dock.items.len() equals `before + 1`
- dock remove running
   - Expected: dock.items.len() equals `before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dock = _make_test_dock()
val before = dock.items.len()
dock.add_running("Browser", "B", 99)
expect(dock.items.len()).to_equal(before + 1)
dock.remove_running(99)
expect(dock.items.len()).to_equal(before)
```

</details>

### Dock selection

#### select_next advances index

- var dock =  make test dock
   - Expected: dock.selected_index equals `0`
- dock select next
   - Expected: dock.selected_index equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dock = _make_test_dock()
expect(dock.selected_index).to_equal(0)
dock.select_next()
expect(dock.selected_index).to_equal(1)
```

</details>

#### select_next wraps around

- var dock =  make test dock
- dock select next
   - Expected: dock.selected_index equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dock = _make_test_dock()
var i: i64 = 0
while i < dock.items.len():
    dock.select_next()
    i = i + 1
expect(dock.selected_index).to_equal(0)
```

</details>

#### select_prev wraps to end

- var dock =  make test dock
- dock select prev
   - Expected: dock.selected_index equals `dock.items.len() - 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dock = _make_test_dock()
dock.select_prev()
expect(dock.selected_index).to_equal(dock.items.len() - 1)
```

</details>

#### get_selected returns current item

- var dock =  make test dock
   - Expected: selected.app_name equals `Terminal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dock = _make_test_dock()
val selected = dock.get_selected()
expect(selected.app_name).to_equal("Terminal")
```

</details>

### Dock visibility

#### show makes visible

- var dock =  make test dock
- dock hide
- assert false
- dock show
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dock = _make_test_dock()
dock.hide()
assert_false(dock.visible)
dock.show()
assert_true(dock.visible)
```

</details>

#### hide makes invisible

- var dock =  make test dock
- dock hide
- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dock = _make_test_dock()
dock.hide()
assert_false(dock.visible)
```

</details>

#### toggle flips visibility

- var dock =  make test dock
- assert true
- dock toggle
- assert false
- dock toggle
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dock = _make_test_dock()
assert_true(dock.visible)
dock.toggle()
assert_false(dock.visible)
dock.toggle()
assert_true(dock.visible)
```

</details>

### AppSwitcher

#### creates hidden

- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val switcher = _make_test_switcher()
assert_false(switcher.is_visible())
```

</details>

#### show displays cards

- var switcher =  make test switcher
- switcher show
- assert true
   - Expected: switcher.cards.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var switcher = _make_test_switcher()
switcher.show([1, 2, 3], ["A", "B", "C"])
assert_true(switcher.is_visible())
expect(switcher.cards.len()).to_equal(3)
```

</details>

#### select_next advances

- var switcher =  make test switcher
- switcher show
   - Expected: switcher.selected_index equals `0`
- switcher select next
   - Expected: switcher.selected_index equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var switcher = _make_test_switcher()
switcher.show([1, 2], ["A", "B"])
expect(switcher.selected_index).to_equal(0)
switcher.select_next()
expect(switcher.selected_index).to_equal(1)
```

</details>

#### get_selected_window_id returns correct id

- var switcher =  make test switcher
- switcher show
   - Expected: switcher.get_selected_window_id() equals `10`
- switcher select next
   - Expected: switcher.get_selected_window_id() equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var switcher = _make_test_switcher()
switcher.show([10, 20, 30], ["A", "B", "C"])
expect(switcher.get_selected_window_id()).to_equal(10)
switcher.select_next()
expect(switcher.get_selected_window_id()).to_equal(20)
```

</details>

#### returns -1 when empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val switcher = _make_test_switcher()
expect(switcher.get_selected_window_id()).to_equal(-1)
```

</details>

#### hide clears cards

- var switcher =  make test switcher
- switcher show
- switcher hide
- assert false
   - Expected: switcher.cards.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var switcher = _make_test_switcher()
switcher.show([1, 2], ["A", "B"])
switcher.hide()
assert_false(switcher.is_visible())
expect(switcher.cards.len()).to_equal(0)
```

</details>

#### close_selected removes card

- var switcher =  make test switcher
- switcher show
   - Expected: closed equals `10`
   - Expected: switcher.cards.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var switcher = _make_test_switcher()
switcher.show([10, 20, 30], ["A", "B", "C"])
val closed = switcher.close_selected()
expect(closed).to_equal(10)
expect(switcher.cards.len()).to_equal(2)
```

</details>

### NotificationCenter

#### creates empty and hidden

- assert false
   - Expected: nc.notifications.len() equals `0`
   - Expected: nc.unread_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nc = _make_test_nc()
assert_false(nc.is_visible())
expect(nc.notifications.len()).to_equal(0)
expect(nc.unread_count()).to_equal(0)
```

</details>

#### push adds notification

- var nc =  make test nc
- nc push
   - Expected: nc.notifications.len() equals `1`
   - Expected: nc.unread_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var nc = _make_test_nc()
nc.push("Title1", "Body1", "Terminal")
expect(nc.notifications.len()).to_equal(1)
expect(nc.unread_count()).to_equal(1)
```

</details>

#### push adds newest first

- var nc =  make test nc
- nc push
- nc push
   - Expected: nc.notifications[0].title equals `Second`
   - Expected: nc.notifications[1].title equals `First`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var nc = _make_test_nc()
nc.push("First", "Body1", "App1")
nc.push("Second", "Body2", "App2")
expect(nc.notifications[0].title).to_equal("Second")
expect(nc.notifications[1].title).to_equal("First")
```

</details>

#### dismiss removes by id

- var nc =  make test nc
- nc push
- nc push
- nc dismiss
   - Expected: nc.notifications.len() equals `1`
   - Expected: nc.notifications[0].title equals `Title2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var nc = _make_test_nc()
nc.push("Title1", "Body1", "App1")
nc.push("Title2", "Body2", "App2")
val first_id = nc.notifications[1].id
nc.dismiss(first_id)
expect(nc.notifications.len()).to_equal(1)
expect(nc.notifications[0].title).to_equal("Title2")
```

</details>

#### clear_all removes everything

- var nc =  make test nc
- nc push
- nc push
- nc push
   - Expected: nc.notifications.len() equals `3`
- nc clear all
   - Expected: nc.notifications.len() equals `0`
   - Expected: nc.unread_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var nc = _make_test_nc()
nc.push("A", "a", "App")
nc.push("B", "b", "App")
nc.push("C", "c", "App")
expect(nc.notifications.len()).to_equal(3)
nc.clear_all()
expect(nc.notifications.len()).to_equal(0)
expect(nc.unread_count()).to_equal(0)
```

</details>

#### unread_count tracks unread

- var nc =  make test nc
- nc push
- nc push
   - Expected: nc.unread_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var nc = _make_test_nc()
nc.push("A", "a", "App")
nc.push("B", "b", "App")
expect(nc.unread_count()).to_equal(2)
```

</details>

#### toggle flips visibility

- var nc =  make test nc
- nc toggle
- assert true
- nc toggle
- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var nc = _make_test_nc()
nc.toggle()
assert_true(nc.is_visible())
nc.toggle()
assert_false(nc.is_visible())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/desktop/dock_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Dock
- DockItem defaults
- Dock add_pinned
- Dock add_running
- Dock remove_running
- Dock selection
- Dock visibility
- AppSwitcher
- NotificationCenter

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 34 |
| Active scenarios | 34 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
