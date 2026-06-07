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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dock = _make_test_dock()
expect(dock.screen_width).to_equal(1024)
expect(dock.screen_height).to_equal(768)
expect(dock.visible)
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dock = _make_test_dock()
expect(dock.auto_hide)
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dock = _make_test_dock()
expect(dock.items[0].is_pinned)
expect(dock.items[4].is_pinned)
```

</details>

#### no items are running

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dock = _make_test_dock()
expect(not dock.items[0].is_running)
expect(dock.items[0].window_id).to_equal(-1)
```

</details>

### Dock add_pinned

#### adds a pinned item

1. var dock =  make test dock
2. dock add pinned
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

1. var dock =  make test dock
2. dock add pinned


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dock = _make_test_dock()
dock.add_pinned("Browser", "B")
val last = dock.items[dock.items.len() - 1]
expect(last.is_pinned)
expect(not last.is_running)
```

</details>

### Dock add_running

#### marks existing pinned item as running

1. var dock =  make test dock
2. dock add running
   - Expected: dock.items[0].window_id equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dock = _make_test_dock()
dock.add_running("Terminal", ">", 42)
expect(dock.items[0].is_running)
expect(dock.items[0].window_id).to_equal(42)
```

</details>

#### adds new unpinned running item

1. var dock =  make test dock
2. dock add running
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

1. var dock =  make test dock
2. dock add running
3. dock remove running
   - Expected: dock.items[0].window_id equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dock = _make_test_dock()
dock.add_running("Terminal", ">", 42)
dock.remove_running(42)
expect(not dock.items[0].is_running)
expect(dock.items[0].window_id).to_equal(-1)
```

</details>

#### removes unpinned running item entirely

1. var dock =  make test dock
2. dock add running
   - Expected: dock.items.len() equals `before + 1`
3. dock remove running
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

1. var dock =  make test dock
   - Expected: dock.selected_index equals `0`
2. dock select next
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

1. var dock =  make test dock
2. dock select next
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

1. var dock =  make test dock
2. dock select prev
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

1. var dock =  make test dock
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

1. var dock =  make test dock
2. dock hide
3. dock show


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dock = _make_test_dock()
dock.hide()
expect(not dock.visible)
dock.show()
expect(dock.visible)
```

</details>

#### hide makes invisible

1. var dock =  make test dock
2. dock hide


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dock = _make_test_dock()
dock.hide()
expect(not dock.visible)
```

</details>

#### toggle flips visibility

1. var dock =  make test dock
2. dock toggle
3. dock toggle


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dock = _make_test_dock()
expect(dock.visible)
dock.toggle()
expect(not dock.visible)
dock.toggle()
expect(dock.visible)
```

</details>

### AppSwitcher

#### creates hidden

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val switcher = _make_test_switcher()
expect(not switcher.is_visible())
```

</details>

#### show displays cards

1. var switcher =  make test switcher
2. switcher show
   - Expected: switcher.cards.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var switcher = _make_test_switcher()
switcher.show([1, 2, 3], ["A", "B", "C"])
expect(switcher.is_visible())
expect(switcher.cards.len()).to_equal(3)
```

</details>

#### select_next advances

1. var switcher =  make test switcher
2. switcher show
   - Expected: switcher.selected_index equals `0`
3. switcher select next
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

1. var switcher =  make test switcher
2. switcher show
   - Expected: switcher.get_selected_window_id() equals `10`
3. switcher select next
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

1. var switcher =  make test switcher
2. switcher show
3. switcher hide
   - Expected: switcher.cards.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var switcher = _make_test_switcher()
switcher.show([1, 2], ["A", "B"])
switcher.hide()
expect(not switcher.is_visible())
expect(switcher.cards.len()).to_equal(0)
```

</details>

#### close_selected removes card

1. var switcher =  make test switcher
2. switcher show
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nc = _make_test_nc()
expect(not nc.is_visible())
expect(nc.notifications.len()).to_equal(0)
expect(nc.unread_count()).to_equal(0)
```

</details>

#### push adds notification

1. var nc =  make test nc
2. nc push
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

1. var nc =  make test nc
2. nc push
3. nc push
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

1. var nc =  make test nc
2. nc push
3. nc push
4. nc dismiss
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

1. var nc =  make test nc
2. nc push
3. nc push
4. nc push
   - Expected: nc.notifications.len() equals `3`
5. nc clear all
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

1. var nc =  make test nc
2. nc push
3. nc push
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

1. var nc =  make test nc
2. nc toggle
3. nc toggle


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var nc = _make_test_nc()
nc.toggle()
expect(nc.is_visible())
nc.toggle()
expect(not nc.is_visible())
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
