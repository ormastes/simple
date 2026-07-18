# Windows Compat Specification

> <details>

<!-- sdn-diagram:id=windows_compat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=windows_compat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

windows_compat_spec -> std
windows_compat_spec -> common
windows_compat_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=windows_compat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 34 | 34 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Windows Compat Specification

## Scenarios

### platform detection

#### rt_platform_name returns a known platform

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val platform = rt_platform_name()
val known = platform == "windows" or platform == "macos" or platform == "linux" or platform == "unix"
expect(known).to_equal(true)
```

</details>

#### rt_platform_name returns non-empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val platform = rt_platform_name()
expect(platform.len() > 0).to_equal(true)
```

</details>

#### rt_platform_name is consistent across calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p1 = rt_platform_name()
val p2 = rt_platform_name()
expect(p1).to_equal(p2)
```

</details>

### GUI backend detection

#### detect_gui_backend returns a valid backend name

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = detect_gui_backend()
val valid = (backend == "tauri" or backend == "electron"
    or backend == "web" or backend == "tui" or backend == "headless")
expect(valid).to_equal(true)
```

</details>

#### detect_gui_backend returns non-empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = detect_gui_backend()
expect(backend.len() > 0).to_equal(true)
```

</details>

#### detect_gui_backend is deterministic

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b1 = detect_gui_backend()
val b2 = detect_gui_backend()
expect(b1).to_equal(b2)
```

</details>

### terminal size

#### get_terminal_size returns positive width

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val size = get_terminal_size()
expect(size.0 > 0).to_equal(true)
```

</details>

#### get_terminal_size returns positive height

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val size = get_terminal_size()
expect(size.1 > 0).to_equal(true)
```

</details>

#### get_terminal_size returns reasonable width

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val size = get_terminal_size()
expect(size.0 >= 20).to_equal(true)
expect(size.0 <= 1000).to_equal(true)
```

</details>

#### get_terminal_size returns reasonable height

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val size = get_terminal_size()
expect(size.1 >= 5).to_equal(true)
expect(size.1 <= 500).to_equal(true)
```

</details>

### ANSI escape sequences

#### ansi_clear_screen contains ESC[2J

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ansi_clear_screen()
expect(result).to_contain("[2J")
```

</details>

#### ansi_cursor_home contains ESC[H

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ansi_cursor_home()
expect(result).to_contain("[H")
```

</details>

#### ansi_hide_cursor contains ESC[?25l

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ansi_hide_cursor()
expect(result).to_contain("[?25l")
```

</details>

#### ansi_show_cursor contains ESC[?25h

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ansi_show_cursor()
expect(result).to_contain("[?25h")
```

</details>

#### ansi_enable_alt_screen contains ESC[?1049h

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ansi_enable_alt_screen()
expect(result).to_contain("[?1049h")
```

</details>

#### ansi_disable_alt_screen contains ESC[?1049l

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ansi_disable_alt_screen()
expect(result).to_contain("[?1049l")
```

</details>

### Screen buffer on all platforms

#### creates screen with correct dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Screen.new(80, 24)
expect(s.width).to_equal(80)
expect(s.height).to_equal(24)
```

</details>

#### creates small screen

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Screen.new(10, 5)
expect(s.width).to_equal(10)
expect(s.height).to_equal(5)
```

</details>

#### put_text does not crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Screen.new(40, 10)
val s2 = s.put_text(0, 0, "Hello")
expect(s2.width).to_equal(40)
```

</details>

#### put_text at various positions

1. var s = Screen new
2. s = s put text
3. s = s put text
4. s = s put text
   - Expected: s.width equals `40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = Screen.new(40, 10)
s = s.put_text(0, 0, "A")
s = s.put_text(5, 10, "B")
s = s.put_text(9, 39, "C")
expect(s.width).to_equal(40)
```

</details>

#### put_text ignores out of bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Screen.new(20, 5)
val s2 = s.put_text(-1, 0, "X")
val s3 = s.put_text(0, -1, "X")
val s4 = s.put_text(100, 0, "X")
expect(s2.height).to_equal(5)
expect(s3.height).to_equal(5)
expect(s4.height).to_equal(5)
```

</details>

#### render produces non-empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Screen.new(20, 5)
val output = s.render()
expect(output.len() > 0).to_equal(true)
```

</details>

#### clear returns fresh screen

1. var s = Screen new
2. s = s put text
   - Expected: cleared.width equals `20`
   - Expected: cleared.height equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = Screen.new(20, 5)
s = s.put_text(0, 0, "Hello")
val cleared = s.clear()
expect(cleared.width).to_equal(20)
expect(cleared.height).to_equal(5)
```

</details>

#### fill_row fills entire row

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Screen.new(20, 5)
val s2 = s.fill_row(0, "#")
expect(s2.width).to_equal(20)
```

</details>

#### draw_box produces valid screen

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Screen.new(40, 10)
val s2 = s.draw_box(0, 0, 20, 5, "Title")
expect(s2.width).to_equal(40)
```

</details>

### widget tree platform independence

#### builds tree successfully

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = column("root", [text_widget("w1", "Hello")])
val tree = build_tree(root)
expect(tree.root_id).to_equal("root")
```

</details>

#### builds tree with title

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = column("root", [text_widget("w1", "Hello")])
val tree = build_tree_with_title(root, "My App")
expect(tree.title_text()).to_equal("My App")
```

</details>

#### initializes state from tree

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = column("root", [text_widget("w1", "Hello")])
val tree = build_tree(root)
val state = init_state(tree)
expect(state.mode_name()).to_equal("NORMAL")
```

</details>

#### state has correct initial focus

1. text widget
2. text widget
   - Expected: state.focused_id equals `root`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = column("root", [
    text_widget("w1", "First"),
    text_widget("w2", "Second")
])
val tree = build_tree(root)
val state = init_state(tree)
expect(state.focused_id).to_equal("root")
```

</details>

#### FocusNext changes focused widget

1. text widget
2. text widget
   - Expected: new_state.focused_id != state.focused_id is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = column("root", [
    text_widget("w1", "First"),
    text_widget("w2", "Second")
])
val tree = build_tree(root)
val state = init_state(tree)
val new_state = update_state(state, UIEvent.FocusNext)
expect(new_state.focused_id != state.focused_id).to_equal(true)
```

</details>

#### CommandMode changes mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = column("root", [text_widget("w1", "Hello")])
val tree = build_tree(root)
val state = init_state(tree)
val new_state = update_state(state, UIEvent.CommandMode)
expect(new_state.mode_name()).to_equal("COMMAND")
```

</details>

#### update_tree replaces tree but preserves mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root1 = column("root1", [text_widget("w1", "First")])
val tree1 = build_tree(root1)
val state1 = init_state(tree1)

val root2 = column("root2", [text_widget("w2", "Second")])
val tree2 = build_tree(root2)
val state2 = update_tree(state1, tree2)
expect(state2.tree.root_id).to_equal("root2")
expect(state2.mode_name()).to_equal("NORMAL")
```

</details>

#### finds widgets in tree

1. text widget
2. text widget
   - Expected: found != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = column("root", [
    text_widget("w1", "First"),
    text_widget("w2", "Second")
])
val tree = build_tree(root)
val found = tree.find_widget("w1")
expect(found != nil).to_equal(true)
```

</details>

#### all_widget_ids returns complete list

1. text widget
2. text widget
   - Expected: ids.len() >= 3 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = column("root", [
    text_widget("w1", "First"),
    text_widget("w2", "Second")
])
val tree = build_tree(root)
val ids = tree.all_widget_ids()
expect(ids.len() >= 3).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/windows_compat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- platform detection
- GUI backend detection
- terminal size
- ANSI escape sequences
- Screen buffer on all platforms
- widget tree platform independence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 34 |
| Active scenarios | 34 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
