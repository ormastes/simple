# Tui Screen Specification

> <details>

<!-- sdn-diagram:id=tui_screen_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tui_screen_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tui_screen_spec -> app
tui_screen_spec -> common
tui_screen_spec -> nogc_sync_mut
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tui_screen_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tui Screen Specification

## Scenarios

### Screen buffer basics

<details>
<summary>Advanced: creates screen with correct dimensions</summary>

#### creates screen with correct dimensions _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val screen = Screen.new(80, 24)
expect(screen.width).to_equal(80)
expect(screen.height).to_equal(24)
expect(screen.buffer.len()).to_equal(24)
```

</details>


</details>

<details>
<summary>Advanced: put_text writes content at position</summary>

#### put_text writes content at position _(slow)_

1. var screen = Screen new

2. screen = screen put text


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var screen = Screen.new(40, 10)
screen = screen.put_text(0, 0, "Hello")
val line = screen.buffer[0]
expect(line).to_start_with("Hello")
```

</details>


</details>

<details>
<summary>Advanced: draw_box produces box-drawing characters</summary>

#### draw_box produces box-drawing characters _(slow)_

1. var screen = Screen new

2. screen = screen draw box


<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var screen = Screen.new(40, 10)
screen = screen.draw_box(0, 0, 20, 5, "Test")
val rendered = screen.render()
# Box-drawing characters: top-left corner
expect(rendered).to_contain("\u{250c}")
# Horizontal line
expect(rendered).to_contain("\u{2500}")
# Top-right corner
expect(rendered).to_contain("\u{2510}")
# Vertical border
expect(rendered).to_contain("\u{2502}")
# Bottom-left corner
expect(rendered).to_contain("\u{2514}")
# Bottom-right corner
expect(rendered).to_contain("\u{2518}")
```

</details>


</details>

<details>
<summary>Advanced: render produces non-empty output</summary>

#### render produces non-empty output _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val screen = Screen.new(80, 24)
val output = screen.render()
expect(output.len()).to_be_greater_than(0)
```

</details>


</details>

<details>
<summary>Advanced: clear resets the buffer</summary>

#### clear resets the buffer _(slow)_

1. var screen = Screen new

2. screen = screen put text


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var screen = Screen.new(40, 10)
screen = screen.put_text(0, 0, "Some text")
val cleared = screen.clear()
# After clearing, the first line should just be spaces
val line = cleared.buffer[0]
expect(line).to_start_with(" ")
```

</details>


</details>

### Screen with UI tree rendering

<details>
<summary>Advanced: renders minimal.ui.sdn tree to screen buffer</summary>

#### renders minimal.ui.sdn tree to screen buffer _(slow)_

1. Ok

2. var screen = Screen new

3. screen = render tui tree

4. Err
   - Expected: e equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree_result = parse_ui_to_tree("examples/06_io/ui/minimal.ui.sdn")
match tree_result:
    Ok(tree) :
        val state = init_state(tree)
        val rects = compute_layout(state.tree.root, 0, 0, 80, 24)

        var screen = Screen.new(80, 24)
        screen = render_tui_tree(screen, state.tree.root, rects, state)

        val output = screen.render()
        # Output should be non-empty
        expect(output.len()).to_be_greater_than(100)
        # Should contain box-drawing for the panel
        expect(output).to_contain("\u{250c}")
        expect(output).to_contain("\u{2500}")
        expect(output).to_contain("\u{2510}")
    Err(e) :
        expect(e).to_equal("")
```

</details>


</details>

<details>
<summary>Advanced: renders demo.ui.sdn tree with multiple widgets</summary>

#### renders demo.ui.sdn tree with multiple widgets _(slow)_

1. Ok

2. var screen = Screen new

3. screen = render tui tree

4. Err
   - Expected: e equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree_result = parse_ui_to_tree("examples/06_io/ui/demo.ui.sdn")
match tree_result:
    Ok(tree) :
        val state = init_state(tree)
        val rects = compute_layout(state.tree.root, 0, 0, 120, 40)

        var screen = Screen.new(120, 40)
        screen = render_tui_tree(screen, state.tree.root, rects, state)

        val output = screen.render()
        # Output should be substantial for a complex layout
        expect(output.len()).to_be_greater_than(200)
        # Should contain vertical borders from panels
        expect(output).to_contain("\u{2502}")
        # Should contain bottom corners from panels
        expect(output).to_contain("\u{2518}")
    Err(e) :
        expect(e).to_equal("")
```

</details>


</details>

### Screen drawing primitives

<details>
<summary>Advanced: draw_hline produces a horizontal line</summary>

#### draw_hline produces a horizontal line _(slow)_

1. var screen = Screen new

2. screen = screen draw hline


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var screen = Screen.new(40, 10)
screen = screen.draw_hline(2, 0, 20, "\u{2500}")
val line = screen.buffer[2]
expect(line).to_contain("\u{2500}")
```

</details>


</details>

<details>
<summary>Advanced: draw_vline produces a vertical line</summary>

#### draw_vline produces a vertical line _(slow)_

1. var screen = Screen new

2. screen = screen draw vline


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var screen = Screen.new(40, 10)
screen = screen.draw_vline(0, 5, 5, "\u{2502}")
# Each row from 0..4 should have the vertical char at col 5
val row0 = screen.buffer[0]
val row4 = screen.buffer[4]
expect(row0).to_contain("\u{2502}")
expect(row4).to_contain("\u{2502}")
```

</details>


</details>

<details>
<summary>Advanced: fill_row fills entire row</summary>

#### fill_row fills entire row _(slow)_

1. var screen = Screen new

2. screen = screen fill row
   - Expected: line.len() equals `20`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var screen = Screen.new(20, 5)
screen = screen.fill_row(1, "#")
val line = screen.buffer[1]
expect(line).to_start_with("#")
expect(line).to_end_with("#")
expect(line.len()).to_equal(20)
```

</details>


</details>

<details>
<summary>Advanced: put_styled includes style codes</summary>

#### put_styled includes style codes _(slow)_

1. var screen = Screen new

2. screen = screen put styled


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var screen = Screen.new(40, 5)
screen = screen.put_styled(0, 0, "Bold", "\u{001b}[1m")
val line = screen.buffer[0]
# Should contain the ANSI bold escape
expect(line).to_contain("\u{001b}[1m")
# Should contain the text
expect(line).to_contain("Bold")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/tui_screen_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Screen buffer basics
- Screen with UI tree rendering
- Screen drawing primitives

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 11 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
