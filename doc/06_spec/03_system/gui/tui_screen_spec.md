# Tui Screen Specification

> Tests covering Screen buffer basics, Screen with UI tree rendering, Screen drawing primitives.

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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates screen with correct dimensions
   - Expected: screen.width equals `80`
   - Expected: screen.height equals `24`
   - Expected: screen.buffer.len() equals `24`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates screen with correct dimensions")
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

- put_text writes content at position


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("put_text writes content at position")
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

- draw_box produces box-drawing characters


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("draw_box produces box-drawing characters")
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

- render produces non-empty output


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("render produces non-empty output")
val screen = Screen.new(80, 24)
val output = screen.render()
expect(output.len()).to_be_greater_than(0)
```

</details>


</details>

<details>
<summary>Advanced: clear resets the buffer</summary>

#### clear resets the buffer _(slow)_

- clear resets the buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("clear resets the buffer")
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

- renders minimal.ui.sdn tree to screen buffer
   - Expected: e equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders minimal.ui.sdn tree to screen buffer")
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

- renders demo.ui.sdn tree with multiple widgets
   - Expected: e equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders demo.ui.sdn tree with multiple widgets")
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

- draw_hline produces a horizontal line


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("draw_hline produces a horizontal line")
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

- draw_vline produces a vertical line


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("draw_vline produces a vertical line")
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

- fill_row fills entire row
   - Expected: line.len() equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fill_row fills entire row")
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

- put_styled includes style codes


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("put_styled includes style codes")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Screen buffer basics, Screen with UI tree rendering, Screen drawing primitives.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c26012643906af40d36cfcafaf75220203071859139c31f9990c2918bd99c4ea`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c26012643906af40d36cfcafaf75220203071859139c31f9990c2918bd99c4ea`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c26012643906af40d36cfcafaf75220203071859139c31f9990c2918bd99c4ea`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/gui/tui_screen_spec.spl
mirror: doc/06_spec/03_system/gui/tui_screen_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/tui_screen_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/tui_screen_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/tui_screen_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/gui/tui_screen_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates screen with correct dimensions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/tui_screen_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'put_text writes content at position' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/tui_screen_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'draw_box produces box-drawing characters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
