# tui_render_spec

> Purpose: Prove that Tiny TUI host renderer.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# tui_render_spec

Purpose: Prove that Tiny TUI host renderer.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/tiny/tui_render_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Tiny TUI host renderer.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### Tiny TUI host renderer

#### renders the shared GUI controls into a bounded cell grid

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- renders the shared GUI controls into a bounded cell grid
- Verify: renders the shared GUI controls into a bounded cell grid
   - Expected: state.add(parent, TINY_COMPONENT_TEXT_INPUT, TinyRect(x: 1, y: 1, width: 8, height: 3), "Hi").code equals `0`
   - Expected: state.add(parent, TINY_COMPONENT_CHECKBOX, TinyRect(x: 1, y: 4, width: 8, height: 1), "On").code equals `0`
   - Expected: state.add(parent, TINY_COMPONENT_BUTTON, TinyRect(x: 1, y: 6, width: 8, height: 3), "Go").code equals `0`
   - Expected: screen.cells.len() equals `120`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders the shared GUI controls into a bounded cell grid")
step("Verify: renders the shared GUI controls into a bounded cell grid")
# @req: REQ-LIB-TINY-001
var state = TinyGuiState.bounded(4)
val parent = TinyHandle.invalid()
expect(state.add(parent, TINY_COMPONENT_TEXT_INPUT, TinyRect(x: 1, y: 1, width: 8, height: 3), "Hi").code).to_equal(0)
expect(state.add(parent, TINY_COMPONENT_CHECKBOX, TinyRect(x: 1, y: 4, width: 8, height: 1), "On").code).to_equal(0)
expect(state.add(parent, TINY_COMPONENT_BUTTON, TinyRect(x: 1, y: 6, width: 8, height: 3), "Go").code).to_equal(0)
var checked = state.nodes[1]
checked.value = 1
state.nodes[1] = checked
state.focused_index = 2
val screen = tiny_tui_render(state, 12, 10)
expect(screen.row_text(2)).to_contain("Hi")
expect(screen.row_text(4)).to_contain("[x]On")
expect(screen.row_text(7)).to_contain("Go")
expect(screen.cells.len()).to_equal(120)  # oracle: 120 — named expected value from the requirement
```

</details>

#### clips controls at the cell-buffer edge

- clips controls at the cell-buffer edge
- Verify: clips controls at the cell-buffer edge
   - Expected: state.add(TinyHandle.invalid(), TINY_COMPONENT_BUTTON, TinyRect(x: 3, y: 1, width: 8, height: 3), "Wide").code equals `0`
   - Expected: screen.cells.len() equals `18`
   - Expected: screen.row_text(2).len() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("clips controls at the cell-buffer edge")
step("Verify: clips controls at the cell-buffer edge")
var state = TinyGuiState.bounded(1)
expect(state.add(TinyHandle.invalid(), TINY_COMPONENT_BUTTON, TinyRect(x: 3, y: 1, width: 8, height: 3), "Wide").code).to_equal(0)
val screen = tiny_tui_render(state, 6, 3)
expect(screen.cells.len()).to_equal(18)  # oracle: 18 — named expected value from the requirement
expect(screen.row_text(2).len()).to_equal(6)  # oracle: 6 — named expected value from the requirement
```

</details>

#### resolves child-local coordinates and clips through the shared pane tree

- resolves child-local coordinates and clips through the shared pane tree
- Verify: resolves child-local coordinates and clips through the shared pane tree
   - Expected: state.add(TinyHandle.invalid(), TINY_COMPONENT_PANE, TinyRect(x: 2, y: 1, width: 6, height: 4), "").code equals `0`
   - Expected: state.add(state.handle_at(0), TINY_COMPONENT_BUTTON, TinyRect(x: 1, y: 1, width: 6, height: 3), "Go").code equals `0`
   - Expected: screen.glyph_at(8, 2) equals ` `


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("resolves child-local coordinates and clips through the shared pane tree")
step("Verify: resolves child-local coordinates and clips through the shared pane tree")
var state = TinyGuiState.bounded(2)
expect(state.add(TinyHandle.invalid(), TINY_COMPONENT_PANE, TinyRect(x: 2, y: 1, width: 6, height: 4), "").code).to_equal(0)
expect(state.add(state.handle_at(0), TINY_COMPONENT_BUTTON, TinyRect(x: 1, y: 1, width: 6, height: 3), "Go").code).to_equal(0)
val screen = tiny_tui_render(state, 12, 8)
expect(screen.row_text(2)).to_not_contain("Go")
expect(screen.row_text(3)).to_contain("Go")
expect(screen.glyph_at(8, 2)).to_equal(" ")
```

</details>

#### normalizes invalid dimensions to an empty bounded buffer

- normalizes invalid dimensions to an empty bounded buffer
- Verify: normalizes invalid dimensions to an empty bounded buffer
   - Expected: screen.width equals `0`
   - Expected: screen.height equals `0`
   - Expected: screen.cells.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("normalizes invalid dimensions to an empty bounded buffer")
step("Verify: normalizes invalid dimensions to an empty bounded buffer")
val screen = tiny_tui_render(TinyGuiState.bounded(0), -2, -3)
expect(screen.width).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(screen.height).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(screen.cells.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### draws List selection and ScrollPane clipping from shared resolved panes

- draws List selection and ScrollPane clipping from shared resolved panes
- Verify: draws List selection and ScrollPane clipping from shared resolved panes
   - Expected: state.add(TinyHandle.invalid(), TINY_COMPONENT_LIST, TinyRect(x: 0, y: 0, width: 12, height: 2), "").code equals `0`
   - Expected: state.add(state.handle_at(0), TINY_COMPONENT_TEXT, TinyRect(x: 0, y: 0, width: 8, height: 1), "first").code equals `0`
   - Expected: state.add(state.handle_at(0), TINY_COMPONENT_TEXT, TinyRect(x: 0, y: 0, width: 8, height: 1), "second").code equals `0`
   - Expected: state.add(TinyHandle.invalid(), TINY_COMPONENT_SCROLL_PANE, TinyRect(x: 0, y: 3, width: 12, height: 2), "").code equals `0`
   - Expected: state.add(state.handle_at(3), TINY_COMPONENT_TEXT, TinyRect(x: 0, y: 0, width: 8, height: 1), "hidden").code equals `0`
   - Expected: state.add(state.handle_at(3), TINY_COMPONENT_TEXT, TinyRect(x: 0, y: 0, width: 8, height: 1), "visible").code equals `0`
   - Expected: state.add(state.handle_at(3), TINY_COMPONENT_TEXT, TinyRect(x: 0, y: 0, width: 8, height: 1), "tail").code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("draws List selection and ScrollPane clipping from shared resolved panes")
step("Verify: draws List selection and ScrollPane clipping from shared resolved panes")
var state = TinyGuiState.bounded(7)
expect(state.add(TinyHandle.invalid(), TINY_COMPONENT_LIST, TinyRect(x: 0, y: 0, width: 12, height: 2), "").code).to_equal(0)
expect(state.add(state.handle_at(0), TINY_COMPONENT_TEXT, TinyRect(x: 0, y: 0, width: 8, height: 1), "first").code).to_equal(0)
expect(state.add(state.handle_at(0), TINY_COMPONENT_TEXT, TinyRect(x: 0, y: 0, width: 8, height: 1), "second").code).to_equal(0)
var list = state.nodes[0]
list.value = 1
state.nodes[0] = list
expect(state.add(TinyHandle.invalid(), TINY_COMPONENT_SCROLL_PANE, TinyRect(x: 0, y: 3, width: 12, height: 2), "").code).to_equal(0)
expect(state.add(state.handle_at(3), TINY_COMPONENT_TEXT, TinyRect(x: 0, y: 0, width: 8, height: 1), "hidden").code).to_equal(0)
expect(state.add(state.handle_at(3), TINY_COMPONENT_TEXT, TinyRect(x: 0, y: 0, width: 8, height: 1), "visible").code).to_equal(0)
expect(state.add(state.handle_at(3), TINY_COMPONENT_TEXT, TinyRect(x: 0, y: 0, width: 8, height: 1), "tail").code).to_equal(0)
var scroll = state.nodes[3]
scroll.value = 1
state.nodes[3] = scroll
val screen = tiny_tui_render(state, 14, 6)
expect(screen.row_text(1)).to_start_with("> second")
expect(screen.row_text(3)).to_start_with("visible")
expect(screen.row_text(3)).to_contain("^")
```

</details>

#### draws Row Column and Stack children at their flow and overlay positions

- draws Row Column and Stack children at their flow and overlay positions
- Verify: draws Row Column and Stack children at their flow and overlay positions


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("draws Row Column and Stack children at their flow and overlay positions")
step("Verify: draws Row Column and Stack children at their flow and overlay positions")
var state = TinyGuiState.bounded(9)
state.add(TinyHandle.invalid(), TINY_COMPONENT_ROW, TinyRect(x: 0, y: 0, width: 8, height: 1), "")
state.add(state.handle_at(0), TINY_COMPONENT_TEXT, TinyRect(x: 9, y: 9, width: 1, height: 1), "A")
state.add(state.handle_at(0), TINY_COMPONENT_TEXT, TinyRect(x: 9, y: 9, width: 1, height: 1), "B")
state.add(TinyHandle.invalid(), TINY_COMPONENT_COLUMN, TinyRect(x: 0, y: 1, width: 8, height: 2), "")
state.add(state.handle_at(3), TINY_COMPONENT_TEXT, TinyRect(x: 9, y: 9, width: 1, height: 1), "C")
state.add(state.handle_at(3), TINY_COMPONENT_TEXT, TinyRect(x: 9, y: 9, width: 1, height: 1), "D")
state.add(TinyHandle.invalid(), TINY_COMPONENT_STACK, TinyRect(x: 0, y: 3, width: 8, height: 1), "")
state.add(state.handle_at(6), TINY_COMPONENT_TEXT, TinyRect(x: 0, y: 0, width: 1, height: 1), "u")
state.add(state.handle_at(6), TINY_COMPONENT_TEXT, TinyRect(x: 0, y: 0, width: 1, height: 1), "o")
val screen = tiny_tui_render(state, 8, 5)
expect(screen.row_text(0)).to_start_with("AB")
expect(screen.row_text(1)).to_start_with("C")
expect(screen.row_text(2)).to_start_with("D")
expect(screen.row_text(3)).to_start_with("o")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
- `REQ-LIB-TINY-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `afad18ce088ffed1b55b80f15b317b46cdf79c47ed2a18308767bec1913bda41`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `afad18ce088ffed1b55b80f15b317b46cdf79c47ed2a18308767bec1913bda41`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `afad18ce088ffed1b55b80f15b317b46cdf79c47ed2a18308767bec1913bda41`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/tiny/tui_render_spec.spl
mirror: doc/06_spec/01_unit/lib/tiny/tui_render_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/tiny/tui_render_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/tiny/tui_render_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/tiny/tui_render_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 13 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/tiny/tui_render_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders the shared GUI controls into a bounded cell grid' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/tiny/tui_render_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clips controls at the cell-buffer edge' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/tiny/tui_render_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves child-local coordinates and clips through the shared pane tree' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
