# gui_event_dispatch_spec

> Verifies the gui event dispatch behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# gui_event_dispatch_spec

Verifies the gui event dispatch behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/tiny/gui_event_dispatch_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the gui event dispatch behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### tiny GUI focus and event dispatch

#### routes tab, enter, pointer, checkbox, and text input

- Verify: routes tab, enter, pointer, checkbox, and text input
   - Expected: tab.target_index equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: enter.action_id equals `77)  # oracle: pinned constant asserted by this scenario`
   - Expected: state.nodes[1].value equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: state.nodes[2].text_value equals `A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TINY_GUI_EVENT_DISPATCH-001
step("Verify: routes tab, enter, pointer, checkbox, and text input")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var state = TinyGuiState.bounded(3)
state.add(TinyHandle.invalid(), TINY_COMPONENT_BUTTON, TinyRect(x: 0, y: 0, width: 20, height: 10), "go")
state.add(TinyHandle.invalid(), TINY_COMPONENT_CHECKBOX, TinyRect(x: 0, y: 12, width: 20, height: 10), "check")
state.add(TinyHandle.invalid(), TINY_COMPONENT_TEXT_INPUT, TinyRect(x: 0, y: 24, width: 30, height: 10), "")
var button = state.nodes[0]
button.value = 77
state.nodes[0] = button

val tab = tiny_gui_dispatch(state, TinyEvent(kind: TINY_EVENT_KEY, point: TinyPoint(x: 0, y: 0), code: TINY_KEY_TAB, value: 0))
state = tab.state
expect(tab.target_index).to_equal(0)  # oracle: pinned constant asserted by this scenario
val enter = tiny_gui_dispatch(state, TinyEvent(kind: TINY_EVENT_KEY, point: TinyPoint(x: 0, y: 0), code: TINY_KEY_ENTER, value: 0))
state = enter.state
expect(enter.action_id).to_equal(77)  # oracle: pinned constant asserted by this scenario

val click = tiny_gui_dispatch(state, TinyEvent(kind: TINY_EVENT_POINTER_DOWN, point: TinyPoint(x: 4, y: 16), code: 0, value: 0))
state = click.state
expect(click.changed).to_be(true)
expect(state.nodes[1].value).to_equal(1)  # oracle: pinned constant asserted by this scenario

val focus_input = tiny_gui_dispatch(state, TinyEvent(kind: TINY_EVENT_POINTER_DOWN, point: TinyPoint(x: 4, y: 28), code: 0, value: 0))
state = focus_input.state
val typed = tiny_gui_dispatch(state, TinyEvent(kind: TINY_EVENT_TEXT, point: TinyPoint(x: 0, y: 0), code: 65, value: 0))
state = typed.state
expect(typed.changed).to_be(true)
expect(state.nodes[2].text_value).to_equal("A")
```

</details>

#### resolves child-local bounds before pointer hit testing

- Verify: resolves child-local bounds before pointer hit testing
   - Expected: click.target_index equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: click.state.nodes[1].value equals `1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TINY_GUI_EVENT_DISPATCH-001
step("Verify: resolves child-local bounds before pointer hit testing")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var state = TinyGuiState.bounded(2)
state.add(TinyHandle.invalid(), TINY_COMPONENT_BUTTON, TinyRect(x: 40, y: 30, width: 40, height: 30), "parent")
val parent = state.handle_at(0)
state.add(parent, TINY_COMPONENT_CHECKBOX, TinyRect(x: 5, y: 6, width: 10, height: 10), "child")
val click = tiny_gui_dispatch(state, TinyEvent(kind: TINY_EVENT_POINTER_DOWN, point: TinyPoint(x: 47, y: 38), code: 0, value: 0))
expect(click.target_index).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(click.state.nodes[1].value).to_equal(1)  # oracle: pinned constant asserted by this scenario
```

</details>

#### routes pointer events through Row flow positions

- Verify: routes pointer events through Row flow positions
   - Expected: click.target_index equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: click.state.nodes[2].value equals `1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TINY_GUI_EVENT_DISPATCH-001
step("Verify: routes pointer events through Row flow positions")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var state = TinyGuiState.bounded(3)
state.add(TinyHandle.invalid(), TINY_COMPONENT_ROW, TinyRect(x: 0, y: 0, width: 20, height: 4), "")
state.add(state.handle_at(0), TINY_COMPONENT_BUTTON, TinyRect(x: 99, y: 99, width: 5, height: 3), "go")
state.add(state.handle_at(0), TINY_COMPONENT_CHECKBOX, TinyRect(x: 99, y: 99, width: 5, height: 3), "check")
val click = tiny_gui_dispatch(state, TinyEvent(kind: TINY_EVENT_POINTER_DOWN, point: TinyPoint(x: 7, y: 1), code: 0, value: 0))
expect(click.target_index).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(click.state.nodes[2].value).to_equal(1)  # oracle: pinned constant asserted by this scenario
```

</details>

#### reports events without a target and unsupported events

- Verify: reports events without a target and unsupported events


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TINY_GUI_EVENT_DISPATCH-001
step("Verify: reports events without a target and unsupported events")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var empty = TinyGuiState.bounded(0)
val miss = tiny_gui_dispatch(empty, TinyEvent(kind: TINY_EVENT_POINTER_DOWN, point: TinyPoint(x: 99, y: 99), code: 0, value: 0))
expect(miss.status.is_ok()).to_be(false)

var state = TinyGuiState.bounded(1)
state.add(TinyHandle.invalid(), TINY_COMPONENT_BUTTON, TinyRect(x: 0, y: 0, width: 10, height: 10), "go")
state.focused_index = 0
val unsupported = tiny_gui_dispatch(state, TinyEvent.none())
expect(unsupported.status.is_ok()).to_be(false)
```

</details>

#### does not assign pointer focus to non-focusable display components

- Verify: does not assign pointer focus to non-focusable display components
   - Expected: click.target_index equals `-1)  # oracle: pinned constant asserted by this scenario`
   - Expected: click.state.focused_index equals `-1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TINY_GUI_EVENT_DISPATCH-001
step("Verify: does not assign pointer focus to non-focusable display components")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var state = TinyGuiState.bounded(1)
state.add(TinyHandle.invalid(), TINY_COMPONENT_TEXT, TinyRect(x: 0, y: 0, width: 20, height: 10), "label")
val click = tiny_gui_dispatch(state, TinyEvent(kind: TINY_EVENT_POINTER_DOWN, point: TinyPoint(x: 2, y: 2), code: 0, value: 0))
expect(click.status.is_ok()).to_be(false)
expect(click.target_index).to_equal(-1)  # oracle: pinned constant asserted by this scenario
expect(click.state.focused_index).to_equal(-1)  # oracle: pinned constant asserted by this scenario
```

</details>

#### selects List items and scrolls ScrollPane children through resolved geometry

- Verify: selects List items and scrolls ScrollPane children through resolved geometry
   - Expected: selected.state.nodes[0].value equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: moved.state.nodes[0].value equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: scrolled.state.nodes[0].value equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: scrolled.state.resolved_panes(TinyRect(x: 0, y: 0, width: 20, height: 4))[1].absolute.y equals `-1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TINY_GUI_EVENT_DISPATCH-001
step("Verify: selects List items and scrolls ScrollPane children through resolved geometry")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var list_state = TinyGuiState.bounded(3)
list_state.add(TinyHandle.invalid(), TINY_COMPONENT_LIST, TinyRect(x: 0, y: 0, width: 20, height: 3), "")
list_state.add(list_state.handle_at(0), TINY_COMPONENT_TEXT, TinyRect(x: 0, y: 0, width: 10, height: 1), "first")
list_state.add(list_state.handle_at(0), TINY_COMPONENT_TEXT, TinyRect(x: 0, y: 0, width: 10, height: 1), "second")
val selected = tiny_gui_dispatch(list_state, TinyEvent(kind: TINY_EVENT_POINTER_DOWN, point: TinyPoint(x: 3, y: 1), code: 0, value: 0))
expect(selected.status.is_ok()).to_be(true)
expect(selected.state.nodes[0].value).to_equal(1)  # oracle: pinned constant asserted by this scenario
val moved = tiny_gui_dispatch(selected.state, TinyEvent(kind: TINY_EVENT_KEY, point: TinyPoint(x: 0, y: 0), code: TINY_KEY_DOWN, value: 0))
expect(moved.state.nodes[0].value).to_equal(1)  # oracle: pinned constant asserted by this scenario

var scroll_state = TinyGuiState.bounded(4)
scroll_state.add(TinyHandle.invalid(), TINY_COMPONENT_SCROLL_PANE, TinyRect(x: 0, y: 0, width: 20, height: 2), "")
scroll_state.add(scroll_state.handle_at(0), TINY_COMPONENT_TEXT, TinyRect(x: 0, y: 0, width: 10, height: 1), "one")
scroll_state.add(scroll_state.handle_at(0), TINY_COMPONENT_TEXT, TinyRect(x: 0, y: 0, width: 10, height: 1), "two")
scroll_state.add(scroll_state.handle_at(0), TINY_COMPONENT_TEXT, TinyRect(x: 0, y: 0, width: 10, height: 1), "three")
val scrolled = tiny_gui_dispatch(scroll_state, TinyEvent(kind: TINY_EVENT_WHEEL, point: TinyPoint(x: 1, y: 1), code: 0, value: 1))
expect(scrolled.status.is_ok()).to_be(true)
expect(scrolled.changed).to_be(true)
expect(scrolled.state.nodes[0].value).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(scrolled.state.resolved_panes(TinyRect(x: 0, y: 0, width: 20, height: 4))[1].absolute.y).to_equal(-1)  # oracle: pinned constant asserted by this scenario
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4fea65cd0aa4f09bae4ac17a91b5931fc70810784c312a1fc3e1d23b3deeb563`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4fea65cd0aa4f09bae4ac17a91b5931fc70810784c312a1fc3e1d23b3deeb563`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4fea65cd0aa4f09bae4ac17a91b5931fc70810784c312a1fc3e1d23b3deeb563`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/lib/tiny/gui_event_dispatch_spec.spl
mirror: doc/06_spec/01_unit/lib/tiny/gui_event_dispatch_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/tiny/gui_event_dispatch_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/lib/tiny/gui_event_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/tiny/gui_event_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
