# Gui Event Dispatch Specification

> Tests covering tiny GUI focus and event dispatch.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gui Event Dispatch Specification

## Scenarios

### tiny GUI focus and event dispatch

#### routes tab, enter, pointer, checkbox, and text input

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### resolves child-local bounds before pointer hit testing

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = TinyGuiState.bounded(2)
state.add(TinyHandle.invalid(), TINY_COMPONENT_BUTTON, TinyRect(x: 40, y: 30, width: 40, height: 30), "parent")
val parent = state.handle_at(0)
state.add(parent, TINY_COMPONENT_CHECKBOX, TinyRect(x: 5, y: 6, width: 10, height: 10), "child")
val click = tiny_gui_dispatch(state, TinyEvent(kind: TINY_EVENT_POINTER_DOWN, point: TinyPoint(x: 47, y: 38), code: 0, value: 0))
expect(click.target_index).to_equal(1)
expect(click.state.nodes[1].value).to_equal(1)
```

</details>

#### routes pointer events through Row flow positions

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = TinyGuiState.bounded(3)
state.add(TinyHandle.invalid(), TINY_COMPONENT_ROW, TinyRect(x: 0, y: 0, width: 20, height: 4), "")
state.add(state.handle_at(0), TINY_COMPONENT_BUTTON, TinyRect(x: 99, y: 99, width: 5, height: 3), "go")
state.add(state.handle_at(0), TINY_COMPONENT_CHECKBOX, TinyRect(x: 99, y: 99, width: 5, height: 3), "check")
val click = tiny_gui_dispatch(state, TinyEvent(kind: TINY_EVENT_POINTER_DOWN, point: TinyPoint(x: 7, y: 1), code: 0, value: 0))
expect(click.target_index).to_equal(2)
expect(click.state.nodes[2].value).to_equal(1)
```

</details>

#### reports events without a target and unsupported events

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = TinyGuiState.bounded(1)
state.add(TinyHandle.invalid(), TINY_COMPONENT_TEXT, TinyRect(x: 0, y: 0, width: 20, height: 10), "label")
val click = tiny_gui_dispatch(state, TinyEvent(kind: TINY_EVENT_POINTER_DOWN, point: TinyPoint(x: 2, y: 2), code: 0, value: 0))
expect(click.status.is_ok()).to_be(false)
expect(click.target_index).to_equal(-1)
expect(click.state.focused_index).to_equal(-1)
```

</details>

#### selects List items and scrolls ScrollPane children through resolved geometry

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var list_state = TinyGuiState.bounded(3)
list_state.add(TinyHandle.invalid(), TINY_COMPONENT_LIST, TinyRect(x: 0, y: 0, width: 20, height: 3), "")
list_state.add(list_state.handle_at(0), TINY_COMPONENT_TEXT, TinyRect(x: 0, y: 0, width: 10, height: 1), "first")
list_state.add(list_state.handle_at(0), TINY_COMPONENT_TEXT, TinyRect(x: 0, y: 0, width: 10, height: 1), "second")
val selected = tiny_gui_dispatch(list_state, TinyEvent(kind: TINY_EVENT_POINTER_DOWN, point: TinyPoint(x: 3, y: 1), code: 0, value: 0))
expect(selected.status.is_ok()).to_be(true)
expect(selected.state.nodes[0].value).to_equal(1)
val moved = tiny_gui_dispatch(selected.state, TinyEvent(kind: TINY_EVENT_KEY, point: TinyPoint(x: 0, y: 0), code: TINY_KEY_DOWN, value: 0))
expect(moved.state.nodes[0].value).to_equal(1)

var scroll_state = TinyGuiState.bounded(4)
scroll_state.add(TinyHandle.invalid(), TINY_COMPONENT_SCROLL_PANE, TinyRect(x: 0, y: 0, width: 20, height: 2), "")
scroll_state.add(scroll_state.handle_at(0), TINY_COMPONENT_TEXT, TinyRect(x: 0, y: 0, width: 10, height: 1), "one")
scroll_state.add(scroll_state.handle_at(0), TINY_COMPONENT_TEXT, TinyRect(x: 0, y: 0, width: 10, height: 1), "two")
scroll_state.add(scroll_state.handle_at(0), TINY_COMPONENT_TEXT, TinyRect(x: 0, y: 0, width: 10, height: 1), "three")
val scrolled = tiny_gui_dispatch(scroll_state, TinyEvent(kind: TINY_EVENT_WHEEL, point: TinyPoint(x: 1, y: 1), code: 0, value: 1))
expect(scrolled.status.is_ok()).to_be(true)
expect(scrolled.changed).to_be(true)
expect(scrolled.state.nodes[0].value).to_equal(1)
expect(scrolled.state.resolved_panes(TinyRect(x: 0, y: 0, width: 20, height: 4))[1].absolute.y).to_equal(-1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/tiny/gui_event_dispatch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering tiny GUI focus and event dispatch.
- tiny GUI focus and event dispatch

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `57177d96505fff230af671df0abd838d1d3e1846eeb8aef9e828e0b96bbcd777`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `57177d96505fff230af671df0abd838d1d3e1846eeb8aef9e828e0b96bbcd777`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `57177d96505fff230af671df0abd838d1d3e1846eeb8aef9e828e0b96bbcd777`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **83/100**; blockers: **0**.

SSpec documentization score: 83/100
source: test/01_unit/lib/tiny/gui_event_dispatch_spec.spl
mirror: doc/06_spec/01_unit/lib/tiny/gui_event_dispatch_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=60 oracle=70
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/tiny/gui_event_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/tiny/gui_event_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/tiny/gui_event_dispatch_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/lib/tiny/gui_event_dispatch_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/tiny/gui_event_dispatch_spec.spl:17:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'routes tab, enter, pointer, checkbox, and text input' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/tiny/gui_event_dispatch_spec.spl:47:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'resolves child-local bounds before pointer hit testing' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/tiny/gui_event_dispatch_spec.spl:56:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'routes pointer events through Row flow positions' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/tiny/gui_event_dispatch_spec.spl:65:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'reports events without a target and unsupported events' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
