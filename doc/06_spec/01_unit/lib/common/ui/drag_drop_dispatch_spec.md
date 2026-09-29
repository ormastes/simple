# Drag-and-Drop Dispatch Spec

> `UIEvent.DragStart` / `DragMove` / `DragDrop` are the framework-level CONTENT drag-and-drop events (distinct from the pre-existing window titlebar move, which stays compositor-only and untouched). This spec drives the full sequence through the public `process_event(state, event) -> state` reducer — the same entry point every other UIEvent already goes through — and shows the dragged payload lands on the drop target's `value` prop, that `DragMove` marks exactly one widget `ui_drop_target=true` at a time, and that drag state (`ui_drag_active` root prop, `ui_dragging` source prop) is cleared once the drop completes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Drag-and-Drop Dispatch Spec

`UIEvent.DragStart` / `DragMove` / `DragDrop` are the framework-level CONTENT drag-and-drop events (distinct from the pre-existing window titlebar move, which stays compositor-only and untouched). This spec drives the full sequence through the public `process_event(state, event) -> state` reducer — the same entry point every other UIEvent already goes through — and shows the dragged payload lands on the drop target's `value` prop, that `DragMove` marks exactly one widget `ui_drop_target=true` at a time, and that drag state (`ui_drag_active` root prop, `ui_dragging` source prop) is cleared once the drop completes.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | N/A |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Research | N/A |
| Source | `test/01_unit/lib/common/ui/drag_drop_dispatch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`UIEvent.DragStart` / `DragMove` / `DragDrop` are the framework-level
CONTENT drag-and-drop events (distinct from the pre-existing window
titlebar move, which stays compositor-only and untouched). This spec drives
the full sequence through the public `process_event(state, event) -> state`
reducer — the same entry point every other UIEvent already goes through —
and shows the dragged payload lands on the drop target's `value` prop, that
`DragMove` marks exactly one widget `ui_drop_target=true` at a time, and
that drag state (`ui_drag_active` root prop, `ui_dragging` source prop) is
cleared once the drop completes.

Drag bookkeeping is recorded as props on the ROOT widget node (the same
process-local prop store `ui_hover`/`ui_pressed` use), not as UITree tokens,
so the reducer stays pure and the state round-trips consistently across
backends.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** N/A

## Design

**Design:** doc/04_architecture/ui/simple_gui_stack.md

## Research

**Research:** N/A

## Examples

A tree with a draggable source button and a text-input drop target: start
a drag on the source, move over the target (asserting hover-highlight
tracks the pointer, not a stale widget), then drop — the input's `value`
prop receives the dragged payload and all drag bookkeeping is cleared.

## Scenarios

### Content drag-and-drop — process_event reducer path

#### DragStart marks the source widget dragging and records the payload on the root node

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- DragStart marks the source widget dragging and records the payload on the root node
- Start a drag from the source widget
   - Expected: WidgetNode(id: "start_source").get_prop("ui_dragging") equals `true`
   - Expected: WidgetNode(id: next.tree.root_id).get_prop("ui_drag_active") equals `true`
   - Expected: WidgetNode(id: next.tree.root_id).get_prop("ui_drag_data") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("DragStart marks the source widget dragging and records the payload on the root node")
step("Start a drag from the source widget")
val state = drag_state("start")
val next = process_event(state, UIEvent.DragStart(source_id: "start_source", mime: "text/plain", data: "hello"))

expect(WidgetNode(id: "start_source").get_prop("ui_dragging")).to_equal("true")
expect(WidgetNode(id: next.tree.root_id).get_prop("ui_drag_active")).to_equal("true")
expect(WidgetNode(id: next.tree.root_id).get_prop("ui_drag_data")).to_equal("hello")
```

</details>

#### DragMove highlights exactly the widget under the pointer as the drop target

- DragMove highlights exactly the widget under the pointer as the drop target
- Start a drag, then move over the target input
   - Expected: WidgetNode(id: "move_target").get_prop("ui_drop_target") equals `true`
   - Expected: WidgetNode(id: "move_other").get_prop("ui_drop_target") equals `false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("DragMove highlights exactly the widget under the pointer as the drop target")
step("Start a drag, then move over the target input")
var state = drag_state("move")
state = process_event(state, UIEvent.DragStart(source_id: "move_source", mime: "text/plain", data: "x"))
# text_input widgets stack below the source button in the column
# layout; hit-test at a point inside the target's laid-out rect
# (viewport falls back to 640x480, 3 flex rows ~160px each).
state = process_event(state, UIEvent.DragMove(x: 10, y: 200))

expect(WidgetNode(id: "move_target").get_prop("ui_drop_target")).to_equal("true")
expect(WidgetNode(id: "move_other").get_prop("ui_drop_target")).to_equal("false")
```

</details>

#### DragDrop delivers the payload to the target input's value and clears drag state

- DragDrop delivers the payload to the target input's value and clears drag state
- Start a drag, move onto the target, then drop
- Payload landed on the target's value prop
   - Expected: WidgetNode(id: "drop_target").get_prop("value") equals `dropped-payload`
- Drag bookkeeping is cleared: source no longer dragging, root inactive, hover cleared
   - Expected: WidgetNode(id: "drop_source").get_prop("ui_dragging") equals `false`
   - Expected: WidgetNode(id: after.tree.root_id).get_prop("ui_drag_active") equals `false`
   - Expected: WidgetNode(id: "drop_target").get_prop("ui_drop_target") equals `false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("DragDrop delivers the payload to the target input's value and clears drag state")
step("Start a drag, move onto the target, then drop")
var state = drag_state("drop")
state = process_event(state, UIEvent.DragStart(source_id: "drop_source", mime: "text/plain", data: "dropped-payload"))
state = process_event(state, UIEvent.DragMove(x: 10, y: 200))
val after = process_event(state, UIEvent.DragDrop(mime: "text/plain", data: "dropped-payload", x: 10, y: 200, source_id: "drop_source"))

step("Payload landed on the target's value prop")
expect(WidgetNode(id: "drop_target").get_prop("value")).to_equal("dropped-payload")

step("Drag bookkeeping is cleared: source no longer dragging, root inactive, hover cleared")
expect(WidgetNode(id: "drop_source").get_prop("ui_dragging")).to_equal("false")
expect(WidgetNode(id: after.tree.root_id).get_prop("ui_drag_active")).to_equal("false")
expect(WidgetNode(id: "drop_target").get_prop("ui_drop_target")).to_equal("false")
```

</details>

#### DragDrop over empty space (no hit) still clears drag state without touching any widget value

- DragDrop over empty space (no hit) still clears drag state without touching any widget value
- Start a drag, then drop far outside every widget's rect
   - Expected: WidgetNode(id: after.tree.root_id).get_prop("ui_drag_active") equals `false`
   - Expected: WidgetNode(id: "miss_target").get_prop("value") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("DragDrop over empty space (no hit) still clears drag state without touching any widget value")
step("Start a drag, then drop far outside every widget's rect")
var state = drag_state("miss")
state = process_event(state, UIEvent.DragStart(source_id: "miss_source", mime: "text/plain", data: "x"))
val after = process_event(state, UIEvent.DragDrop(mime: "text/plain", data: "x", x: 9999, y: 9999, source_id: "miss_source"))

expect(WidgetNode(id: after.tree.root_id).get_prop("ui_drag_active")).to_equal("false")
expect(WidgetNode(id: "miss_target").get_prop("value")).to_equal("")
```

</details>

#### DragMove before any DragStart is a no-op (no active drag to route)

- DragMove before any DragStart is a no-op (no active drag to route)
- Move without a preceding DragStart
   - Expected: WidgetNode(id: "nodrag_target").get_prop("ui_drop_target") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("DragMove before any DragStart is a no-op (no active drag to route)")
step("Move without a preceding DragStart")
val state = drag_state("nodrag")
process_event(state, UIEvent.DragMove(x: 10, y: 200))
expect(WidgetNode(id: "nodrag_target").get_prop("ui_drop_target")).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** `doc/04_architecture/ui/simple_gui_stack.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `33f9ad44f3ca0e18541100dfbdb993666022071b043ea09da36e71867ca05e5f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `33f9ad44f3ca0e18541100dfbdb993666022071b043ea09da36e71867ca05e5f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `33f9ad44f3ca0e18541100dfbdb993666022071b043ea09da36e71867ca05e5f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/ui/drag_drop_dispatch_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/drag_drop_dispatch_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/drag_drop_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/drag_drop_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/drag_drop_dispatch_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'DragStart marks the source widget dragging and records the payload on the root node' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/drag_drop_dispatch_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'DragMove highlights exactly the widget under the pointer as the drop target' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/drag_drop_dispatch_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'DragDrop delivers the payload to the target input's value and clears drag state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
