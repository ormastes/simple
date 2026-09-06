# Unified 2D interaction core — conformance spec

> Covers the first deliverable slice of the shared interaction core (`src/lib/common/engine/interaction/`): an ordered hit stack whose paint order equals hit order, full capture -> target -> bubble event dispatch with stop/immediate-stop/prevent-default semantics, and pointer capture with hover-path diffing. This is surface-agnostic plumbing — no GUI widget, browser DOM, or Node2D adapter is wired yet (that is a later lane); every scenario here builds `HitProxy2D`/`EventListener2D` fixtures directly.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unified 2D interaction core — conformance spec

Covers the first deliverable slice of the shared interaction core (`src/lib/common/engine/interaction/`): an ordered hit stack whose paint order equals hit order, full capture -> target -> bubble event dispatch with stop/immediate-stop/prevent-default semantics, and pointer capture with hover-path diffing. This is surface-agnostic plumbing — no GUI widget, browser DOM, or Node2D adapter is wired yet (that is a later lane); every scenario here builds `HitProxy2D`/`EventListener2D` fixtures directly.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | N/A (Phase 1 of the unified 2D interaction plan) |
| Category | Stdlib / Engine |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | doc/03_plan/ui/unified_2d_engine/unified_2d_interaction_2026-07-20.md |
| Research | N/A |
| Source | `test/01_unit/lib/common/engine/interaction/interaction_core_spec.spl` |
| Updated | 2026-07-20 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Covers the first deliverable slice of the shared interaction core
(`src/lib/common/engine/interaction/`): an ordered hit stack whose paint
order equals hit order, full capture -> target -> bubble event dispatch
with stop/immediate-stop/prevent-default semantics, and pointer capture
with hover-path diffing. This is surface-agnostic plumbing — no GUI
widget, browser DOM, or Node2D adapter is wired yet (that is a later
lane); every scenario here builds `HitProxy2D`/`EventListener2D` fixtures
directly.

A runnable mirror of every case in this file lives at
`probe_interaction_core.spl` in this directory (`timeout 300 bin/simple
run test/01_unit/lib/common/engine/interaction/probe_interaction_core.spl`)
since the `simple test` daemon path is not reliably available in this
environment; the probe is the primary evidence artifact.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Paint-order key | `stacking_context_order, render_layer, z_index, tree_order, insertion_sequence` — the SAME flattened key drives both paint order and hit order |
| `PointerPolicy.None` | Hit-test pass-through: the proxy never appears in the hit stack and never blocks a proxy below it |
| capture -> target -> bubble | `dispatch()` walks `ancestor_path` root-to-target (capture), fires the target, then target-to-root (bubble) |
| `stopPropagation` vs `stopImmediatePropagation` | stop blocks remaining ANCESTOR nodes; stopImmediate additionally blocks remaining listeners on the CURRENT node |
| Pointer capture | While captured, `effective_target()` returns the capture target regardless of where the point currently is |

## Examples

Two overlapping `HitProxy2D` boxes at the same point resolve to the one
with the higher paint-order key. A `PointerPolicy.None` box on top is
skipped entirely, so the point resolves to the box underneath. A 3-node
chain (root -> mid -> target) with capture- and bubble-registered
listeners on every node fires in the order capture(root), capture(mid),
target, bubble(mid), bubble(root); a `stopPropagation` at the target
prevents the bubble-phase ancestors from firing; a second listener on the
same node as a `stopImmediatePropagation` never fires. A captured pointer
keeps resolving to its capture target even when the current point is
outside every proxy's bounds, until `release_pointer()`.

## Scenarios

### hit_stack — paint-order-ranked hit testing

#### the topmost box by paint key wins under overlapping bounds

- Two full-overlap boxes differing only by z_index
- var low = HitProxy2D create
- var high = HitProxy2D create
   - Expected: result.primary equals `2`
   - Expected: result.hits.len() equals `2`
   - Expected: result.hits[0].node_id equals `2`
   - Expected: result.hits[1].node_id equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Two full-overlap boxes differing only by z_index")
var low = HitProxy2D.create(1, 0, 0, 100, 100)
low.z_index = 0
var high = HitProxy2D.create(2, 0, 0, 100, 100)
high.z_index = 5
val parents: Dict<i64, i64> = {}

val result = hit_stack([low, high], parents, 50, 50)
expect(result.primary).to_equal(2)
expect(result.hits.len()).to_equal(2)
expect(result.hits[0].node_id).to_equal(2)
expect(result.hits[1].node_id).to_equal(1)
```

</details>

#### stacking_context_order outranks z_index -- full key precedence, not just the last field

- Box with a lower stacking_context_order but a MUCH higher z_index
- var a = HitProxy2D create
- var b = HitProxy2D create
   - Expected: result.primary equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Box with a lower stacking_context_order but a MUCH higher z_index")
var a = HitProxy2D.create(10, 0, 0, 100, 100)
a.stacking_context_order = 1
a.z_index = 0
var b = HitProxy2D.create(11, 0, 0, 100, 100)
b.stacking_context_order = 0
b.z_index = 999
val parents: Dict<i64, i64> = {}

val result = hit_stack([a, b], parents, 50, 50)
expect(result.primary).to_equal(10)
```

</details>

#### PointerPolicy.None passes hit-testing through to the box below

- A None-policy box fully covers a lower Auto box at the same point
- var top = HitProxy2D create
- var below = HitProxy2D create
   - Expected: result.primary equals `21`
   - Expected: result.hits.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("A None-policy box fully covers a lower Auto box at the same point")
var top = HitProxy2D.create(20, 0, 0, 100, 100)
top.z_index = 99
top.pointer_policy = POINTER_POLICY_NONE
var below = HitProxy2D.create(21, 0, 0, 100, 100)
below.z_index = 0
val parents: Dict<i64, i64> = {}

val result = hit_stack([top, below], parents, 50, 50)
expect(result.primary).to_equal(21)
expect(result.hits.len()).to_equal(1)
```

</details>

#### a point outside every proxy's bounds hits nothing

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val proxy = HitProxy2D.create(30, 0, 0, 10, 10)
val parents: Dict<i64, i64> = {}
val result = hit_stack([proxy], parents, 999, 999)
expect(result.primary).to_equal(-1)
expect(result.ancestor_path.len()).to_equal(0)
```

</details>

#### ancestor_path_of walks a child->parent map into root-to-node order

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parents: Dict<i64, i64> = {}
parents[2] = 1
parents[3] = 2
val path = ancestor_path_of(parents, 3)
expect(path.len()).to_equal(3)
expect(path[0]).to_equal(1)
expect(path[1]).to_equal(2)
expect(path[2]).to_equal(3)
```

</details>

### event_route.dispatch — capture, target, bubble

#### fires capture(root), capture(mid), target, bubble(mid), bubble(root) in order

- A 3-node chain with both capture- and bubble-registered listeners on every node
- EventListener2D create
- EventListener2D create
- EventListener2D create
- EventListener2D create
- EventListener2D create
   - Expected: outcome.fired_node_ids.len() equals `5`
   - Expected: outcome.fired_node_ids[0] equals `100`
   - Expected: outcome.fired_node_ids[1] equals `101`
   - Expected: outcome.fired_node_ids[2] equals `102`
   - Expected: outcome.fired_node_ids[3] equals `101`
   - Expected: outcome.fired_node_ids[4] equals `100`
- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("A 3-node chain with both capture- and bubble-registered listeners on every node")
val path: [i64] = [100, 101, 102]
val listeners = [
    EventListener2D.create(100, -1, true, false, handler_none),
    EventListener2D.create(101, -1, true, false, handler_none),
    EventListener2D.create(102, -1, false, false, handler_none),
    EventListener2D.create(101, -1, false, false, handler_none),
    EventListener2D.create(100, -1, false, false, handler_none)
]
val event = PointerEvent2D.create(1, POINTER_DOWN, 5, 5, 1, 102)

val outcome = dispatch(event, listeners, path)
expect(outcome.fired_node_ids.len()).to_equal(5)
expect(outcome.fired_node_ids[0]).to_equal(100)
expect(outcome.fired_node_ids[1]).to_equal(101)
expect(outcome.fired_node_ids[2]).to_equal(102)
expect(outcome.fired_node_ids[3]).to_equal(101)
expect(outcome.fired_node_ids[4]).to_equal(100)
assert_false(outcome.stopped)
```

</details>

#### stopPropagation at the target blocks the remaining (bubble) ancestors

- EventListener2D create
- EventListener2D create
- EventListener2D create
   - Expected: outcome.fired_node_ids.len() equals `1`
- assert true
- assert false
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path: [i64] = [200, 201, 202]
val listeners = [
    EventListener2D.create(202, -1, false, false, handler_stop_propagation),
    EventListener2D.create(201, -1, false, false, handler_none),
    EventListener2D.create(200, -1, false, false, handler_none)
]
val event = PointerEvent2D.create(1, POINTER_DOWN, 5, 5, 1, 202)

val outcome = dispatch(event, listeners, path)
expect(outcome.fired_node_ids.len()).to_equal(1)
assert_true(outcome.stopped)
assert_false(outcome.stopped_immediate)
assert_true(event.stop_flag)
```

</details>

#### stopImmediatePropagation blocks a later listener registered on the SAME node

- EventListener2D create
- EventListener2D create
   - Expected: _count_i64(outcome.fired_node_ids, 301) equals `1`
- assert true
- the un-fired second listener is NOT dropped -- immediate-stop blocks firing, not registration
   - Expected: outcome.remaining_listeners.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path: [i64] = [300, 301]
val listeners = [
    EventListener2D.create(301, -1, false, false, handler_stop_immediate),
    EventListener2D.create(301, -1, false, false, handler_none)
]
val event = PointerEvent2D.create(1, POINTER_DOWN, 5, 5, 1, 301)

val outcome = dispatch(event, listeners, path)
expect(_count_i64(outcome.fired_node_ids, 301)).to_equal(1)
assert_true(outcome.stopped_immediate)
step("the un-fired second listener is NOT dropped -- immediate-stop blocks firing, not registration")
expect(outcome.remaining_listeners.len()).to_equal(2)
```

</details>

#### a `once` listener fires exactly once and is dropped from the returned listener list

- EventListener2D create
   - Expected: outcome.fired_node_ids.len() equals `1`
   - Expected: outcome.remaining_listeners.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path: [i64] = [400]
val listeners = [
    EventListener2D.create(400, -1, false, true, handler_none)
]
val event = PointerEvent2D.create(1, POINTER_DOWN, 5, 5, 1, 400)

val outcome = dispatch(event, listeners, path)
expect(outcome.fired_node_ids.len()).to_equal(1)
expect(outcome.remaining_listeners.len()).to_equal(0)
```

</details>

#### an empty ancestor_path (nothing hit) is a no-op

- EventListener2D create
   - Expected: outcome.fired_node_ids.len() equals `0`
   - Expected: outcome.remaining_listeners.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event = PointerEvent2D.create(1, POINTER_DOWN, 5, 5, 1, -1)
val listeners = [
    EventListener2D.create(1, -1, false, false, handler_none)
]
val outcome = dispatch(event, listeners, [])
expect(outcome.fired_node_ids.len()).to_equal(0)
expect(outcome.remaining_listeners.len()).to_equal(1)
```

</details>

### pointer_capture — capture routing and hover diff

#### a captured pointer keeps resolving to the capture target outside every proxy's bounds

- Capture pointer 1 on node 500, then hit-test a point far outside any proxy
   - Expected: far_hit.primary equals `-1`
- var router = PointerRouter create
- router capture pointer
- assert true
   - Expected: effective_target(router, 1, far_hit) equals `500`
- release_pointer falls back to the hit-test primary
- router release pointer
- assert false
   - Expected: effective_target(router, 1, far_hit) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Capture pointer 1 on node 500, then hit-test a point far outside any proxy")
val proxy = HitProxy2D.create(500, 0, 0, 10, 10)
val parents: Dict<i64, i64> = {}
val far_hit = hit_stack([proxy], parents, 999, 999)
expect(far_hit.primary).to_equal(-1)

var router = PointerRouter.create()
router.capture_pointer(1, 500)
assert_true(router.has_pointer_capture(1, 500))
expect(effective_target(router, 1, far_hit)).to_equal(500)

step("release_pointer falls back to the hit-test primary")
router.release_pointer(1)
assert_false(router.has_pointer_capture(1, 500))
expect(effective_target(router, 1, far_hit)).to_equal(-1)
```

</details>

#### an uncaptured pointer resolves to the hit-test primary

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val proxy = HitProxy2D.create(600, 0, 0, 100, 100)
val parents: Dict<i64, i64> = {}
val hit = hit_stack([proxy], parents, 50, 50)
val router = PointerRouter.create()
expect(effective_target(router, 1, hit)).to_equal(600)
```

</details>

#### hover_diff emits entered/left node sets and an over/out primary pair

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val old_path: [i64] = [1, 2, 3]
val new_path: [i64] = [1, 4, 5]

val diff = hover_diff(old_path, new_path)
expect(diff.entered.len()).to_equal(2)
expect(_count_i64(diff.entered, 4)).to_equal(1)
expect(_count_i64(diff.entered, 5)).to_equal(1)
expect(diff.left.len()).to_equal(2)
expect(_count_i64(diff.left, 2)).to_equal(1)
expect(_count_i64(diff.left, 3)).to_equal(1)
expect(diff.over_target).to_equal(5)
expect(diff.out_target).to_equal(3)
```

</details>

#### hover_diff on an unchanged path emits no enter/leave and no over/out

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val old_path: [i64] = [1, 2, 3]
val same_path: [i64] = [1, 2, 3]
val diff = hover_diff(old_path, same_path)
expect(diff.entered.len()).to_equal(0)
expect(diff.left.len()).to_equal(0)
expect(diff.over_target).to_equal(-1)
expect(diff.out_target).to_equal(-1)
```

</details>

#### PointerRouter tracks pressed_target independently of capture/hover

- var router = PointerRouter create
   - Expected: router.pressed_target(1) equals `-1`
- router set pressed
   - Expected: router.pressed_target(1) equals `700`
- router clear pressed
   - Expected: router.pressed_target(1) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var router = PointerRouter.create()
expect(router.pressed_target(1)).to_equal(-1)
router.set_pressed(1, 700)
expect(router.pressed_target(1)).to_equal(700)
router.clear_pressed(1)
expect(router.pressed_target(1)).to_equal(-1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** `doc/03_plan/ui/unified_2d_engine/unified_2d_interaction_2026-07-20.md`


</details>
