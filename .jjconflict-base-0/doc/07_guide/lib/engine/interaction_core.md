# Unified 2D Interaction Core

`src/lib/common/engine/interaction/` (`use std.common.engine.interaction.*`) is
a surface-agnostic hit-testing and event-dispatch core shared by GUI widgets,
the browser DOM engine, and Engine2D/game nodes. It owns no tree structure,
no rendering, and no windowing — callers supply a flat proxy array, a
child→parent map, and listener lists; the core returns ordered results.
Landed `e9734f41cf2` (spec 15/15, probe 38/38).

```
src/lib/common/engine/interaction/
  pointer_event.spl    PointerEvent2D, kind/phase codes
  hit_proxy.spl         HitProxy2D, PointerPolicy codes, paint_key_less
  hit_test.spl           hit_stack() -> HitTestResult (ordered front-to-back)
  event_route.spl        dispatch() -> capture/target/bubble, DispatchOutcome
  pointer_capture.spl     PointerRouter (capture/hover/press), hover_diff()
  mod.spl                 re-exports all of the above
```

Governing plan:
`doc/03_plan/ui/unified_2d_engine/unified_2d_interaction_2026-07-20.md`
(landed `e9390c63774` on `origin/main`). It diagnoses the pre-existing
fragmentation (GUI hit test vs browser hit test disagreeing on bounds
inclusion, event dispatch being target-phase-only, no pointer capture) with
file:line evidence, adopts the `PaintOrderKey`/`PointerPolicy`/
`HitTestResult`/`PointerRouter` model this package implements, and assigns
this package to **Phase 1** of a 0-7 phase plan ("Phase 1 — Shared
interaction core: ... ordered hit stack, capture/target/bubble, stop +
default-prevention semantics, pointer capture, enter/leave/over/out,
transparent hit policies").

## Model: paint order == hit order

`HitProxy2D` (`hit_proxy.spl`) carries the same flattened ordering key used
for rendering — `stacking_context_order`, `render_layer`, `z_index`,
`tree_order`, `insertion_sequence`, compared in that priority order,
ascending = later/on top. `hit_stack()` (`hit_test.spl`) sorts hit
candidates by the identical key (`_hit_record_less`, front-to-back
descending) so whichever proxy paints on top is also the one that receives
the pointer. `paint_key_less()` is exported specifically so a future
renderer can sort with the same key and the two orders can never drift
apart.

`PointerPolicy` (an `i32` code on `HitProxy2D`, not a rendering property) is
deliberately independent of paint opacity — a fully transparent element can
still be hit-testable, and a fully opaque one can be click-through. Today
only two policies are actually distinguished by `hit_test.spl`:

- `POINTER_POLICY_NONE` — skipped entirely: never appears in the hit stack
  and never blocks a proxy underneath it.
- Everything else (`Auto`, `BoundingBox`, `Painted`, `Fill`, `Stroke`,
  `SelfOnly`, `ChildrenOnly`, `Translucent`) hit-tests against the proxy's
  axis-aligned bounding box via `HitProxy2D.contains_point()`.

**Gotcha:** `Painted`/`Fill`/`Stroke` are reserved policy codes with no
distinct behavior yet — there is no rasterized-content/coverage buffer in
this core to sample against, so they fall back to bounding-box. `SelfOnly`,
`ChildrenOnly`, and `Translucent` are defined for future adapters
(widget/DOM/Node2D) but are not interpreted here at all. Do not assume any
of these six codes changes hit-test behavior today.

Bounds are half-open: `[left, right) x [top, bottom)`. This is the same
convention GUI's `widget_hit.spl` already used; the browser hit tester's
previously-inclusive-edge convention was the one that had to migrate, and
did (`ea2e187c394`, `src/lib/gc_async_mut/gpu/browser_engine/layout.spl`) —
GUI and browser hit-testing now agree on edge inclusion.

## API surface

`pointer_event.spl` — `PointerEvent2D`: `pointer_id`, `kind` (POINTER_DOWN /
UP / MOVE / ENTER / LEAVE / OVER / OUT / CANCEL, `i32` 0-7), `x`/`y`,
`buttons`, `target`, `phase` (PHASE_NONE/CAPTURE/TARGET/BUBBLE, `i32` 0-3),
`bubbles`, `cancelable`, plus `stop_flag`/`stop_immediate_flag`/
`default_prevented`. `kind` and `phase` are plain `i32` fields rather than
enum-typed ones — an enum-typed struct field with a default is left
uninitialized by the interpreter on some construction paths, so every
construction site in this package sets every field explicitly.

`hit_proxy.spl` — `HitProxy2D.create(node_id, left, top, right, bottom)`
gives a default proxy (`PointerPolicy.Auto`, enabled, visible, zeroed paint
key); callers set the paint-key fields and policy when they matter.
`contains_point(px, py)`, `hit_tests_by_bounds()`.

`hit_test.spl` — `hit_stack(proxies, parents, x, y) -> HitTestResult`
(`primary: i64`, `hits: [HitRecord]`, `ancestor_path: [i64]`; `-1`/`[]` mean
"nothing hit" — no `Option<i64>` field, matching `NodeId.invalid()`'s
sentinel convention). `ancestor_path_of(parents, node_id)` walks a
child→parent `Dict<i64, i64>` root-to-node (public so `pointer_capture.spl`
can rebuild a path for a captured target the current point never touched).

`event_route.spl` — `EventListener2D.create(node_id, kind, use_capture,
once, handler)` where `handler: fn(PointerEvent2D) -> i32`; `kind == -1`
matches any event kind. `dispatch(mut event, listeners, ancestor_path) ->
DispatchOutcome` (`fired_node_ids`, `remaining_listeners`, `stopped`,
`stopped_immediate`, `default_prevented`).

`pointer_capture.spl` — `PointerRouter.create()`; `capture_pointer`/
`release_pointer`/`has_pointer_capture`/`capture_target`;
`effective_target(router, pointer_id, hit)`; `hover_diff(old_path,
new_path) -> HoverDiff`.

## Dispatch: capture → target → bubble

`dispatch()` walks `ancestor_path` (root-to-target, last element is the
target) in three phases, mirroring DOM `Event.eventPhase`:

1. **Capture** (`PHASE_CAPTURE`) — root through the target's parent
   (exclusive of the target itself); only `use_capture: true` listeners
   fire.
2. **Target** (`PHASE_TARGET`) — fires on the target node; both
   `use_capture` and bubble-phase listeners fire here (DOM
   `addEventListener` semantics: capture/bubble both include target).
3. **Bubble** (`PHASE_BUBBLE`) — target's parent back to root (exclusive of
   the target); only `use_capture: false` listeners fire. Skipped entirely
   when `event.bubbles == false`.

An empty `ancestor_path` (nothing hit) is a no-op that returns the listener
list unchanged. `once` listeners are dropped from `DispatchOutcome.
remaining_listeners` after firing — callers **must** use the returned array
as their new listener list (arrays are value types in this language, so
continuing to use the array passed in keeps the stale listener alive).

### stopPropagation vs stopImmediatePropagation vs preventDefault

- `stop_propagation()` blocks remaining **ancestor** nodes — the current
  node's own remaining listeners still fire.
- `stop_immediate_propagation()` additionally blocks remaining listeners on
  the **current** node (it stops firing, not registration — a
  `stopImmediatePropagation`-blocked listener is still present in
  `remaining_listeners`).
- `prevent_default()` only flips `default_prevented`; this core has no
  built-in default action to suppress (there's no click/scroll/drag
  behavior implemented here) — interpreting it is entirely an adapter's
  responsibility.

### IMPORTANT: listeners return an action code, they do not mutate the event

`EventListener2D.handler` is `fn(PointerEvent2D) -> i32`, returning an
`ACTION_*` bitmask (`ACTION_NONE=0`, `ACTION_STOP_PROPAGATION=1`,
`ACTION_STOP_IMMEDIATE=2`, `ACTION_PREVENT_DEFAULT=4`) instead of mutating
`event` via a `me` call from inside the callback. This is deliberate, not
an oversight: a listener callback lives in a different module than
`dispatch()`, and depending on a cross-module `me` mutation being visible
inside `dispatch()`'s own loop variables mid-dispatch is a confirmed
landmine class in this codebase (see
`doc/08_tracking/bug/engine2d_jit_mut_capability_chain_2026-06-05.md` — the
JIT/mut-capability chain that motivates avoiding this pattern). `dispatch()`
still writes the final stop/immediate/prevent-default state onto the
event's own fields itself (a same-function, same-module assignment) before
returning, so those fields are safe to read once `dispatch()` has returned
— but the returned `DispatchOutcome` is the authoritative result to assert
against, not a mutation observed through the original event reference.

## Pointer capture and hover diffing

`PointerRouter` tracks per-pointer-id capture/hover/press state in three
dicts (`captures`, `hover_paths`, `pressed_targets`). Every lookup goes
through `contains_key` + `[]`, never `.get()` — `Dict.get()` returns `nil`
for *present* keys on the interpreter, which would silently drop a live
capture.

`effective_target(router, pointer_id, hit)` is the routing target a caller
should dispatch to: while `pointer_id` is captured, it returns the capture
target **regardless of where the point currently is** — captured events
keep routing to their target even when the pointer moves outside every
proxy's bounds, until `release_pointer()` is called. Because a captured
target's path is independent of the current hit-test result, the caller
resolves the ancestor path via `hit_test.ancestor_path_of(parents,
effective_target(...))` rather than reusing `hit.ancestor_path` when a
capture is active.

`hover_diff(old_path, new_path)` diffs two root-to-target paths (DOM
`pointerenter`/`pointerleave`/`pointerover`/`pointerout` style) into
`entered`/`left` node-id lists plus `over_target`/`out_target` (the new/old
primary — deepest — node, `-1` when the primary didn't change).

## What is NOT here yet

This package ships only the surface-agnostic primitives. Widget, browser
DOM, and WM adapters that wire real UI trees into `hit_stack()`/`dispatch()`
are explicitly a later lane (slice item 6 of the — currently missing —
governing plan) and do not exist in the repo yet. There is no rendering
integration, no built-in default-action handling (scroll, drag, text
selection), and no coverage-buffer-based `Painted`/`Fill`/`Stroke` hit
testing.
