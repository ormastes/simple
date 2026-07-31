<!-- codex-architecture -->
# CSS Animation Lifecycle Safety Architecture

Status: **PROPOSED / RED — contract only; candidate `47df593f600` remains
rejected and no lifecycle-event implementation or runtime evidence is
admitted.**

## Scope and rejection boundary

The current `origin/main` renders CSS animation frames but does not dispatch
`animationstart`, `animationiteration`, `animationend`, or `animationcancel`.
This design adds the missing lifecycle boundary without changing the canonical
web semantic/layout -> `DrawIrComposition` -> Engine2D route. Draw IR remains a
render description and must not retain DOM targets, event cursors, queues, or
JavaScript objects.

Candidate `47df593f600` must not be replayed or partially merged. It is based on
`20afc4de0c6`, not current origin, and has five blocking defects:

- animation ownership transfers through reserialized `path:<ordinal>` text, so
  replacement at the same path can inherit stale lifecycle state;
- one target maps to one instance and `animation_order` is always zero, so an
  animation list cannot have independent identities;
- ordering state converts authored counts and elapsed time through `f64` and
  rounded milliseconds before dispatch;
- a 4,096-event drain limit bounds work per call but the heap itself has no
  capacity and can retain stale per-boundary tasks;
- detached targets are retained as whole node snapshots without a
  document/node-generation contract, so cancel, restart, replacement, and
  release cannot be proved independently.

The already-landed equal-`innerHTML` restart and animation property-index
optimization are outside this change. This contract must compose with them; it
must not reimplement either lane.

## Ownership and frozen identities

The DOM owner assigns identity. The animation sampler may consume it but may
not derive identity from HTML paths, `id` attributes, array positions, or
serialized markup.

```text
BrowserDomGenerationIdentity(
    document_generation:i64,
    node_id:i64,
    node_generation:i64
)

BrowserCssAnimationIdentity(
    target:BrowserDomGenerationIdentity,
    animation_slot:i32,
    animation_generation:i64
)
```

`document_generation` advances before navigation installs a new document.
`node_generation` is assigned when the DOM owner creates a node and never
wraps or transfers to a replacement; exhaustion retires the source ID.
Reparenting preserves node identity. Reparse, `innerHTML` replacement, and a
new element with the same path or author `id` receive a new node generation.
`animation_slot` is the computed animation-list position. The slot is not a
complete identity: `animation_generation` advances whenever reconciliation
creates a new animation effect in that slot and never wraps.

The session owns a minimal `BrowserDomEventTargetHandle` for each live or
retiring animation generation. It contains the generation-qualified DOM
identity and the canonical JS event-target handle/listener ownership needed by
the existing dispatcher. It must not retain a serialized path, a full detached
subtree, or a second listener table.

### Current-origin identity owner map

Current source has reusable event-delivery mechanics, but no identity that can
safely produce `BrowserDomEventTargetHandle`. The exact owners are:

- `src/lib/gc_async_mut/gpu/browser_engine/dom.spl` owns
  `BeDomNode.node_id`, but it owns no document or node generation.
- `html_tree_builder_build_with_parse_limits` in
  `src/lib/gc_async_mut/gpu/browser_engine/html_tree_builder.spl` initializes
  `next_node_id` to `1` on every parse. `BrowserSession._replace_current_body_children`
  in `src/lib/gc_async_mut/web/browser_session_runtime.spl` reparses body HTML
  and grafts those children into the live document. A replacement can therefore
  reuse the detached node's raw ID inside the same document.
- `be_dom_event_identity` and `be_dom_route_identity` in
  `src/lib/gc_async_mut/gpu/browser_engine/dom_accessors.spl` expose mutable
  author `id` or `route-node:<node_id>` text. Neither value is a lifetime
  identity, and neither may key an animation cursor or detached event.
- `ui_access_revision` is owned by `BrowserSession` and appears with
  `node_id` in `browser_session_ui_access.spl`. It is a snapshot/action stale
  guard: title and unrelated UI-visible changes advance it, and its counter
  saturates. It is not a stable per-node generation.
- `BrowserRuntimeState.dom_bridge_generation` mirrors one interpreter-wide
  bridge rebuild counter. It is not document-qualified or per-node, and direct
  `bind_dom` callers can rebuild mappings without creating the required node
  lifetime identity.
- `BrowserRuntimeState._bind_dom_node`, `bind_dom`, and `adopt_dom_bridge` in
  `src/lib/gc_async_mut/web/browser_session.spl` own the current parallel
  `dom_node_ids -> dom_element_ids` mapping. `BrowserDomCallableListener` owns
  callbacks by raw JS `target_object_id`.
- `_browser_session_object_id_for_node`,
  `_browser_session_callable_dispatch_root`, `BrowserDomEventExecutor`, and
  `BrowserSession._dispatch_dom_event_with_payload` in
  `src/lib/gc_async_mut/web/browser_session_runtime.spl` are the canonical
  event consumers. They already own listener lookup, CSP policy,
  capture/bubble order, JavaScript callback execution, and side-effect flush;
  lifecycle work must reuse them.
- `BrowserCssAnimationInstance` and `_simple_web_animation_target_keys` still
  identify one animation per serialized `path:<ordinal>`. They are consumers
  of the future identity contract, never producers of DOM identity.

Raw `node_id`, `ui_access_revision`, and `dom_bridge_generation`, alone or in
an ad-hoc tuple, are explicitly forbidden as substitutes for
`BrowserDomGenerationIdentity`.

### Required producer/consumer order

Implementation remains blocked until these prerequisites land in order:

1. The DOM owner produces nonwrapping `document_generation` and
   `node_generation` values at document/node creation, preserves node
   generation across reparenting, and assigns a new generation on replacement.
2. `BrowserRuntimeState` produces `BrowserDomEventTargetHandle` while binding
   the canonical JS target object. The handle combines the DOM identity with
   that exact `target_object_id`; no path lookup creates a handle later.
3. `BrowserSession` consumes the handle through its existing event dispatcher.
   Connected dispatch first verifies all generations and resolves the live
   path; disconnected cancel dispatch uses the retained old target in target
   phase only.
4. Only then may animation-list reconciliation consume the handle and create
   generation-qualified lifecycle cursors. Rendering continues to consume
   animation samples and never becomes an identity or event owner.

Until steps 1-3 exist with focused stale-reuse and release tests, lifecycle
source, runtime, and acceptance status remain **RED**.

## Exact time and bounded lifecycle state

Lifecycle ordering uses canonical integer ticks. No queued record contains a
`f64` time.

```text
BrowserCssAnimationTime(ticks:i64)
BrowserCssIterationCount(coefficient:u64, decimal_scale:u32, infinite:bool)

BrowserCssAnimationLifecycleCursor(
    identity,
    target_handle,
    animation_name,
    pseudo_element,
    start_boundary,
    duration_ticks,
    delay_ticks,
    iteration_count,
    start_emitted,
    next_iteration:u64,
    terminal_kind,
    terminal_emitted
)

BrowserCssAnimationEventRecord(
    identity,
    kind,
    boundary,
    elapsed_ticks,
    document_order,
    animation_slot
)
```

Durations and delays are normalized once by the CSS value owner to checked
integer ticks. The finite decimal iteration token is retained as exact
coefficient/scale data and reduced before checked multiplication/division.
Overflow saturates only to the explicit infinite/terminal sentinel; it never
wraps or orders through `f64`. `AnimationEvent.elapsedTime` converts
`elapsed_ticks` to JavaScript Number seconds only while materializing the event
object, after ordering and cursor mutation are complete.

The session owns at most 4,096 live animation effects and 4,096 retiring
cancel cursors. `BrowserCssAnimationEventQueue` is a fixed-capacity ordered
queue of at most one head record per cursor (maximum 8,192 records). A large
clock jump advances `next_iteration` after each dispatch and materializes only
the next due record; it never expands missed iterations into a task array.
One host turn dispatches at most 4,096 lifecycle events. Remaining work stays
in the cursor and resumes on a later explicit host turn, without recursion,
same-turn polling, prefix copies, or a second heap. Capacity/invariant failure
is fail-closed before admitting a new effect and emits one bounded warning.

Ordering is `(boundary, document_order, animation_slot, generation,
kind_rank)`. At one boundary, cancellation of an old generation precedes the
start of its replacement. Start precedes end for a zero-duration generation;
the terminal boundary never also emits `animationiteration`.

## Reconcile, cancel, restart, and detach

The lifecycle owner reconciles the complete computed animation list against
generation-qualified identities:

- a retained matching effect keeps its generation; play-state and supported
  timing updates change its cursor without inventing a restart;
- removing/replacing an animation name queues exactly one cancel for the old
  generation; a new effect receives a new generation and start cursor;
- finishing emits exactly one end; later style removal does not also cancel;
- pause emits no lifecycle event and freezes local active time; resume
  continues the same generation;
- detaching a live target queues cancel for the old target handle. If the node
  is disconnected when dispatched, the event is target-phase only and cannot
  bubble through a replacement or its ancestors;
- reinserting the same node starts a new animation generation. Replacing it at
  the same path or with the same author `id` cancels the old generation and
  starts the new target independently;
- navigation and close invalidate the document generation and clear cursors,
  target handles, and queued records without dispatch into the destroyed
  realm.

Event delivery must extend the canonical `BeDomEvent` payload and existing
`BrowserSession` DOM dispatcher. It must not add a private callable-listener
dispatcher. Listener mutations, capture/bubble order, CSP inline-handler
policy, and side-effect flushing therefore remain owned by the current event
path.

## Deterministic SSpec contract

The primary modern SSpec is
`test/02_integration/rendering/browser_session_css_animation_event_lifecycle_spec.spl`.
Its displayed scenario uses these exact steps:

1. `Open the scripted CSS animation lifecycle fixture`
2. `Advance the monotonic clock across exact iteration boundaries`
3. `Cancel and restart the animation through the DOM bridge`
4. `Observe ordered animation events and canonical Draw IR frames`

Frozen helpers are
`setup_scripted_css_animation_lifecycle_fixture`,
`check_css_animation_event_log`, and
`check_css_animation_draw_ir_frame`. Until the implementation exists, any
executable placeholder must call
`fail("RED: generation-safe CSS animation lifecycle is not implemented")`.

The fixture uses a 100 ms, three-iteration animation. It proves the exact log
`animationstart,animationiteration,animationcancel,animationstart,animationiteration,animationiteration,animationend,`,
checks start/base/restart/terminal Draw IR colors at exact clock boundaries,
and verifies an extra tick/render emits no duplicate event. Separate hidden
cases replace a target at the same path/`id`, detach and reinsert it, exercise
two animation slots, jump across many iterations while checking queue/cursor
caps, and prove navigation/close release all retained handles.

## Acceptance boundary

Static source review cannot promote this design. Acceptance requires the
modern SSpec plus unit coverage for identity reuse rejection, exact-time
ordering, zero/fractional durations, bounded clock jumps, cancellation before
restart, disconnected-target dispatch, and terminal reclamation. Generated
manuals must be current with zero stubs. Runtime, bootstrap, performance,
aggregate HTML/CSS, and full-browser PASS remain separate gates.
