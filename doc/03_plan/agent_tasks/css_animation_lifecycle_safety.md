# CSS Animation Lifecycle Safety Agent Plan

Status: **PROPOSED / RED — docs-only safety contract; rejected candidate
`47df593f600` is not an implementation base.**

## Frozen shared contract

All lanes follow
[`css_animation_lifecycle_safety.md`](../../04_architecture/css_animation_lifecycle_safety.md).
The primary interfaces are:

- `BrowserDomGenerationIdentity`
- `BrowserCssAnimationIdentity`
- `BrowserCssAnimationTime`
- `BrowserCssIterationCount`
- `BrowserCssAnimationLifecycleCursor`
- `BrowserCssAnimationEventRecord`
- `BrowserCssAnimationEventQueue`
- `BrowserDomEventTargetHandle`

No lane may use serialized path/author `id` identity, hard-code one animation
slot, store ordering time as `f64`, enqueue one task per missed iteration,
retain a detached subtree, or create a parallel DOM listener dispatcher.

Frozen modern SSpec helpers:

- `setup_scripted_css_animation_lifecycle_fixture`
- `check_css_animation_event_log`
- `check_css_animation_draw_ir_frame`

Incomplete helpers fail with
`fail("RED: generation-safe CSS animation lifecycle is not implemented")`.

Frozen displayed manual steps:

1. `Open the scripted CSS animation lifecycle fixture`
2. `Advance the monotonic clock across exact iteration boundaries`
3. `Cancel and restart the animation through the DOM bridge`
4. `Observe ordered animation events and canonical Draw IR frames`

## Mandatory identity prerequisite

Current origin has no safe producer for `BrowserDomEventTargetHandle`:

- `BeDomNode.node_id` is raw and is reused because the HTML tree builder starts
  IDs at `1` on every parse, including body replacement;
- `ui_access_revision + node_id` is a saturating UI snapshot/action stale
  guard, not a stable document/node lifetime;
- `dom_bridge_generation` is one bridge-wide mutation scalar, not a
  document-qualified per-node generation;
- `BrowserRuntimeState.dom_node_ids -> dom_element_ids` and
  `BrowserDomCallableListener.target_object_id` are the existing canonical JS
  target mapping, but the raw object ID has no DOM generation contract.

The smallest safe reuse is the current `target_object_id` and canonical
`BrowserSession._dispatch_dom_event_with_payload` behavior, wrapped only after
the missing producer exists. Work must proceed in this exact order:

1. **G0 DOM producer:** the DOM owner adds nonwrapping document/node
   generations and proves same-path/same-author-`id` replacement receives a
   distinct identity while reparenting preserves identity.
2. **G1 handle producer:** `BrowserRuntimeState._bind_dom_node` creates
   `BrowserDomEventTargetHandle(identity, target_object_id)` at canonical JS
   target binding time and retains no path or subtree snapshot.
3. **G2 handle consumer:** BrowserSession validates generations, resolves a
   connected target, and reuses the existing listener/CSP/capture/bubble/flush
   dispatcher; a disconnected old target is target-phase only.
4. **G3 lifecycle consumer:** animation-list reconciliation may consume the
   verified handle and build bounded cursors/events. It may not reconstruct
   identity from layout paths.

G1-G3 must not start from candidate `47df593f600`. If G0-G2 cannot remain
within reviewed owner boundaries, stop and return to architecture review rather
than hiding identity work inside the animation renderer. Source, executable
SSpec, runtime, and acceptance status remain **RED**.

## Parallel implementation lanes

| Lane | Scope and owner boundary | Depends on |
|---|---|---|
| A: DOM identity | G0 DOM-owned document/node generations; replacement, reparent, detach, and realm teardown rules | frozen contract |
| B: exact lifecycle core | checked integer time, exact decimal iteration count, generation cursor, one-head-per-cursor fixed queue, ordering and caps | frozen contract |
| C: target handle + animation-list reconciliation | G1 handle production plus complete slot identities and old/new generation decisions; no path transfer and no same-`innerHTML` reimplementation | A and B interfaces |
| D: canonical event integration | G2/G3 handle consumption, `BeDomEvent` payload, existing BrowserSession dispatcher, target-only detached delivery, and bounded continuation | A–C |
| E: modern SSpec | unit identity/time/queue cases and the frozen integration scenario with semantic event log plus canonical Draw IR oracle | frozen helpers; final assertions depend on A–D |
| F: manuals and traceability | docgen output, zero-stub review, REQ mapping, and explicit evidence limits | E settled |

A and B may run in parallel. C may draft against the frozen identities while A
is active. E may create only fail-fast scaffolding until A–D merge. D is the
single integration owner; other lanes must not edit the BrowserSession event
executor concurrently.

## Merge and review protocol

1. Merge owner: root normal/highest-capability browser owner.
2. Sidecars: N/A for A–D because identity, detached-target ownership, timing,
   and event reentrancy are safety-critical. A lower-model sidecar may update
   generated-manual bookkeeping only after E is final.
3. Merge order: A and B, then C, D, E, F. The merge owner resolves all shared
   type and BrowserSession conflicts.
4. Final reviewer: independent highest-capability reviewer checks current
   origin, full animation-list identity, exact ordering time, hard queue/cursor
   caps, cancel/restart/detach semantics, canonical dispatch reuse, and manual
   traceability.
5. The rejected candidate may be read as negative evidence only. No cherry-pick
   or copied scheduler/session block is allowed without line-by-line redesign
   against the frozen contract.

## Done conditions

- Same path/author `id` replacement cannot inherit an old cursor or listener
  target.
- Every computed animation slot has an independent, nonwrapping generation.
- Ordering and cursor state contain no `f64`; JS Number conversion happens only
  at event materialization.
- Live plus retiring cursors are bounded, the event queue holds at most one
  record per cursor, and a large clock jump cannot allocate per-boundary tasks.
- Start/iteration/end/cancel each emit exactly once with cancellation ordered
  before same-boundary restart.
- Pause/resume retains generation; finish never later cancels.
- Detach dispatches only to the old target and cannot bubble through a
  replacement; navigation/close release the destroyed realm without dispatch.
- JavaScript lifecycle callbacks mutate semantics before the next canonical
  Draw IR frame; Draw IR owns no lifecycle/event state.
- The frozen modern SSpec and hidden identity/list/time/cap/release cases pass,
  their generated manuals contain zero stubs, and independent review accepts
  the result.

Until all conditions hold, animation lifecycle and the broader HTML/CSS goal
remain RED. This plan authorizes no bootstrap, runtime, release, or push.
