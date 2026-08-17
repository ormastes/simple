# JS VM DOM bridge retention is frame-linear and property-scan quadratic

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

**Re-verified LIVE 2026-08-17 by content.**
`src/lib/nogc_sync_mut/js/engine/vm_object_store.spl` is still a flat set of
parallel arrays with no reclamation of any kind: `get_object` (line 43),
`set_property` (line 55), `get_property` (line 73) and `array_length` (line 96)
each perform a full linear scan of `prop_obj_ids`, which only ever grows —
`alloc_object` (line 31) hands out monotonically increasing ids and nothing but
an explicit `remove_property` ever shrinks the arrays. So per-generation work is
Theta(store size) and cumulative work is Theta(frames^2), exactly as filed. No
patch attempted: the fix is the bounded tracing GC this doc describes, which the
doc assigns to Root Codex and which is far outside "small change" scope.

## Status

Open. No implementation, executable spec, or production receipt is merged.
The diagnosis and bounded tracing-GC design passed high-capability review;
Root Codex owns any future implementation merge.

## Reproducer and impact

A JavaScript `requestAnimationFrame` loop that replaces
`document.body.innerHTML` retains one old DOM bridge generation per frame.
The current minimal replacement has implicit `html`, `head`, and `div` nodes:
the focused test encodes `replacement_object_count = 7`, while production
allocation logic proves **1 + 2*3 = 7** new VM objects per replacement (one
element-list object plus three element/style pairs).

The chain is:

1. `BrowserSession.advance_time` drains the rAF callback and flushes runtime
   side effects.
2. `JsInterpreter._publish_host_body_mutation` admits a new bridge generation,
   creates its objects, and adds its object/byte totals to cumulative retained
   counters.
3. Browser-session synchronization adopts that bridge for the new DOM.

Neither retained counter decreases during a document lifetime. A minimal
replacement accepts frame 4,681 at 32,767 retained objects, then rejects frame
4,682 because it would require 32,774 (about 78 seconds at 60 Hz). Later DOM
updates are silently ignored to preserve the old body.

The same path is time-superlinear. `JsInterpreter.set_object_property` scans
the monotonically growing property arrays before it writes. Existing keys
update in place, but each fresh bridge generation introduces fresh object IDs
and keys, so its writes scan an ever-larger store: retained property work is
**Theta(frames^2)** before the cap is reached.

## Exact owners

- `src/lib/gc_async_mut/web/browser_session_runtime.spl`: rAF drain and bridge
  synchronization.
- `src/lib/nogc_sync_mut/js/engine/interpreter_eval_member.spl`: host body
  mutation admission, bridge allocation, and cumulative counters.
- `src/lib/nogc_sync_mut/js/engine/vm_object_store.spl` and
  `interpreter_object.spl`: monotonically growing object IDs and fresh-
  generation property storage; existing keys update in place, and the owning
  `JsInterpreter.set_object_property` performs the reverse property scan.

Navigation and `BrowserSession.close()` discard `runtime_state`, so they release
the whole document runtime. They do not fix a long-running page animation.
rAF timer handles retire correctly and CSS animation instances are reconciled;
neither is this defect.

## Unsafe shortcuts rejected

- Do not reset the retained counters: that removes the only admission bound and
  permits unbounded retention.
- Do not free or reuse a bridge generation by DOM generation alone: detached
  elements can escape into JavaScript and must remain distinct from replacement
  elements.
- Do not rebuild the whole runtime for every body mutation: it destroys globals,
  closures, listeners, timers, and rAF continuity.

## Required scoped prerequisite

This needs VM tracing reclamation, not a bridge-local delete. Add stable object
liveness metadata and sweepable property storage without remapping live IDs;
track environment parents/liveness and function records; then mark every
interpreter-owned `JsValue`/function/environment root: global bindings and
global values, call frames (including `this` and returns), `return_value`,
`thrown_value`, object/array properties, functions and closure environments,
host DOM roots, timer/async/promise work, listeners, prototypes, bound/native/
wasm caches, and Node require-cache values. Sweep only at a post-callback/
post-microtask safe point after a committed bridge replacement. Preserve every
marked detached element and callback identity. Existing byte/node admission
limits remain DoS bounds, but report current live counts rather than cumulative
allocation totals.

## RED SSpec and performance acceptance

Add a focused SSpec with these exact steps:

1. `Create bounded animation work` — a 256-frame rAF chain replaces one body
   child; retain the pre-replacement element and one callback/listener.
2. `Advance many frames` — advance deterministic 16 ms ticks and prove all 256
   callbacks ran, the retained detached element remains distinct/readable, and
   the current element/listener still works.
3. `Release navigation state` — navigate to a new document, then close.
4. `Verify retained counts and RSS/operation bounds` — live object/property
   counts plateau at the current bridge plus the explicitly retained detached
   element, callback, and listener roots; new-document counts start clean and
   close clears the runtime. A production perf companion runs N and 2N frames,
   records RSS delta for the NFR receipt (report-only until a selected numeric
   RSS threshold exists), and gates 2N elapsed time at no worse than 2.2x N.

Use live-object/live-property metrics, not monotonic `next_id`. The current
test that expects the cap to reject a second replacement is regression evidence
for this bug, not proof of lifecycle correctness.
