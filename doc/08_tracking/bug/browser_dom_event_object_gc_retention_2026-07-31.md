# Browser DOM event object GC retention

Status: **RED — reachability reclamation is not implemented**

## Scope

`BrowserSession` creates a distinct JavaScript event object whenever a host
event reaches a callable listener. Page code may retain that object, so deleting
or reusing it immediately after dispatch would violate JavaScript semantics.

The bounded mitigation now registers the three receiver-based event-control
natives once per `BrowserRuntimeState` and replaces the existing global `event`
slot. This removes duplicate native-function, native-map, and global-slot growth
without pretending to reclaim event objects.

## Reproduction and evidence

Run the focused scenario:

`test/02_integration/rendering/browser_session_event_retention_spec.spl`

After one warm event, repeated same-document listener dispatches must add zero
function records, zero native mappings, and zero global-name slots. The scenario
also asserts that `object_store.obj_proto_ids` still grows, keeping this bug RED.

## Required root fix

Implement reachability-aware object reclamation for the JavaScript VM. Roots
must include globals, environments, call frames, pending callbacks/promises,
timers, host bindings, and listener registries. Reclaim only objects proven
unreachable; navigation and `BrowserSession.close()` remain coarse cleanup.

## Fix landed 2026-11-05 (work/libbug-w6-domevent-20261105)

Status: **mitigation superseded — reachability reclamation implemented**

- `src/lib/nogc_sync_mut/js/engine/vm_object_store.spl`:
  `ObjectStore.collect_unreachable(root_obj_ids)` marks from roots and
  transitively through property values and prototype slots, drops property
  slots of unmarked objects, and recycles their ids through a `free_object_ids`
  list consumed by `alloc_object()`. Ids are never renumbered, so all
  outstanding references stay valid across a collection.
- `src/lib/nogc_sync_mut/js/engine/interpreter_object.spl`:
  `JsInterpreter.collect_garbage()` enumerates the full root set required
  above — globals (latest binding per name wins), environments, call frames,
  pending callbacks/promises, timers, host bindings (window/document/body/
  element/style ids, well-known prototypes), and listener registries.
- `src/lib/gc_async_mut/web/browser_session_runtime.spl`: reclamation runs at
  the event-loop quiescence point — after each outermost
  `_dispatch_dom_event_route_with_payload` unwinds (`_reclaim_unreachable_event_objects`),
  never during dispatch. Navigation and `BrowserSession.close()` remain
  coarse cleanup.
- Evidence: `test/01_unit/lib/nogc_sync_mut/js/engine/object_store_reachability_reclamation_spec.spl`
  (orphan reclaimed, rooted/chained objects survive, id reuse);
  `test/02_integration/rendering/browser_session_event_retention_spec.spl`
  now asserts the object heap stays flat across repeated dispatches while the
  page-retained latest event survives.

Known residual: on origin/release/1.0.0 the JS listener registration path is
independently degraded (element objects served by `getElementById` lack the
bound `addEventListener`, and document-level listeners are not in the
callable dispatch path), so the integration scenario's per-dispatch
allocations are not observable end-to-end under the phase1 seed binary; the
unit spec carries the RED→GREEN evidence for the reclamation itself.
