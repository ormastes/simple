# Browser DOM event object GC retention

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

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
