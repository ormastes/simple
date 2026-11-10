---
id: event_api_spec_dispatch_route_api_drift_2026-11-10
status: open
severity: low
discovered: 2026-11-10
discovered_by: P3 interpreter-lane triage of browser_script_crossmodule_mutation_breaks_timer_event_2026-07-11
related: test/01_unit/browser/script/event_api_spec.spl
related: src/lib/gc_async_mut/gpu/browser_engine/script/event_api.spl
---

# event_api_spec "Dispatch" example references an unimplemented typed-route API

`test/01_unit/browser/script/event_api_spec.spl` (describe "Event API -
Dispatch") calls four functions that do not exist anywhere in `src/`:

- `_event_api_index(root)`
- `_event_api_route(index, id)`
- `event_dispatch_route(root, index, target_route, related_route, ev)`
- `event_dispatch_target_author_id(index, dispatch)`

Every other example in the spec passes (8/9); this example fails at semantic
time with `semantic: function '_event_api_index' not found`, which also forces
the whole spec file outcome to ERROR.

The spec documents an intended "typed routes + projected author ids" dispatch
layer on top of the event API. Either implement the four functions in
`src/lib/gc_async_mut/gpu/browser_engine/script/event_api.spl` (and export
them), or rewrite the example against the dispatch primitives that actually
ship (`event_create` / listener registration / DOM projection).

Evidence (2026-11-10, deployed Windows Rust seed, worktree work/p3-interp-20261110):
`Results: 9 total, 8 passed, 1 failed`; failing example
"dispatches typed routes and projects author ids on demand".
