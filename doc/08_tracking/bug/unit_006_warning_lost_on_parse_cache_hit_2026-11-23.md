# SPL-UNIT-006 warning not re-raised on parse-cache hit (2026-11-23)

Status: verification-pending

## Symptom
When a module that redeclares a `unit` with different bounds is served from the
parse cache, its `SPL-UNIT-006` ("declared again with different bounds")
warning is not reported again. A cold parse reports it; a warm run is silent.

## Mechanism
- The conflict is queued only as a side effect of parsing:
  `unit_constraint_register` (`src/compiler/10.frontend/core/unit_constraint.spl:155`),
  called from `_ParserDecls/enum_module_body.spl`.
- The driver drains it per owner (`unit_constraint_drain_conflicts_for`) and
  prints it in `src/compiler/80.driver/hir_typecheck_consumer_v1.spl:97-102`.
- A parse-cache hit skips the parser, so nothing calls
  `unit_constraint_register`, nothing is queued, and the drain finds nothing.
  The registry bounds themselves are also not rebuilt from the cached AST.

## Fix direction
On a cache hit, replay `unit_constraint_register` for every cached unit
declaration that has bounds (in declaration order). That rebuilds the registry
and queues the conflicts again. Alternatively, store the drained conflict list
with the cache entry and replay it. Add a repro spec that parses the same file
twice with the cache enabled and expects the warning both times.

## Why not fixed in the Dist / i64 change
That change is limited to MIR operator lowering. This bug is in the
frontend/cache layer and needs its own cache-replay design and spec.

## Fix (2026-11-23)
The cold parse stores the conflicts it queued for the module in a
`<key>.u006` sidecar next to the private parse-cache entry
(`frontend_parse_cache_store_unit_conflicts`, atomic write, no locks). Every
cache-hit path in `frontend_parse_or_restore` (spab, fpc, shared) re-queues
them under the module path (`unit_constraint_requeue_conflicts`). A clean
reparse clears a stale sidecar. Limit: a shared-CAS hit on a host that never
parsed the module cold has no local sidecar, so it stays silent there.
Repro spec: `test/01_unit/compiler/frontend/unit_conflict_parse_cache_replay_spec.spl`.
