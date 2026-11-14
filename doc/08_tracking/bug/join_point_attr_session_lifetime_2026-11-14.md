# Join-point attribute rows survive their build session

Status: source fix implemented; native verification pending. No runtime crash
reproduction or full compiler-session qualification is claimed.

Inspection of release `06e03560053` found a module-global attribute dictionary
without a reset hook. HIR lowering records path/name keys and attribute arrays;
ordinary allocations made during a live core-C build session belong to that
session. BuildSession successfully frees that allocation list, but its reset
list did not invalidate this registry. Subsequent lookup can inspect stale rows.
The feature branch also adds proof-epoch rows, which need the same ownership edge.

The source fix adds scalar invalidation immediately after successful heap end.
Failed teardown preserves live rows. Getters check the scalar before any
registry graph access; unavailable metadata returns empty/unproven results.
Registration refuses until the real lowering owner begins a new epoch. That
begin operation refuses active or paused transient scopes, replaces stale slots
without reading them, and retains monotonically increasing source epochs.

This relies on the inspected serialized native LLVM/Cranelift + core-C direct
store and explicit-root collection semantics described in
`doc/05_design/compiler/aspect_session_core_c_lifetime_audit_2026-11-14.md`.
It is not an alternate-runtime/concurrent-reader proof. Existing attribute
payloads can still originate in module scratch; their ownership is a separate
unresolved gap. This fix does not claim general scope-exit safety.

Authored, unrun evidence:

- `test/fixtures/join_point_attr_session/main.spl`: actual two native heap
  sessions, stale-row absence, new epoch/attributes, active and paused scope refusal.
- `test/01_unit/compiler/aop/join_point_attr_session_lifetime_spec.spl`: actual
  BuildSession.end_with with failed/successful injected heap-end outcomes.

No native build was authorized for this checkpoint. The canonical bug shard is
`join_point_attr_session_lifetime_2026-11-14` and remains waiting for verification.
