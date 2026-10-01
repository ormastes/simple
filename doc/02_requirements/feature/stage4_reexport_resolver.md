<!-- codex-design -->
# Stage4 re-export resolver requirements

## Selected design

Option A: a resolver cache owned by an immutable `ModuleSurfacesByName`
snapshot, with an explicit `snapshot_generation` and a local DFS active set.

## Requirements

- REQ-001: repeated root lookup of `(facade_name, wanted)` against one
  snapshot must return its completed positive or negative result without a
  second graph traversal, regardless of which HIR lowering instance asks.
- REQ-002: a new module-surface snapshot must never reuse entries created for
  an earlier snapshot.
- REQ-003: cyclic re-export paths must terminate, while alternate positive
  paths remain discoverable.
- REQ-004: HIR lowering must not expose the cache as mutable per-module state;
  only DFS active-path state may be local to a lookup/lowering.
