# Collection planner — TLDR

Item 3 remains incomplete: typed registry/advisory planning and checked numeric
TypedSeries adapters exist; general typed query lowering and native host/NFR
qualification remain open. Read source facts and dated status in the
[architecture](collection_planner.md), not this summary as execution evidence.

- Resolved typed operations feed logical plans, semantic proof, physical cost
  selection, verified MIR lowering and observed execution. Those are separate
  admission stages; unknown facts retain Original.
- Preserve callbacks/effects/errors, missing values, key equality, duplicate
  multiplicity, order, alias/mutation/escape and suspension behavior.
- [Common backend capabilities](compiler/collection_backend_capabilities.md)
  bind Item 7 representations and async resource/index owners. Algorithm,
  provider/progress, column layout and workload feedback remain separate.
- Keep both sync/async DataFrame family APIs and checked typed adapters.
  Admission covers old/new/retired memory, stable entry references and retained
  owners; lockless maps do not automatically make a join index appropriate.
- Prepare registries/profiles once per admitted snapshot; no hot-path profile
  I/O/scans. Invalidate decisions on source, callee, target, type/equality,
  backend, layout, policy or admitted profile changes.
- [Detail design](../05_design/collection_planner.md),
  [existing tests](../03_plan/sys_test/collection_planner.md), and
  [shared CBC TDD gates](../03_plan/sys_test/collection_backend_capabilities.md).
