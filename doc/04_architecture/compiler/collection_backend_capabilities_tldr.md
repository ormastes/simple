# Collection backend capabilities — TLDR

Selected design refinement, not an implemented API or native qualification.

- DataFrame/query operations, Linear/Hash/Ordered representation, native/pure
  provider, progress guarantees, column layout and workload profiles are
  independent choices. `.sprof` target identity is not lockless capability.
- One proposed `CollectionCapabilitiesV1` under common contracts describes
  operations, exact key/value semantics, lifetime, limits, per-operation
  progress, measurement and directed migration support. Existing async/resource
  and storage-layout owners supply result/ref/layout contracts.
- Make static-only, no-capture, constructor-only, unsupported and live-switch
  capabilities explicit. No new annotation syntax is claimed. Explicit strict
  requirements fail if unsupported; advisory Auto may keep Original.
- DashMap and the legacy native registry use locks. Active legacy profiling
  also uses a lock; strict hot paths must disable it or qualify another path.
- Preserve DataFrame masks/types/strides/order/duplicates and callback/error
  behavior. Admit old+new+retired memory before conversion; retain qualified
  views and stable entry identity. No raw pointer or bucket identity crosses
  backend selection, serialization or suspension.
- Cache decisions bind type/source/equality/target/provider/layout/policy and
  admitted profile. Ready access performs no profile file reads or global scans.
- [Full contract](collection_backend_capabilities.md),
  [TDD matrix](../../03_plan/sys_test/collection_backend_capabilities.md),
  [async architecture](../language/async_infrastructure.md). Native evidence
  remains OPEN; existing defaults and seven-item host statuses are unchanged.
