# Architecture: Simple distributed textual databases — TLDR

This design adds a local-first SCV semantic database over Git/jj without adding an always-on database server. Offline replicas create signed typed patches and provisional IDs; one fenced Git settlement authority validates them and assigns permanent compact aliases. GitHub is the first live Git/CI adapter, while provider-neutral contracts keep other Git and CI servers compatible.

## Core Shape

- `EntityRef` preserves canonical SCV identity and adds namespace/epoch/kind-scoped compact aliases; `IdentityMap` owns permanent aliases, high-water marks, accepted batches, merge links, and tombstones.
- `DbPatch` enters a provider-free `MergePolicy`/reducer only after signature, ACL, schema, causal-base, quota, and reference validation.
- `SettlementSubject` signs candidate tree digest, expected parent, namespace/epoch, allocator state, batch, schema/reducer, and prior subject—never its own commit OID. A post-publication `AcceptedCommitBinding` records the verified commit OID outside that commit.
- The SJ lease/capsule is the only local writer. Network/provider waits occur after durable intent is recorded and the lease is released.
- `RevisionRef<T>` pins configuration, reproduction, test-definition, expectation, and evaluation relationships to immutable revision digests.
- `BridgeDelivery` connects CI/bug providers through durable intent, uncertain-effect read-back, cursors, and loop prevention. `RetentionCatalog` separates durable semantic Git from raw evidence CAS.

## Operational Notes

- startup: open the last verified local checkpoint/receipt and incrementally replay local accepted batches; remote fetch and capability verification occur only during explicit `fetch`/`sync`/`settle` operations.
- hot path: resolve settled integers through materialized indexes; deduplicate bounded CI bundles before patch construction; never scan Git history or shell out per query.
- cache/index: alias, accepted-batch, provider-event, current-status, rollup, and archive-closure indexes are rebuildable projections, not authority.
- invalidation: settlement head/schema/reducer changes invalidate affected projections; provider cursors advance only after durable canonical acceptance.
- perf/RSS: selected Operating B requires 1M aliases/observations, query p95 ≤100 ms, 10k import ≤5 s and ≤256 MiB, and a ten-year semantic Git pack/full clone ≤2 GiB.
- residual risk: Git branch protection constrains ordinary writers, not administrators. Signed chained receipts detect rollback or equivocation only after divergent views are compared; ambiguous recovery creates a new namespace.

## Open Next

- [Full architecture](simple_distributed_textual_databases.md)
- [Detail design](../05_design/simple_distributed_textual_databases.md)
- [Implementation plan](../03_plan/agent_tasks/simple_distributed_textual_databases.md)
- [System-test plan](../03_plan/sys_test/simple_distributed_textual_databases.md)
- [Executable acceptance design](../../test/03_system/app/scv/feature/simple_distributed_textual_databases_spec.spl)
