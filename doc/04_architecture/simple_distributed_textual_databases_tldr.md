# Architecture: Simple distributed textual databases — TLDR

> **Superseded 2026-10-25 (status verified against `origin/release/1.0.0` source + git log; no host execution in this check):**
> the "design only / not implemented" wording is stale. `src/app/scv/db/` now carries 53 production modules landed 2026-10-02..04, e.g.
> local store/apply/offline actor (`cc045164176`), Git settlement transport (`c1c37cef2ea`, `b08d6a2adae`), paged import/conflict/resolution (`86df09b1421`, `09b699621ec`),
> durable settlement queue + signed checkpoints (`5e8694374d9`, `56c15e77044`), GitHub provider/binding/issue bridge (`f3463704919`, `f1718d431e4`),
> CI store (`07c0edd8a58`), retention/evidence hydration (`2da1d731a2d`, `dd8b0793777`), quarantine (`3f5b25a0074`); last SCV source change `7d941093b1e` (2026-10-04).
> Lane status: L1 identity/storage PARTIAL · L2 codec/reducer/merge PARTIAL · L3 Git settlement PARTIAL, **jj/SJ orchestration OPEN** (no `jj` reference in `src/app/scv`) ·
> L4 evidence/CI PARTIAL · L5 bridge PARTIAL · L6 GitHub adapter PARTIAL (`db_github_discover_live` exists; no live designated-remote run recorded) · L7 retention/hydration PARTIAL ·
> L8 fault injection PARTIAL · L9 migration/shadow export OPEN · L10 performance evidence OPEN.
> Implemented `scv db` subcommands are `status apply inspect-patch paged-init paged-apply paged-status paged-quarantine-apply quarantine-import quarantine-inspect quarantine-apply queue-enqueue queue-status`;
> `fetch/sync/publish/settle/resolve/history/compact` remain OPEN as CLI verbs. Item-2 done gate (two-clone convergence/recovery against a designated remote, per-host path/case/Unicode/EOL/lock checks) is **OPEN**: no executed self-hosted RED/GREEN acceptance evidence beyond the 2026-10-11 focused MIR-layout regression (`doc/03_plan/evidence/seven_plans/item2_astra_mir_layout_fix_2026-10-11.md`).

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
