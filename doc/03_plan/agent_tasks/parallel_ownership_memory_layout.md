# Parallel Ownership and Storage Layout Agent Tasks

Merge owner: `/root`. Final reviewer: normal/highest-capability reviewer. Shared interfaces are frozen in WP-01 through WP-04: `TransferEnvelopeV1`, `StorageLayoutPlanV1`, `ParallelCommitPort`, `ResolvedParallelPolicyV1`, and `ResolvedMemoryPolicyV1`.

| Lane | Work packages | Exclusive scope | Depends on |
|---|---|---|---|
| P0 integration | WP-00..05 | shared contract roots, diagnostic/policy hubs | none |
| P1 ownership analysis | WP-10..12 | `55.borrow`, HIR boundary, MIR transfer leaves | WP-01/04/05 |
| P2 runtime transport | WP-13..18 | transfer/codec, mailbox, process, actor/channel, pool leaves | WP-01/04 |
| P3 storage | WP-20..27 | storage planner/lowering/cache/allocator leaves | WP-02/10 |
| P4 MDSOC/pilots | WP-30..36 | MDSOC adapters and isolated pilot modules | contract/runtime/layout dependencies |
| P5 evidence/docs | WP-40..44 | guides, skills, SSpec, formal/benchmark tooling | public contracts/pilots |

No lower-model sidecars are started until P0 publishes contract hashes, helper names, and fail-fast placeholders. Each lane supplies a focused test, one real integration fixture, an operator-readable documentation delta, unsupported cases, and receipt samples. The CSV work-package plan is authoritative for dependencies and acceptance gates.
