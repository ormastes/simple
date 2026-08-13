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

## Current execution ownership

| Lane | Current state | Next owned action | Gate before handoff |
|---|---|---|---|
| P1 ownership analysis | Partial: HIR boundary classification and MIR transfer facts exist; source-to-runtime transfer remains incomplete. | Keep dynamic/borrowed values fail-closed while connecting a real transfer receiver. | Source-to-MIR-to-runtime fixture proves one admitted transfer and one rejected raw/borrowed value. |
| P2 runtime transport | Active: scalar pool-state ABI is internal-only and bounded; public facade is deliberately not admitted. The legacy actor mailbox now has one class-backed authority shared by copied `ActorRef` and scheduler values, but that route lacks native lifecycle evidence. `ParentCommitOwnerV1` now serializes the local parent snapshot root but has no admitted child-transport execution yet. | Finish a bounded self-hosted native `PoolStateV1` callback run, then migrate the generic pool separately. Verify one actor send/ask route through the shared mailbox and one owner commit through native transport, then retire remaining copied scheduler/global authority. | Native callback result, Full-until-release, close/idle/destroy, alternate-provider execution, and one child-created result committed through the owner; no `GLOBAL_*` path may be presented as the new pool. |
| P3 storage | Partial: compiler-private AoS/SoA and capsule evidence are landed; no public transformed array claim. | Keep the typed-view pilot private until a real owner/allocation route and executable parity are admitted. | Physical plan, binding, cache/receipt identity, and native execution must agree; unsupported layouts reject. |
| P4 MDSOC/pilots | Pending downstream integration. | Route the already-frozen transfer/layout/commit policies through one real MDSOC stage. | Bypass probe fails and the stage emits the selected policy receipt. |
| P5 evidence/docs | Continuous merge-owner responsibility. | Preserve exact blocked commands and do not upgrade runtime/internal evidence into public API claims. | Every plan/guide/skill statement has a matching focused result or explicit blocker. |

P2 currently has no sidecar write authority. Its public pool facade and native SSpec
are retained only as uncommitted evidence candidates after the prior test-runner
timeout; they must not be folded into a transport or storage change without the
native callback gate above.
