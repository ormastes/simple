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
| P2 runtime transport | Active: scalar pool-state ABI is internal-only and bounded; public facade is deliberately not admitted. The legacy actor mailbox now has one class-backed authority shared by copied `ActorRef` and scheduler values; each reference retains its admitting scheduler for send/ask/stop, its mailbox and ready queue have bounded/cursor storage, and `ask()` reserves reply capacity through completion until consume/cancel. It still lacks typed/native lifecycle evidence. `ParentCommitOwnerV1` serializes the local parent snapshot root. Its bounded copied-frame inbox now has an existing stdout reader: children encode validated result frames as `SPRF1` armored text, and the parent reassembles lines, enforces a per-reader line budget, decodes and validates the frame, then applies normal inbox backpressure. The source/system gate exists, but no self-hosted native verdict admits child execution yet. | Run the self-hosted native parent-result gate first; only then admit one child-created result through owner commit. Verify actor ask cancellation/close cleanup in a native lifecycle gate. Finish a bounded self-hosted native `PoolStateV1` callback run before a separate generic-pool migration. | `<self-hosted-simple> test test/03_system/feature/language/parent_commit_piped_result_spec.spl --mode=native` must prove a child result is received and committed by the parent. Actor ask needs a native bounded reservation/cancellation/close receipt before handoff. Pool handoff separately requires native callback result, Full-until-release, close/idle/destroy, and alternate-provider execution; no `GLOBAL_*` path may be presented as the new pool. |
| P3 storage | Partial: compiler-private AoS/SoA and capsule evidence are landed; no public transformed array claim. | Keep the typed-view pilot private until a real owner/allocation route and executable parity are admitted. | Physical plan, binding, cache/receipt identity, and native execution must agree; unsupported layouts reject. |
| P4 MDSOC/pilots | Pending downstream integration. | Route the already-frozen transfer/layout/commit policies through one real MDSOC stage. | Bypass probe fails and the stage emits the selected policy receipt. |
| P5 evidence/docs | Continuous merge-owner responsibility. | Preserve exact blocked commands and do not upgrade runtime/internal evidence into public API claims. | Every plan/guide/skill statement has a matching focused result or explicit blocker. |

P2 currently has no sidecar write authority. Its public pool facade and native SSpec
are retained only as uncommitted evidence candidates after the prior test-runner
timeout; they must not be folded into a transport or storage change without the
native callback gate above.

## WP-18 bounded pool handoff sequence

The current `src/lib/nogc_async_mut/thread_pool.spl` is not a migration
target: it copies `ThreadPool` values through `GLOBAL_POOLS`, retains global
callback/result arrays, and resolves invalid pool IDs by fallback. Do not
incrementally decorate that authority with a new API. The first admitted pool
slice is runtime-internal and scalar-only: a function pointer plus inline
`i64` input/result, never a captured closure or heap graph.

| Step | Owner and scope | Required result | Fail-closed gate |
|---|---|---|---|
| 18.1 | runtime pool providers and registration surfaces | Generation- and kind-tagged state/task handles; registry acquisition pins lifetime. | Stale, forged, cross-kind, release/destroy-race handles return Invalid without dereference. |
| 18.2 | same runtime owner | `try_submit_i64(state, entry, input)` reserves one credit through completed-but-unreleased state; completion publishes result before idle. | Full, Closed, Invalid, and success are distinct; schedule failure rolls back handle and counters. |
| 18.3 | both shipped C provider lanes plus Rust/interpreter/ELF symbol maps | One ABI/status-vector contract; interpreter is explicitly unsupported rather than a success stub. | Provider-parity tests exercise the same vectors, including zero payload and 100k sequential reuse. |
| 18.4 | private Simple owner leaf | `PoolStateV1` wraps only the opaque state handle; task receipt has checked terminal status plus scalar result and release. | Native Simple callback proves descriptor ABI, Full-until-release, close/idle/destroy, and no `GLOBAL_*` fallback. |
| 18.5 | public migration | Replace/deprecate legacy `ThreadPool` only after typed transfer envelopes admit a result class beyond `i64`. | Real OS-thread stress, bounded high-water/RSS counters, cancellation, and two-pool isolation. |

Sidecar lanes: **N/A until 18.1 names and status codes are frozen**. Merge owner
defines the ABI names, test `step("...")` labels, and failure messages before
any lower-model implementation review. Final review must verify that no
runtime pointer or caller-owned closure descriptor crosses the pool boundary.
