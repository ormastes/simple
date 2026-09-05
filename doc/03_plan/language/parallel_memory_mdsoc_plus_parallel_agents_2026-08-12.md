# Parallel Ownership and Memory Layout: Execution Status

Baseline: `ddfcfbea806cb2dc0f2fbc311bb922962a0ea29c` inspected on 2026-08-12.
Merge owner: `/root`. Final reviewer: normal/highest-capability reviewer.
The companion CSV is the complete work-package dependency graph.

## Frozen common names

`TransferEnvelopeV1`, `StorageLayoutPlanV1`, `ResultEnvelopeV1`,
`ParallelAccessPathV1`, `ParallelCommitPort`, and `ResolvedParallelPolicyV1`.
Do not redefine them in runtime, MDSOC, backend, or application lanes.

## Current status

| Work package | Status | Evidence / next gate |
|---|---|---|
| WP-00 baseline/census | complete for this lane | local research names existing placement/mutation owners |
| WP-01 transfer contract | partial implementation | common + native 40-byte codecs agree on a golden vector; token uniqueness model remains |
| WP-02 storage contract | partial implementation | plan, conservative planner, overflow-safe AoS/SoA/AoSoA projection, canonical wire/equality/SHA-256 identity, and malformed-input vectors exist; specialized grouped/tiled/packed/factored mappings and a ratified V2 for additional semantic fields remain |
| WP-03 commit contract | partial implementation | deterministic order/conflict validation, bounded receipt invariants, canonical receipt wire/equality/SHA-256 identity, and constant-size proposed root state exist. `ParentCommitOwnerV1` serializes the live root, while framed `SPRS` process results remain pointer-free; payload/root attestation and a production CAS alternative remain |
| WP-04 policy resolver | partial implementation | raise-only parallel and memory resolvers exist. Memory policy constrains bounded buffers, ABI/address pinning, implicit conversion, and layout receipts without selecting a representation; SDN/driver/planner integration remains |
| WP-05 requirements/diagnostics | partial implementation | selected requirements/state exist; stable compiler diagnostic registry remains |
| WP-10 borrow soundness | in progress | dynamic indices are conservative; CFG successors and one global MIR/NLL point layout now cover non-entry blocks; path-sensitive move joins, loop fixed points, and proven range disjointness remain |
| WP-11 HIR boundary checker | partial implementation | compiler-owned copy/frozen/move/runtime-classified/reject decisions, parent-origin diagnostics, and assurance-derived policy wiring exist for literal `spawn` HIR; parser-seed `spawn(...)` lowering and complete capture/boundary coverage remain |
| WP-12 MIR transfer operations | partial implementation | explicit TransferOut/In, FreezeRegion, AcquireSnapshot, and CommitUpdates instructions, JSON identity, borrow facts, optimizer uses/defs, and spawn/spawn_actor emission exist; actor/process/device adapters and backend lowering remain |
| WP-13 native transfer codec | partial implementation | strict envelope/inline packet, fail-closed RuntimeValue classification, authority state machine, all four Rust isolated-thread spawn variants reject unsupported heap inputs before launch, and a bounded logical-content codec materializes boxed `f64`, boxed `u64`, and UTF-8 strings with new heap identity; graph/schema sealing and non-Rust runtime parity remain |
| WP-14 bounded mailbox | partial implementation | native compatibility channel and actor/common inbox/outbox queues have finite capacity 256. Public actor send/ask/stop now enter through the scheduler owner, actor arguments are copied at admission, native checked send reports invalid/heap/full/disconnected outcomes, and native stop wakes receive exactly once. Process parent ingress has frame-count plus copied-byte ceilings. Stage-4 Simple execution, policy-selected capacities, and typed heap payloads remain |
| WP-15 commit engine | partial implementation | `ParentCommitOwnerV1` now validates the complete batch, applies and verifies its canonical application payload root, then publishes payload root plus revision/snapshot token once under one mutex with a before/after mutation receipt. Focused source tests cover mixed malformed and conflict rollback. A production CAS path and admitted Stage-4 Simple evidence remain |
| WP-16 actor/channel migration | partial implementation | `ActorRef` retains only actor ID plus admitting scheduler; all public operations fail closed outside the scheduler's creator thread. Native `rt_actor_try_send` exposes checked backpressure while the legacy void ABI delegates to it, and cooperative stop has hosted-runtime evidence. Typed heap/owned payloads, cross-domain command ingress, and admitted Simple actor lifecycle execution remain |
| WP-17 process transport | partial implementation | `ParentCommitPipedProcessSessionV1` owns one child handle and bounded `SPRF1` reader, issues a fresh generation, rejects replay, revokes accepted frames on cancellation, and records natural-exit/cancel/close-once lifecycle receipts. The Stage-2 executable proves copied-frame isolation, but its aggregate/`Option` lowering corrupts the remaining real-child scenarios; Stage-4 remains unavailable. Child request input protocol, schema registry, ObjectRef, and admitted end-to-end evidence remain |
| WP-18 thread pool | in progress | internal `rt_pool_state_*_v1` groundwork bounds accepted unreleased scalar tasks, uses tagged generation handles with lifetime pins, rejects stale/wrong-kind handles, reclaims task state on release, and normalizes tagged direct-function values before task-owned descriptor copy; Rust runtime gates pass, but the only native Simple facade run timed out at the runner before an assertion verdict, so its uncommitted facade is not admitted. A bounded self-hosted native callback/Full→release/close→idle/destroy gate, alternate-provider execution, legacy generic-global migration, cancellation, blocking admission, and heap transfer remain |
| WP-20 access analysis | partial implementation | compiler MIR analysis preserves constant partition ranges through record loads into field paths, retains conservative public Load+GetField legality facts, derives address-observation/unknown-access summaries, and separately classifies terminal field events for layout advice; terminator and non-field uses prevent structural-load elision; authoritative CFG/noalias, partition ownership, PGO, and frequency evidence remain |
| WP-21 layout planner | partial implementation | a compiler advisory derives the existing planner request from complete, sparse typed field observations without parsing projection text. The memory-policy adapter pins address-observed data and suppresses automatic conversion under a deny-conversion profile while binding policy identity into the request hash; empty, dynamic, unknown, co-accessed, and all-fields-used cases retain AoS/reference. The full cost model, driver/SDN policy loading, landed-layout filtering, typed receipts, and PGO inputs remain |
| WP-22 host AoS/SoA lowering | partial implementation | compiler-private MIR allocation owner/fact, declaration conversion, canonical producer, and pre-optimization address rewrite are landed; CompileContext freezes validated module-qualified storage rows, then the parent creates class-handle MIR+storage capsules for every uncached module before the ParallelBuilder branch; capsule workers receive no CompileContext or BuildCache, complete MIR/storage identity is revalidated around codegen, object receipts bind content hash/size, and a parent-only hook checkpoints cache results; focused registry/capsule evidence passes 16/16; the current builder branch is sequential batching, so real process/thread concurrency still requires a complete MIR capsule codec/lease enforcement; public typed allocation, subword/other backends, and fresh non-stub W^X execution remain |
| WP-23 AoSoA/SIMD lowering | partial implementation | admitted full blocks emit typed MIR through OpenCL and aligned native x86 AVX2 f32x8; native selection requires a versioned target-capability receipt, the pure-Simple driver intersects `SIMPLE_NATIVE_CPU` with canonical host CPUID/XGETBV evidence and keys its cache by the decision; straight-line AVX2 regions now reuse YMM registers from exact last-use facts, allowing more than eight sequential destinations while true pressure, multi-block SIMD, and calls fail closed; a compiled W^X spec checks eight exact f32 results; CFG vector liveness, 32-byte spills, explicit cross-target receipts, partial-vector, scalable routes, and public custom-native CLI admission remain |
| WP-24..27 layout/performance | planned | no GPU backend lowering, layout-view cache, allocator adoption, NUMA/false-sharing implementation, or end-to-end evidence yet |
| WP-30..36 MDSOC/pilots | planned | do not start with a decorative port: current MDSOC ports are descriptive counters with no driver policy-carrying stage route or bypass oracle. First establish production framed process spawn/piped delivery and an allocation-owner planner call, then add one routed pilot with a real bypass failure |
| WP-40..44 docs/formal/benchmarks | in progress | guide and skills added; real system/manual/formal evidence remains |

## Non-overlap assignments

| Lane | May edit | Must not edit |
|---|---|---|
| P0 integration | common contract roots, policy root, status plan | runtime adapters, compiler borrow implementation |
| P1 borrow | `src/compiler/55.borrow/**` and borrow tests | common contract names, runtime transport |
| P2 runtime transport | dedicated runtime transfer/actor/channel/process leaves | pure compiler ownership rules unless interface change ratified |
| P3 storage | dedicated MIR storage-layout/backend/allocator leaves | ABI-facing types without explicit conversion boundary |
| P4 MDSOC/pilots | `85.mdsoc` adapters and isolated pilots | contract roots and other pilot owners |
| P5 evidence | docs, guides, system/formal/benchmark tests | source runtime/compiler leaves |

## Immediate next gates

1. WP-10: replace block/point ambiguity with CFG-sensitive region facts and add dynamic-index, branch, loop, capture, and move regression evidence.
2. WP-13/WP-16/WP-17: connect bounded encoded process frames to the production spawn/piped facade, add schema/ObjectRef codecs, and prove failure rollback; the native compatibility channel now has checked ref-counted lifetime across concurrent send/close/free, but still needs typed public endpoints and policy-selected capacity. Never revive the removed aggregate `rt_pg_parallel_worker_handoff_*` design.
3. WP-15/WP-17: keep `ParentCommitOwnerV1` as the serialized local root and add application-owned payload apply/verify plus mutation receipts. Repair the deployed self-hosted `test --help` crash first, then run `SIMPLE_LIB=src bin/release/simple test test/03_system/feature/language/parent_commit_piped_result_spec.spl --mode=native` once for an admitted framed child-result delivery verdict.
4. WP-30/WP-33: route the frozen transfer/layout/commit policy through one real MDSOC process pilot, where a bypass fails before publication and cancellation/cleanup are observable.
5. WP-20/WP-22: preserve MIR access paths into typed AoS/SoA reference parity before SIMD/GPU lowering.

## Restart12 actor/process SPipe completion plan (2026-08-14)

Owner: detached `/mnt/data/worktrees/restart12-actors` lane. Integration owner:
`/root`, serialized by `/tmp/simple-main-restart12-push.lock`. SPipe state:
`.spipe/parent_authoritative_actor_process/state.md`. Parallel review lanes:
`actor_audit` (actor/channel authority and lifecycle) and `process_audit`
(framing, replay, parent commit, and SPipe/manual evidence). Final reviewer: a
separate highest-capability reviewer after merge, before accepting done marks.

Execution authorization update (2026-08-14): the user requires completion of
all AC-1..AC-9 work and explicitly authorizes provenance-identified Stage-3 or
Stage-2 pure-Simple binaries while the deployed Stage-4 wrapper is broken.
Stage-2/3 evidence must record the exact binary and runtime bundle; it may prove
the commands that the binary actually implements, but must not be described as
Stage-4/full-CLI evidence. The completion lane therefore first inventories or
produces an admitted Stage-2/3 artifact, implements AC-1..AC-6, runs each
supported focused/core gate once, and records any genuinely Stage-4-only gate
separately instead of silently substituting the Rust seed.

### Acceptance and evidence matrix

| AC | State | Current evidence | Required completion evidence |
|---|---|---|---|
| AC-1 actor authority and safe payload | **implemented; Simple execution blocked** | `ActorRef` retains only ID+scheduler; send/ask/query/stop use scheduler-owned admission and fail closed off its creator thread. Arguments are copied at admission. Hosted native tests pass heap/invalid rejection and finite-capacity backpressure. | Obtain an admitted Stage-4 Simple public-surface verdict; typed heap/owned actor payloads remain outside this fixed-packet contract. |
| AC-2 bounded framed process result | **implemented; focused Stage-2 PASS** | The admitted Stage-2 executable passed all 8 inbox examples: hostile input, replay, frame/byte budgets, FIFO, copied retention, revoke, and deterministic drain. | Repair nested aggregate lowering and obtain the real-child system verdict. |
| AC-3 sole parent apply/verify/publish | **implemented; focused Stage-2 PASS** | The admitted Stage-2 executable passed all 9 owner examples, including candidate apply/verify, mutation receipts, canonical order, and mixed malformed/conflict rollback. | Retain the focused PASS while repairing the broad system executable; no overall acceptance yet. |
| AC-4 lifecycle, cancellation, no resurrection | **implemented; focused mixed PASS** | Hosted actor lifecycle tests pass. The admitted Stage-2 piped unit passed all 6 examples, including zero-generation rejection and close behavior; inbox revoke/no-resurrection passed. | Obtain the real-child cancellation/reap system verdict after aggregate-return repair. |
| AC-5 focused executable evidence | **partial** | Stage-2 process units historically report 8/8 inbox, 9/9 owner, and 6/6 piped examples, but their exact shard logs were not retained. The process system source now has modern typed evidence and four real scenarios; Stage 2 passed copied isolation only. A separate actor/channel Modern SSpec covers same-thread scheduler authority, bounded credit, copied arguments, and unique stop. An admitted Stage-2 compile probe now parses the repaired mailbox and advances into `actor/spawn.spl`, where the existing flat-AST tag-39/`str.clear` compiler gap stops compilation. Neither spec has an admitted Stage-4 verdict. | Repair the tracked Stage-2 spawn-expression/code-generation gap, nested aggregate-return lowering, and Stage-4 deployment, then run both focused system specs once and retain commands/logs/provenance. |
| AC-6 SPipe manual and maintenance | **authored; generation blocked** | The process and actor/channel primary flows each have five frozen steps, closed typed schemas, authored operator manuals, traceability, and no skip-success path. | Stage-4 `spipe-docgen` and seven-score `sspec-maintain` remain unavailable; neither authored manual is labeled generated PASS. |
| AC-7 production verification | **FAIL / blocked** | A typed receipt authorized the current-source Stage-2 compiler (SHA-256 `4c2d7d7328372175260d75ffd1ee2e475d9848a1d534c73ace7a9ef1eee0b68e`). The mailbox parser defect and mixed `runtime_memtrack.c` line endings are repaired; the bounded Stage-2 compile reached the separately tracked spawn-expression/compiler failure. Stage 3 terminated at 29,019,120 KiB RSS. Phase 4 was explicitly excluded from this continuation. | Repair staged aggregate-return lowering and the profiled Stage-3 retention owner, then complete Stage 3/4 and run compiler/lib/MCP/LSP, lint, duplication, SPipe, and concurrency/resource-model gates. Do not rerun unchanged failed transactions. |
| AC-8 guide and expert knowledge | **complete** | Architecture, detail design, guide, feature/layer experts, test plans, and blocker classifications reflect the landed actor/process contracts and current evidence. | Reopen if final review finds an overclaim or an interface changes. |
| AC-9 cooperative review | **modernization delta accepted; feature acceptance withheld** | Read-only SSpec, knowledge, and truthfulness audits identified stale cancellation, plan, provenance, and status claims; the merge owner incorporated their findings. A separate highest-capability reviewer accepted the corrected final modernization diff, including the explicit exclusion of moved-source invalidation from cancellation coverage. | Re-review any later semantic change. Overall feature acceptance remains withheld while AC-5..7 fail. |

The obsolete `codex/runtime-server-actors-01a00035` tip was inspected without
merging. It comes from a pre-canonical fork whose competing `STP1` text codec
and removed usage-spec paths omit or conflict with the canonical bounded
`SPRF1`/`SPRS` process transport, so the old 174-commit branch is excluded
rather than rebased or cherry-picked.

### Frozen implementation and manual vocabulary

- Interfaces: `ActorMailbox`, `ActorScheduler`, `ActorRef`,
  `TransferEnvelopeV1`, `ProcessTransferFrameV1`,
  `ParentCommitFrameInboxV1`, `ParentCommitPipedProcessSessionV1`, and
  `ParentCommitOwnerV1`.
- Manual steps: `Create a bounded parent-owned process session`; `Receive a
  fragmented encoded child result`; `Reject stale or replayed child output`;
  `Commit one validated batch at the parent`; `Close the child transport
  exactly once`.
- Setup/checker helpers: `child_result_line`,
  `parent_commit_frame_inbox_v1_for_generation`,
  `parent_commit_piped_process_session_v1`, and
  `drain_process_result_batch`. Any not-yet-wired helper must fail explicitly
  with `assert(false)` or `fail(...)`.
- Actor manual steps: `Create one scheduler-owned bounded actor channel`;
  `Admit copied arguments through one actor reference`; `Observe finite mailbox
  and reply backpressure`; `Dispatch and consume the isolated result`; `Stop
  once through the owning scheduler`.
- Closed evidence schemas: `actor-channel-authority/v1` and
  `parent-commit-piped-result/v1`.

### Ordered implementation lanes

1. **Actor admission owner (AC-1/4/5):** choose the scheduler-domain contract,
   land one checked admission port, remove direct `ActorRef` mailbox mutation,
   surface native backpressure, and add public behavioral evidence.
2. **Parent application commit (AC-3/5):** add candidate-root apply/verify and
   mutation receipts, then atomic mixed-batch rollback evidence.
3. **Process lifecycle (AC-2/4/5):** add parent-issued session freshness,
   cancel/reap/close-once receipts, and real-child hostile-stream evidence.
4. **Stage-2/3 execution lane (AC-7):** inventory or produce a provenance-bound
   Stage-3 or Stage-2 pure-Simple binary and use it only for explicitly
   supported focused compile/native gates. General `test`, docgen, and
   maintenance require the Stage-4 surface. Keep Stage-4-only CLI coverage
   explicit; do not use the Rust seed as acceptance evidence.
5. **SPipe/manual and production gates (AC-5/6/7):** author the frozen five-step
   scenario, generate its mirrored manual, clear the seven-score maintenance
   gate, and execute each remaining production check once, with at most three
   fix cycles.
6. **Knowledge and review (AC-8/9):** refresh guide/design/experts/bugs, then
   require separate highest-capability acceptance before marking any remaining
   item complete.

### Active blockers and resume commands

- Stage 4 runtime: `bin/release/simple test --help` fails its bounded ABI probe
  with status 139. The authorized recovery lane is an admitted Stage-3/2
  pure-Simple artifact; capture its provenance and supported-command inventory
  before using it. Run the focused native executable directly when the staged
  compiler lacks the full `test` driver.
- SPipe manual: docgen/maintenance cannot be admitted with the crashing Stage 4
  runtime. Resume `spipe-docgen` and `sspec-maintain scan` for both
  `actor_channel_authority_spec.spl` and
  `parent_commit_piped_result_spec.spl` using the exact commands in their
  focused system-test plans.
- Raw actor value transport remains tracked by
  `parallel_runtime_raw_value_transport_2026-08-12.md`; session freshness,
  cancellation revocation, PID reuse, and terminal child cleanup are tracked
  separately by
  `process_transfer_session_replay_identity_2026-08-12.md`. Both records remain
  open until executable proof lands.

## Mandatory handoff record

This lane produced the current-source pure-Simple Stage-2 binary at
`build/bootstrap-restart12-current/stage2/x86_64-unknown-linux-gnu/simple`
(SHA-256 `4c2d7d7328372175260d75ffd1ee2e475d9848a1d534c73ace7a9ef1eee0b68e`).
Stage 2 passed the canonical sanity gate. Stage 3 was terminated at
29,019,120 KiB RSS while parsing file 200/617, before a diagnostic or candidate;
do not repeat that unchanged transaction. The repo-managed
Stage-4 wrapper still rejects tests because its bounded `test --help` ABI probe
segfaults. The source guard is tracked by
[native_selfhosted_run_segfault_startup_normalize_2026-07-24.md](../../08_tracking/bug/native_selfhosted_run_segfault_startup_normalize_2026-07-24.md).
Before a lane claims executable PASS, repair that deployment prerequisite and
re-run its focused spec with the admitted Stage 4 CLI, capturing the resolved
binary identity.
The raw-value runtime blocker is
[tracked](../../08_tracking/bug/parallel_runtime_raw_value_transport_2026-08-12.md);
do not label actor/process isolation as complete until that record is resolved.
