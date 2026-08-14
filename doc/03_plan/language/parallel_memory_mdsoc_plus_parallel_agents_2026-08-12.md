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
| WP-14 bounded mailbox | partial implementation | native compatibility channel and actor/common inbox/outbox queues have finite capacity 256; `ActorMailbox.new(0)`/negative resolve to the finite default, close now rejects future sends through every shared handle, and its head-cursor FIFO compacts only when capacity reuse needs it. The older priority mailbox now normalizes zero/negative or forged configuration to its finite default, including its legacy `unbounded()` spelling. Process parent ingress additionally has frame-count plus copied-byte ceilings. Real self-hosted FIFO/backpressure/close-wakeup execution, policy-selected capacities, and checked public actor send remain |
| WP-15 commit engine | partial implementation | common functional owner transition validates the whole batch before one revision/snapshot-token root assignment and emits canonical-order receipts; bounded result ordering uses stable O(n log n) merge passes. `ParentCommitOwnerV1` mutex-serializes local publication and drains a bounded framed Process-to-Parent batch through the common transition. Payload apply/verify, a production CAS path, and admitted Stage 4 evidence remain |
| WP-16 actor/channel migration | partial implementation | native safe paths carry route-validated inline packets, actor reply provenance is explicit, and heap actor context is rejected. Actor, scheduler, and mailbox are class-backed shared authorities; each `ActorRef` retains its admitting scheduler so `spawn_on` cannot route through the global scheduler, mailbox closure prevents post-stop admission through copies, scheduler ready IDs use cursor storage, and legacy `ask()` reserves bounded reply capacity through completion until consume/cancel. Typed heap/owned payloads, native lifecycle execution, and public API migration remain |
| WP-17 process transport | partial implementation | common/native bounded encoded-copy frames share a complete golden vector and a real exec-child round trip. `ParentCommitPipedProcessSessionV1` now owns one child handle and bounded `SPRF1` reader, pairs it with a generation-bound/replay-rejecting inbox, and records an idempotent terminal close result. The native system gate is present, but the deployed self-hosted CLI currently segfaults on `test --help` before discovery; child request input protocol, schema registry, ObjectRef, application payload rollback, and admitted native process evidence remain |
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

## Restart12 actor/process replacement lane acceptance (2026-08-14)

Owner: detached `/mnt/data/worktrees/restart12-actors` lane. Integration owner:
`/root`, serialized by `/tmp/simple-main-restart12-push.lock`. Sidecars: `N/A`
for this narrow runtime-boundary repair. Final reviewer: the primary
normal/highest-capability verifier before integration.

- [ ] Actor/channel public sends retain one scheduler/mailbox authority, reject
  admission after close through every copied handle, and never transport an
  unchecked heap `Value` or child-local pointer.
- [x] Process results use the canonical bounded `SPRF1`/`SPRS` encoded-copy
  frame path through the shipped piped-process facade; partial reads, malformed
  frames, non-ASCII output, oversize lines, and full frame/byte budgets fail
  closed without unbounded retention.
- [ ] `ParentCommitOwnerV1` remains the sole mutable root owner: children create
  result envelopes, the parent validates and deterministically orders the whole
  batch, and publication occurs once only after validation succeeds.
- [x] Rejected, stale, cancelled, or failed child results are not reinserted or
  implicitly retried; close wakes/terminates the transport lifecycle and all
  accepted process handles are closed exactly once.
- [ ] Focused unit/integration evidence covers copied-frame isolation,
  backpressure, close behavior, split/coalesced stdout reads, failure rollback,
  deterministic parent commit, and real separate-process delivery.
- [ ] The focused system spec passes once with the deployed self-hosted runtime
  in native mode, followed by the required compiler/lib/MCP/LSP regression and
  runtime-facade audit gates for changed core/lib surfaces.
- [ ] Verification reports `STATUS: PASS`; intentional changes are committed,
  rebased onto fetched `origin/main`, pushed without token environment
  overrides while holding the integration lock, and proven reachable from the
  freshly fetched `origin/main` with a clean tree.

Current blocker: the deployed self-hosted CLI still crashes
during its bounded `test --help` discovery probe, so native process evidence is
not yet admitted. This lane has now added explicit child-generation/replay
binding and a parent-observable terminal lifecycle receipt; their executable
verdict remains WARN until that prerequisite is repaired.

## Mandatory handoff record

The available `bin/simple` identifies itself as a bootstrap seed. The deployed
`bin/release/simple` wrapper identifies a self-hosted beta runtime, but rejects
tests because its bounded `test --help` ABI probe currently segfaults. The
source guard is already tracked; its fresh redeploy is blocked by the documented
stage-4 parse-memory balloon in
[native_selfhosted_run_segfault_startup_normalize_2026-07-24.md](../../08_tracking/bug/native_selfhosted_run_segfault_startup_normalize_2026-07-24.md).
Before a lane claims executable PASS, repair that deployment prerequisite and
re-run its focused spec with the admitted Stage 4 CLI, capturing the resolved
binary identity.
The raw-value runtime blocker is
[tracked](../../08_tracking/bug/parallel_runtime_raw_value_transport_2026-08-12.md);
do not label actor/process isolation as complete until that record is resolved.
