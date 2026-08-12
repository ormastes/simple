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
| WP-03 commit contract | partial implementation | deterministic order/conflict validation, bounded receipt invariants, canonical receipt wire/equality/SHA-256 identity, and constant-size proposed root state exist; payload/root attestation and serialized/CAS owner adapter remain |
| WP-04 policy resolver | partial implementation | raise-only common resolver exists; SDN/driver integration remains |
| WP-05 requirements/diagnostics | partial implementation | selected requirements/state exist; stable compiler diagnostic registry remains |
| WP-10 borrow soundness | in progress | dynamic indices are conservative; CFG successors and one global MIR/NLL point layout now cover non-entry blocks; path-sensitive move joins, loop fixed points, and proven range disjointness remain |
| WP-11 HIR boundary checker | partial implementation | compiler-owned copy/frozen/move/runtime-classified/reject decisions, parent-origin diagnostics, and assurance-derived policy wiring exist for literal `spawn` HIR; parser-seed `spawn(...)` lowering and complete capture/boundary coverage remain |
| WP-12 MIR transfer operations | partial implementation | explicit TransferOut/In, FreezeRegion, AcquireSnapshot, and CommitUpdates instructions, JSON identity, borrow facts, optimizer uses/defs, and spawn/spawn_actor emission exist; actor/process/device adapters and backend lowering remain |
| WP-13 native transfer codec | partial implementation | strict envelope/inline packet, fail-closed RuntimeValue classification, authority state machine, all four Rust isolated-thread spawn variants reject unsupported heap inputs before launch, and a bounded logical-content codec materializes boxed `f64`, boxed `u64`, and UTF-8 strings with new heap identity; graph/schema sealing and non-Rust runtime parity remain |
| WP-14 bounded mailbox | partial implementation | native compatibility channel and actor/common inbox/outbox queues have finite capacity 256; `ActorMailbox.new(0)`/negative now resolve to the same finite default instead of an unbounded sentinel, while explicit positive capacity remains configurable. Its bounded head-cursor FIFO compacts only when a full storage buffer is reused rather than slicing at every dequeue. The resolver fixture and available bootstrap check emit dependency warnings without a final verdict, so real self-hosted FIFO/backpressure execution, policy-selected capacities, and checked public actor send remain |
| WP-15 commit engine | partial implementation | common functional owner transition validates the whole batch before one revision/snapshot-token root assignment and emits canonical-order receipts; bounded result ordering now uses stable O(n log n) merge passes instead of quadratic selection, with a 16-result reverse-completion regression awaiting an admitted self-hosted run. Concurrent CAS/lock publication, payload apply/verify, and admitted Stage 4 evidence remain |
| WP-16 actor/channel migration | partial implementation | native safe paths carry route-validated inline packets, actor reply provenance is explicit, and heap actor context is rejected; typed heap/owned payloads remain |
| WP-17 process transport | partial implementation | common/native bounded encoded-copy frames share a complete golden vector and a real exec-child round trip; production spawn/piped integration, session/replay binding, schema registry, ObjectRef, and rollback remain |
| WP-18 thread pool | in progress | internal `rt_pool_state_*_v1` groundwork bounds accepted unreleased scalar tasks, uses tagged generation handles with lifetime pins, rejects stale/wrong-kind handles, reclaims task state on release, and normalizes tagged direct-function values before task-owned descriptor copy; Rust runtime gates pass, but the only native Simple facade run timed out at the runner before an assertion verdict, so its uncommitted facade is not admitted. A bounded self-hosted native callback/Full→release/close→idle/destroy gate, alternate-provider execution, legacy generic-global migration, cancellation, blocking admission, and heap transfer remain |
| WP-20 access analysis | partial implementation | compiler MIR analysis preserves constant partition ranges through record loads into field paths, retains conservative public Load+GetField legality facts, derives address-observation/unknown-access summaries, and separately classifies terminal field events for layout advice; terminator and non-field uses prevent structural-load elision; authoritative CFG/noalias, partition ownership, PGO, and frequency evidence remain |
| WP-21 layout planner | partial implementation | a compiler advisory now derives the existing planner request from complete, sparse typed field observations without parsing projection text; empty, dynamic, unknown, address-observed, co-accessed, and all-fields-used cases retain AoS/reference, while ABI/GPU/SIMD remain explicit hard inputs; the full cost model, landed-layout filtering, typed receipts, and policy/PGO inputs remain |
| WP-22 host AoS/SoA lowering | partial implementation | compiler-private MIR allocation owner/fact, declaration conversion, canonical producer, and pre-optimization address rewrite are landed; CompileContext freezes validated module-qualified storage rows, then the parent creates class-handle MIR+storage capsules for every uncached module before the ParallelBuilder branch; capsule workers receive no CompileContext or BuildCache, complete MIR/storage identity is revalidated around codegen, object receipts bind content hash/size, and a parent-only hook checkpoints cache results; focused registry/capsule evidence passes 16/16; the current builder branch is sequential batching, so real process/thread concurrency still requires a complete MIR capsule codec/lease enforcement; public typed allocation, subword/other backends, and fresh non-stub W^X execution remain |
| WP-23 AoSoA/SIMD lowering | partial implementation | admitted full blocks emit typed MIR through OpenCL and aligned native x86 AVX2 f32x8; native selection requires a versioned target-capability receipt, the pure-Simple driver intersects `SIMPLE_NATIVE_CPU` with canonical host CPUID/XGETBV evidence and keys its cache by the decision; straight-line AVX2 regions now reuse YMM registers from exact last-use facts, allowing more than eight sequential destinations while true pressure, multi-block SIMD, and calls fail closed; a compiled W^X spec checks eight exact f32 results; CFG vector liveness, 32-byte spills, explicit cross-target receipts, partial-vector, scalable routes, and public custom-native CLI admission remain |
| WP-24..27 layout/performance | planned | no GPU backend lowering, layout-view cache, allocator adoption, NUMA/false-sharing implementation, or end-to-end evidence yet |
| WP-30..36 MDSOC/pilots | planned | do not start before safe transport and layout inputs |
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
3. WP-15: connect the common functional snapshot-root transition to serialized/CAS owner publication, payload-aware apply/verify, mutation receipts, and admitted Stage 4 evidence.
4. WP-20/WP-22: preserve MIR access paths into typed AoS/SoA reference parity before SIMD/GPU lowering.

## Mandatory handoff record

The available `bin/simple` identifies itself as a bootstrap seed. Before a lane
claims executable PASS, re-run its focused spec with an admitted Stage 4
self-hosted CLI and capture the resolved binary identity. The raw-value runtime
blocker is [tracked](../../08_tracking/bug/parallel_runtime_raw_value_transport_2026-08-12.md);
do not label actor/process isolation as complete until that record is resolved.
