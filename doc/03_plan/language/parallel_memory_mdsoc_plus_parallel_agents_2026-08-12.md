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
| WP-01 transfer contract | partial implementation | common envelope/boundary checks; codec/wire vectors remain |
| WP-02 storage contract | partial implementation | plan and conservative planner exist; mapping/wire vectors remain |
| WP-03 commit contract | partial implementation | deterministic order/conflict validator exists; receipt/apply remains |
| WP-04 policy resolver | partial implementation | raise-only common resolver exists; SDN/driver integration remains |
| WP-05 requirements/diagnostics | partial implementation | selected requirements/state exist; stable compiler diagnostic registry remains |
| WP-10 borrow soundness | in progress | dynamic index is now conservative; CFG/NLL rewrite remains |
| WP-11..18 runtime/boundaries | blocked on implementation | P0 raw RuntimeValue transport record identifies exact sources |
| WP-20..27 layout/performance | planned | no MIR lowering, allocator adoption, or evidence yet |
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
2. WP-13/WP-16/WP-17: replace raw RuntimeValue transport with envelope codecs and bounded typed mailboxes; prove separate-process pointer isolation.
3. WP-15: connect validated ordered results to atomic owner-side snapshot publication and receipts.
4. WP-20/WP-22: preserve MIR access paths into typed AoS/SoA reference parity before SIMD/GPU lowering.

## Mandatory handoff record

The available `bin/simple` identifies itself as a bootstrap seed. Before a lane
claims executable PASS, re-run its focused spec with an admitted Stage 4
self-hosted CLI and capture the resolved binary identity. The raw-value runtime
blocker is [tracked](../../08_tracking/bug/parallel_runtime_raw_value_transport_2026-08-12.md);
do not label actor/process isolation as complete until that record is resolved.
