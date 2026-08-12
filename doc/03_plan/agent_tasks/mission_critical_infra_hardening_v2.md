# Mission-Critical Infrastructure Hardening V2 — Parallel Agent Plan

**Status:** contract frozen for implementation
**Merge owner:** root Codex
**Final reviewer:** a separate normal/highest-capability Codex (or equivalent
highest-capability model), not a lane author

## Coordination rules

Wave 0 is serial: the merge owner freezes the interfaces below and creates
fail-fast skeletons. Waves 1–3 may run in parallel only with disjoint ownership.
Lane agents do not edit aggregate dispatch, shared schemas, root exports, the
canonical SSpec, generated manual, or another lane's files. They return file
lists, commands run once, results, open risks, and evidence paths to the merge
owner. Unrelated dirty files are preserved. Shared-contract changes stop the
affected lanes and return to a serial merge-owner review.

Lower-model sidecars may inventory or draft lane-local cases, but their output
is not accepted until reviewed by a normal/highest-capability model. Only the
merge owner integrates. Only the independent final reviewer may sign the final
review receipt.

## Wave 0 — shared contract lock (root Codex)

Freeze these public names before parallel implementation:

- `MciRunIdentityV1`, `MciArtifactIdentityV1`, `MciEvidenceManifestV1`
- `MciTypedResultV1`, `MciRejectionCodeV1`, `MciGateReceiptV1`
- `CompilerAdmissionV1`, `CertifiedSimpleOsManifestV1`, `CertifiedCellV1`
- `DrawIrGenerationPlanV3`, `DrawIrGenerationArenaV3`,
  `DrawIrOverflowReceiptV1`, `RenderProvenanceV1`
- `RelaxedAllocationProfileV1`, `CriticalContextV1`, `DomainArenaV1`,
  `ArenaCheckpointV1`, `ArenaExhaustionV1`
- `BoundedWorkPoolV1`, `BoundedProcessCaptureV1`, `ProcessSafetyReceiptV1`
- lane entrypoints: `run_compiler_admission`, `run_tooling_admission`,
  `run_certified_simpleos`, `run_render_admission`,
  `run_allocation_admission`, `run_process_admission`, `run_stress_admission`,
  `aggregate_mci_admission`

The common receipt fields are `run_id`, `profile_id`, `generation_id`, exact
binary/source/config hashes, host/guest identity, UTC timestamps, command,
timeout, exit status, typed result/rejection, metrics, and artifact paths.
Serialization is deterministic. Unknown enum/schema versions reject.

The canonical SSpec vocabulary is frozen in
`doc/03_plan/sys_test/mission_critical_infra_hardening_v2.md`; agents must use
those exact eight `step("...")` strings and exact setup/checker helper names.
Do not introduce `Given_*`, `When_*`, or `Then_*` aliases.

Every not-yet-implemented shared runner/helper must fail immediately:

```simple
fail("MCI endpoint not implemented: <endpoint>")
```

`assert(false)` is acceptable where `fail` is unavailable. Silent returns,
empty bodies, dummy receipts, `pass_todo`, and unconditional success are
forbidden.

## Parallel implementation lanes

| Lane | Exclusive ownership | Requirements | Deliverables and acceptance |
|---|---|---|---|
| A — compiler/tooling | exact-current compiler provenance/admission modules; unified tooling gate; compiler/tooling gate scripts; lane-local unit/integration tests and evidence schema adapters | REQ-MCI-001, 002; NFR-MCI-001, 002, 003, 007; supports 010 | Exact-current discriminating execution; clean-host reproducibility; bounded compiler/lib/MCP/LSP/bootstrap/lint/duplication/test/perf/runtime/direct-env rows; stale/unknown/timeout/capture negative controls |
| B — SimpleOS | certified platform manifest and schema; guest payload/image placement; platform runners; lane-local tests and evidence adapters | REQ-MCI-003, 004; NFR-MCI-003, 008; supports 010 | All 24 cells visible, selected cells fully witnessed; guest filesystem payload executes from canonical paths; unavailable/incomplete cell blocks broader claim; bounded 24-hour runner |
| C — rendering/allocation | DrawIR-v3 count/plan/admit arena and fixed queues; producer/Engine2D integration; provenance/readback/interaction/RenderDoc checks; relaxed allocation arenas, telemetry, rollback, injection; lane-local tests and gates | REQ-MCI-005, 006, 007, 008; NFR-MCI-003, 004, 005, 006; supports 010 | Immutable active generations; overflow-before-emission; no atlas/cache in Draw IR; strict zero allocation; relaxed sealed domain quotas; complete fault injection and isolation evidence |
| D — concurrency/process | bounded runtime pool, queue/in-flight admission, capture, cancellation/timeouts, PID validation; lane-local tests and process gate | REQ-MCI-009; NFR-MCI-003; supports 010 | Deterministic boundary cancellation; capture/queue overflow; all kill/wait paths reject `pid <= 0`; no unbounded fallback or unrelated-process effect |

Lanes may add files only within their declared feature directories and
lane-local tests/scripts. Any necessary edit to a pre-existing shared
dispatcher, manifest registry, root export, aggregate checker, or the canonical
SSpec is proposed as a patch note and performed serially by root Codex.

## Wave 2 — lane verification (parallel, once per criterion)

Each lane performs at most three verify/fix cycles and never repeats an
identical green command. Lane gates and evidence locations are:

| Lane | One-run gate | Evidence root |
|---|---|---|
| A | `check-mci-v2-compiler-admission.shs` then `check-mci-v2-tooling-admission.shs` | `build/evidence/mci-v2/{compiler,tooling}` |
| Process safety | `check-mci-v2-process-safety.shs` with an admitted exact-current pure-Simple runner | `build/evidence/mci-v2/process` |
| B | `check-mci-v2-simpleos-manifest.shs` and the bounded stress runner | `build/evidence/mci-v2/{simpleos,stress}` |
| C | `check-mci-v2-rendering.shs` then `check-mci-v2-allocation.shs` | `build/evidence/mci-v2/{rendering,allocation}` |
| D | `check-mci-v2-process-safety.shs` | `build/evidence/mci-v2/process` |

Each handoff must demonstrate its happy, exact-boundary, and injected-failure
scenario IDs from the system-test plan. A source search is supporting evidence,
not acceptance.

## Wave 3 — serial integration (root Codex)

The merge owner:

1. Reviews lane diffs and scope manifests; rejects overlapping or unrelated edits.
2. Connects shared exports/registries and deterministic evidence serialization.
3. Creates the canonical executable SSpec using the frozen helpers and all
   `MCI-*` scenario IDs; every REQ/NFR has real happy, edge, and failure evidence.
4. Implements traceability and aggregate runners without rerunning subordinate
   green gates; the aggregate consumes their correlated manifests.
5. Runs docgen once after the final spec edit and verifies `0 stubs` plus the
   `doc/06_spec` layout invariant.
6. Runs direct-env working/staged audits and any compiler/lib/MCP/LSP mandatory
   checks triggered by the actual diff, each at most once after its final edit.
7. Runs the single release-facing gate and requires
   `release_blockers=none`.

Root Codex owns REQ-MCI-010 and REQ-MCI-011 integration and NFR-MCI-009 schema,
traceability, generated-manual, and review plumbing. Lane evidence cannot
self-promote to an aggregate PASS.

### Aggregate runner state (2026-08-12)

- Implemented: host-independent `check-mci-v2-aggregate.shs` admission for the
  fixed compiler/tooling/SimpleOS/rendering/allocation/process/stress/docs/
  reviewer rows, including canonical receipt and artifact re-hashing, exact
  run/source/configuration/freshness correlation, stable scenario mapping, and
  deterministic resume/report output. Independent review hardening added
  same-directory private snapshots, regular-file/symlink/path confinement,
  bounded capture/lifetime validation, real producer-class attestation,
  aggregate ownership of `MCI-AGG-001/002/003`, executable-owner-only resume
  commands, and sync/atomic-rename/post-publication hash verification.
- Verified locally: focused script contract covers complete PASS plus stale,
  mutated-hash, and missing-receipt BLOCKED behavior.
- Still BLOCKED: all real hardware, QEMU, 24-hour stress, GPU/RenderDoc, and
  other lane executions not represented by fresh same-run receipts. This work
  did not execute or promote any of those rows. The canonical release
  entrypoint is absent, so release is BLOCKED rather than runnable.

## Wave 4 — independent final review

### Evidence-refresh progress — 2026-08-11

- Storage formal producer: PASS; retained hash-bound DB/FAT32/NVFS log.
- Memory-safety formal producer: PASS; retained hash-bound GC reachability,
  no-allocation boundary, manual-borrow, pointer-borrow, and no-GC compilation
  log at `build/evidence/mci-v2/formal-memory-20260811/`.
- These are model-only results. Native/codegen correspondence, actual
  concurrency, QEMU/hardware, aggregate, and release evidence remain pending.
- Critical-concurrency formal producer: PASS once; 85 theorem assertions across
  five Lake projects/14 Lean files, with hash-bound receipt at
  `build/evidence/mission_critical_infra_hardening_v2/critical_concurrency_20260811/`.
  This is model-only evidence; implementation/runtime correspondence and actual
  deployed race freedom remain pending.
- CPU/SIMD Engine2D producer: FAIL once with
  `simple-bin-simd-smoke-failed`. The explicit release candidate passed binary
  identity/symbol admission but segfaulted in the required interpreter smoke,
  before exact-bitmap or facade evidence ran. Current report:
  `doc/09_report/cpu_simd_engine2d_evidence_2026-08-11.md`; hash-bound receipt:
  `build/cpu-simd-engine2d-evidence-20260811/receipt.md`. Repair/rebuild the
  self-hosted candidate before a fresh producer cycle; do not promote the
  CPU/SIMD, GPU, QEMU, aggregate, or release rows from this result.
- RISC-V dual-track producer: FAIL once after its eight-fixture sidecar
  negative-control self-test passed; the production lane rejected the selected
  Rust bootstrap seed before BYL/Lean checking. Hash-bound receipt:
  `build/evidence/mission_critical_infra_hardening_v2/riscv_dual_track_20260811/receipt.md`.
  Resume only with an exact-current admitted pure-Simple compiler. Keep the
  formal dual-track, RTL/SBY, QEMU, FPGA, aggregate, and release rows RED.

The highest-capability reviewer receives no implementation ownership. The
reviewer checks every REQ-MCI-001..011 and NFR-MCI-001..009 against the current
source, executable scenarios, raw evidence, generated manual, and one-run gate
results. Required red-team probes include stale/cached/cross-run evidence,
unknown compiler identity, unavailable platform, capacity+1 Draw IR, post-ready
critical allocation, every allocation failure point, cross-domain mutation,
PID `-1`/`0`, output flood, hung child, screenshot-only rendering, invalid
RenderDoc, missing budget, and altered reviewer metadata.

The reviewer writes a canonical, separately signed acceptance/rejection receipt
binding reviewer identity/role/scope, run/source/configuration, decision time,
expiry, and the exact pre-review aggregate candidate hash. The gate rejects
same-key/self-issued, missing, stale, and replayed decisions. The focused shell
fixture uses ephemeral distinct keys only to prove this contract; operating the
real independent reviewer producer remains outside the merge owner. WARN cannot satisfy a
mission-critical release claim. Any missing, indirect, or unexercised evidence
is FAIL/BLOCKED and returns to the owning lane through root Codex. Release is
blocked for REQ-MCI-009 until the canonical facade registry, atomic slot synchronization,
and spawn/process-group signal/registered reap syscall integration have executable evidence.
eligible only after the independent receipt accepts all 20 requirements and
the aggregate reports `release_blockers=none`.
