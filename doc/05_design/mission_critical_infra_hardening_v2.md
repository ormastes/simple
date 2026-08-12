<!-- codex-design -->
# Mission-Critical Infrastructure Hardening V2 — Detail Design

Status: implementation design for selected `C1 + O1 + R2 + M2 + N2`
Requirements: `doc/02_requirements/feature/mission_critical_infra_hardening_v2.md` and `doc/02_requirements/nfr/mission_critical_infra_hardening_v2.md`

## 1. Design invariants

1. Admission is fail-closed: only an aggregate whose required receipts are fresh, identified, executable, and `pass` may publish a release claim.
2. Every externally persisted contract below has an explicit `schema_version = 1`, except `CertifiedPlatformManifestV1`, whose sole accepted wire contract is `schema_version = 2`; each has canonical serialization and a content hash over all fields except its own hash/signature field. Unknown versions and fields are rejected, not ignored.
3. Ready-state critical paths do not allocate. The relaxed profile permits allocation only from a preallocated, sealed, domain-local arena in an explicitly allowed context.
4. Draw IR count, plan, admit, encode, and publish are distinct phases. Nothing becomes visible to Engine2D until the complete generation commits.
5. No failure path truncates, clamps, retries into an unbounded allocator, reuses stale evidence, or mutates the last committed generation.
6. All bounds are checked with overflow-detecting integer arithmetic before an offset, byte size, deadline, PID, or capacity is used.

## 2. Versioned contracts

The implementation uses value types and composition; wire enums use stable integer codes and retain a diagnostic text rendering outside the signed/hash domain.

### 2.1 Common identity and evidence values

```text
ArtifactIdentityV1 {
  schema_version: u16, kind: ArtifactKind,
  sha256: Hash256, size_bytes: u64,
  source_tree_hash: Hash256?, build_config_hash: Hash256?,
  canonical_path: text
}

ExecutionIdentityV1 {
  run_id: Uuid128, check_id: text, attempt: u16,
  host_id: Hash256, guest_id: Hash256?,
  started_utc_ns: i64, ended_utc_ns: i64,
  timeout_ms: u64, command_hash: Hash256,
  exit_kind: ExitKind, exit_code: i32?,
  stdout_artifact: ArtifactIdentityV1?, stderr_artifact: ArtifactIdentityV1?
}

EvidenceReceiptV1 {
  schema_version: u16, evidence_kind: EvidenceKind,
  subject: ArtifactIdentityV1, execution: ExecutionIdentityV1,
  configuration_hash: Hash256, result: EvidenceResult,
  reason: EvidenceReason, artifacts: [ArtifactIdentityV1],
  valid_until_utc_ns: i64, receipt_hash: Hash256
}
```

`EvidenceResult` is `pass | fail | blocked`; there is no `skip`. Missing prerequisites produce `blocked`. A receipt is invalid when timestamps are inverted, its validity interval has ended, identities are unknown/zero, an artifact cannot be re-hashed, output capture exceeded its declared bound, or the run/configuration IDs do not match the aggregate.

### 2.2 `CompilerAdmissionReceiptV1`

```text
CompilerAdmissionReceiptV1 {
  schema_version: u16,
  compiler: ArtifactIdentityV1,
  compiler_lineage: CompilerLineage,       // must be pure_simple_exact_current
  source_revision: Hash256,
  bootstrap_parent: ArtifactIdentityV1,
  build_environment_hash: Hash256,
  clean_build_a: EvidenceReceiptV1,
  clean_build_b: EvidenceReceiptV1,
  reproducible_output_hash: Hash256,
  fixtures: [CompilerFixtureReceiptV1],
  result: EvidenceResult,
  reason: CompilerAdmissionReason,
  receipt_hash: Hash256
}

CompilerFixtureReceiptV1 {
  fixture_id: text, source_hash: Hash256,
  expected_semantic_hash: Hash256,
  emitted_artifact: ArtifactIdentityV1,
  build_execution: ExecutionIdentityV1,
  run_execution: ExecutionIdentityV1,
  observed_semantic_hash: Hash256,
  result: EvidenceResult
}
```

The builder first proves both clean-host outputs byte-identical, then runs a fixed, versioned discrimination corpus. The corpus includes function call/return, control flow, aggregate layout, error propagation, module linkage, and a negative missing-function fixture. Each positive emitted artifact must execute and match its semantic oracle. The negative fixture must fail with the specified diagnostic class. Rust-seed/hybrid/stale lineage, a non-executable output, an omitted fixture, or a build/run identity mismatch yields `blocked` or `fail`; it can never be represented as PASS.

### 2.3 `CertifiedPlatformManifestV1`

```text
CertifiedPlatformManifestV1 {
  schema_version: u16, release_id: text,
  source_revision: Hash256, compiler_receipt_hash: Hash256,
  rows: [CertifiedPlatformRowV1],
  matrix_shape: PlatformMatrixShapeV1,
  manifest_hash: Hash256
}

CertifiedPlatformRowV1 {
  row_id: text, selected: bool,
  host: PlatformIdentityV1, guest: PlatformIdentityV1,
  image: ArtifactIdentityV1, config_hash: Hash256,
  run_id: Uuid128?,
  boot: EvidenceReceiptV1?, mount: EvidenceReceiptV1?,
  target_listing: EvidenceReceiptV1?,
  arbitrary_program: EvidenceReceiptV1?,
  compiler_lineage: EvidenceReceiptV1?,
  source_identity: EvidenceReceiptV1?,
  payload_placement: EvidenceReceiptV1?,
  stress_24h: EvidenceReceiptV1?,
  result: EvidenceResult, reason: PlatformReason
}
```

The manifest always serializes all 24 matrix cells in stable `row_id` order. Unselected rows carry `selected = false`, no PASS result, and remain visible in reports. A selected row passes only when every receipt exists, has the same `run_id`, source revision, guest/image/config identity, and proves target-side execution. Payload placement evidence hashes and executes the guest-resident compiler/interpreter/loader at canonical `/usr/bin`, `/bin`, `/sys/apps`, and `/SYS/SIMPLETOOL.SDN` locations. Host-side inspection alone is invalid. An umbrella platform claim is permitted only if every row in the named umbrella set is selected and passes.

### 2.4 `DrawIrV3GenerationArena`

```text
DrawIrV3CountsV1 {
  commands, geometries, paints, text_runs, glyphs, resources,
  path_spans, path_points, clips, transforms, hit_shapes: u32
}

DrawIrV3PlanV1 {
  generation: u64, source_revision: u64,
  counts: DrawIrV3CountsV1,
  byte_offsets: DrawIrV3OffsetsV1, total_bytes: u64,
  queue_slots: u32, profile_hash: Hash256, plan_hash: Hash256
}

DrawIrV3GenerationArena {
  arena_id: u64, capacity_bytes: u64,
  slot_count: u8, committed_slot: u8,
  next_generation: u64,
  slots: FixedArray<DrawIrV3GenerationSlot>,
  queue: FixedRing<DrawIrV3Submission>, telemetry: DrawIrV3ArenaTelemetry
}

DrawIrV3GenerationSlot {
  state: free | admitted | encoding | committed | in_flight,
  generation: u64, plan: DrawIrV3PlanV1?, used_bytes: u64,
  packed_storage: FixedByteRegion, content_hash: Hash256
}
```

The producer walks the canonical GUI scene or Web semantic/layout output once to count exact rows and variable payload units. Planning computes aligned column offsets using checked multiply/add, validates referential/index limits and the certified profile, and derives `plan_hash`. Admission atomically reserves one free fixed slot and queue credit only when every count, byte, and in-flight limit fits. Encoding performs a second deterministic walk into the admitted ranges; each writer owns a cursor/end pair and rejects any mismatch. Finalization requires every cursor to equal its planned end and verifies structural references before hashing. Publication changes `encoding -> committed` in one ownership-publication operation and enqueues the immutable generation. Engine2D accepts only the queued `generation + arena_id + content_hash`; GUI/Web may not submit a parallel private representation.

Font shaping may contribute durable glyph IDs/positions to packed Draw IR, but transient atlas pages, caches, renderer batches, and device handles are created and owned by Engine2D after admission and never enter the arena contract.

### 2.5 Rendering receipts

```text
DrawIrV3RejectionReceiptV1 {
  arena_id: u64, generation: u64, plan_hash: Hash256?,
  phase: count | plan | admit | encode | validate | queue,
  reason: DrawIrV3RejectReason, requested: u64,
  limit: u64, dimension: DrawIrV3Dimension,
  last_committed_generation: u64
}

RenderExecutionReceiptV1 {
  arena_id: u64, generation: u64, content_hash: Hash256,
  backend: text, backend_binary: ArtifactIdentityV1,
  physical_device_id: text?, driver_hash: Hash256?,
  frame_profile_hash: Hash256, queue_depth: u32,
  cpu_readback_hash: Hash256?, device_readback_hash: Hash256?,
  interaction_trace: ArtifactIdentityV1?,
  renderdoc_capture: ArtifactIdentityV1?,
  result: EvidenceResult, reason: RenderEvidenceReason
}
```

HTML-backed UI PASS requires a structured input/action/semantic-target/output trace correlated to the generation; a screenshot alone is never interaction evidence. Claims of exact pixels require exact readback hashes. GPU/device claims require non-synthetic physical device and driver provenance. Profiles that require RenderDoc must include a parseable capture whose frame/generation markers match the receipt.

### 2.6 `RelaxedAllocationProfileV1`

```text
RelaxedAllocationProfileV1 {
  schema_version: u16, profile_id: text,
  domains: [AllocationDomainPolicyV1],
  forbidden_context_mask: u64,
  profile_hash: Hash256
}

AllocationDomainPolicyV1 {
  domain_id: u32, quota_bytes: u64, alignment: u32,
  max_allocations_per_generation: u32,
  allowed_context_mask: u64,
  rollback_mode: checkpoint_rewind,
  cross_domain_references: false
}

SealedDomainArenaV1 {
  arena_id: u64, domain_id: u32, generation: u64,
  base: ptr, quota_bytes: u64, cursor_bytes: u64,
  high_water_bytes: u64, overflow_count: u64,
  allocation_count: u32, sealed: bool,
  checkpoint: ArenaCheckpointV1,
  committed_state: ArenaCommittedSnapshotV1,
  # Compatibility-only output mirrors; operational logic never reads them.
  committed_generation: u64,
  committed_cursor_bytes: u64,
  committed_allocation_count: u32,
  publication_epoch: u64
}

ArenaCheckpointV1 {
  generation: u64, cursor_bytes: u64,
  allocation_count: u32, publication_epoch: u64
}

ArenaCommittedSnapshotV1 {
  generation: u64, cursor_bytes: u64,
  allocation_count: u32, publication_epoch: u64
}

ArenaFailureInjectionLedgerEntryV1 {
  schema_version: u16, run_id: text,
  fault_point: u16, fault_name: text, occurrence: u16,
  subject_arena_id: u64, subject_generation: u64,
  isolated_arena_id: u64, isolated_generation: u64,
  subject_before_hash: Hash256, subject_after_hash: Hash256,
  isolated_before_hash: Hash256, isolated_after_hash: Hash256,
  injected: bool, rolled_back: bool,
  row_hash: Hash256
}

AllocationExhaustionV1 {
  arena_id: u64, domain_id: u32, generation: u64,
  requested_bytes: u64, remaining_bytes: u64,
  reason: quota | alignment_overflow | allocation_count | forbidden_context |
          unsealed | generation_mismatch,
  high_water_bytes: u64
}
```

The V1 arena registers exactly two deterministic one-shot injection boundaries:
`before_cursor_advance` and `before_publication`. Arming any other identifier or
arming outside an open transaction fails closed. The allocation boundary returns
a typed `injected_fault` exhaustion before cursor mutation. The publication
boundary rejects commit before epoch/generation publication and leaves the
transaction available for deterministic rollback. Injection telemetry is
monotonic and saturating. Tests must exercise both registered points, prove the
last committed generation remains valid, and prove a separately committed
domain is unchanged.

`arena_failure_point_count_v1` plus indexed lookup is the completeness
authority; each stable ID resolves to its canonical name. Evidence is one
`ArenaFailureInjectionLedgerEntryV1` per registry row. Every row must carry
schema version 1, a non-empty run ID, occurrence 1, the registered point ID and
name, distinct nonzero subject/isolated arena IDs, and their positive committed
generations. A valid row requires successful injection and rollback, and equal
64-character lowercase hexadecimal SHA-256 committed-state hashes before/after
for both the subject arena and an independently committed arena.

`row_hash` is recomputed from a version-tagged, fixed-order, length-framed
canonical serialization of every row field except `row_hash` itself: schema,
run, point ID/name, occurrence, arena IDs/generations, all four snapshot hashes,
and both outcomes. Aggregate validation requires exactly one unique valid row
for every registered point. `arena_failure_injection_ledger_complete_v1`
separately accepts seven scalar expectations: `run_id`, `subject_arena_id`,
`subject_generation`, `subject_snapshot_hash`, `isolated_arena_id`,
`isolated_generation`, and `isolated_snapshot_hash`. Consequently, changing a
label and recomputing `row_hash`,
replaying a row from another run or generation, omitting/duplicating a point,
or swapping subject and isolated evidence remains rejected.

The committed-state hash deliberately excludes
attempt telemetry and staging state, while binding arena/domain identity,
profile hash, committed generation/extent/count, and publication epoch.

At initialization, the owner allocates each arena at its hard quota, binds it to one domain, and seals the profile before readiness. `arena_try_alloc<T>(arena, count, context)` checks context, generation, count, multiplication, alignment, quota, and allocation-count bounds, then advances the cursor and returns `Result<ArenaRef<T>, AllocationExhaustionV1>`. It never invokes a general allocator. Arena references contain arena/domain/generation plus an offset, not a freely transferable raw owner.

Work begins from `checkpoint()`. Objects remain private to the arena transaction until validation succeeds. `commit(checkpoint)` constructs and validates a complete committed snapshot, then makes it visible with one owner-state assignment; compatibility mirrors are not publication authority. On any error, `rollback(checkpoint)` clears publication candidates, rewinds cursor/allocation count deterministically, restores the last committed visible generation, and leaves the reserved next-generation counter monotonic so the next checkpoint is fresh. Rollback cannot cross a committed checkpoint. Kernel, ISR, storage-commit, ownership-publication, and policy-declared critical contexts reject before cursor mutation. Cross-domain ownership is forbidden; explicit copying through a bounded port is required.

## 3. Unified admission and evidence aggregation

```text
MissionCriticalAdmissionRequestV1 {
  release_id: text, source_revision: Hash256,
  policy_hash: Hash256, manifest_hash: Hash256,
  required_check_ids: [text], deadline_utc_ns: i64
}

MissionCriticalAdmissionResultV1 {
  schema_version: u16, request_hash: Hash256,
  compiler: CompilerAdmissionReceiptV1,
  platform_manifest: CertifiedPlatformManifestV1,
  evidence: [EvidenceReceiptV1],
  rendering: [RenderExecutionReceiptV1],
  allocation: [AllocationEvidenceReceiptV1],
  result: EvidenceResult,
  blockers: [AdmissionBlockerV1], aggregate_hash: Hash256
}
```

The policy expands `required_check_ids` to compiler, one tooling manifest, rendering, allocation/fault-injection, process safety, selected-platform checks, traceability, stress, and independent review. The tooling owner records library, MCP, LSP, bootstrap-essential tools, lint, duplication, whole-test, runtime contract, direct-env, and startup/latency/RSS as rows inside that single manifest; the aggregate must not duplicate the same tooling scenario ownership into parallel top-level receipts. The runner admits a fixed number of jobs to the existing bounded runtime pool. Each job has a deadline, bounded stdout/stderr capture, fixed artifact directory, and deterministic cancellation. Subprocess launch records the positive PID before registration; every kill/wait API rejects `pid <= 0`. Timeout kills the registered process group once, performs a bounded reap, and emits a blocked receipt if termination cannot be proven.

Aggregation is a pure, stable-order fold keyed by `check_id`; duplicate, unexpected, missing, stale, skipped, wrong-run, wrong-source, wrong-config, or invalid-hash receipts become explicit blockers. Cryptographic verification uses identity-stable snapshots of the trusted public key, receipt, artifact, and detached signature; changing any source during its snapshot fails closed instead of mixing generations. Cached artifacts may be inputs only when policy names them and their producing receipt is part of the same valid evidence graph; cached reports cannot directly satisfy a required check. `collector_contract=PASS` means only that collector validation, rejection, ordering, and publication mechanics passed `MCI-AGG-001/002/003`; release `result=PASS` additionally requires zero blockers and all real producer receipts. The reviewer signs the content-addressed pre-review evidence graph as `aggregate_candidate_sha256`, not the display-row summary. That graph binds policy/header and ordered required IDs; every non-review canonical/raw receipt digest, receipt hash field, detached-signature digest, declared and verified artifact digest; blocker and resume-owner state; and the complete unexpected-receipt name/digest set. Thus valid-to-valid evidence replacement and unexpected-set addition/removal require a new decision. The separately pinned reviewer decision binds identity, `independent-release-reviewer` role, `mci-v2-aggregate` scope, run, source, configuration, decision time, expiry, approval, and candidate hash. Same-key/self-issued, missing, stale, replayed, malformed, or non-approval decisions fail closed. The verifier contract is executable, but the independently operated reviewer producer remains an operational prerequisite; the focused test's ephemeral reviewer is contract evidence, not a real review. The aggregate writes to a temporary generation, fsyncs/verifies it, then atomically publishes the content-addressed result; a failed write leaves the prior result intact but cannot make it current for the new request.

## 4. Module interactions and ownership

```text
release admission owner
  -> compiler admission port -> compiler/build/fixture executors
  -> platform certification port -> SimpleOS host/guest runner
  -> verification port -> bounded runtime pool/process facade
  -> evidence validator/aggregator -> content-addressed evidence store

GUI semantic owner ----\
                       -> DrawIrComposition -> DrawIR-v3 count/plan/admit/encode
Web semantic/layout ---/                         -> immutable generation queue
                                                    -> Engine2D -> backend receipt

domain owner -> sealed arena transaction -> validate -> domain publication port
                                      \-> typed exhaustion -> rollback
```

The admission layer depends only on ports and V1 values. Compiler, OS, rendering, process, and allocation owners implement those ports in their existing layers; they do not import the aggregate owner. Evidence validation occurs both at receipt ingestion and immediately before aggregate publication. Hot MCP/LSP requests never invoke the aggregate, scan the repository, or spawn admission subprocesses; admission is an explicit maintenance/release operation.

## 5. Error and recovery matrix

| Failure | Required result | State after failure |
|---|---|---|
| Compiler lineage stale/unknown/hybrid | blocked | no compiler/release claim |
| Emitted fixture missing or non-executable | fail | receipt retained as negative evidence |
| Evidence absent/stale/hash mismatch | blocked | prior aggregate remains historical only |
| Platform unavailable or selected row incomplete | blocked | row and umbrella claim blocked |
| Count/size/index overflow | typed Draw IR rejection | no slot or queue mutation |
| Arena/queue capacity exceeded | typed rejection/exhaustion | last committed generation unchanged |
| Encode count differs from plan | typed encode mismatch | admitted slot released after generation invalidation |
| Backend/device provenance missing | blocked render receipt | rendering claim blocked |
| Allocation attempted in forbidden context | typed exhaustion/policy error | cursor and publication unchanged |
| Fault after private allocation | error plus rollback receipt | checkpoint restored; generation invalidated |
| Timeout/cancellation | blocked receipt | bounded process-group termination and reap evidence |
| Invalid PID | process-contract failure | no signal/wait syscall issued |

All public operations return `Result<T, E>` with the typed errors above. Panics/assertions are reserved for detected internal invariant corruption and must transition the owning service to a non-admitting safe state; they are never converted into PASS.

## 6. Certified budgets

Each certified profile may tighten these values, but cannot omit a field or exceed the initial ceiling without a new reviewed profile hash.

| Budget | Initial ceiling / gate |
|---|---|
| Admission parallelism | 8 jobs maximum; fixed queue 64; fixed in-flight subprocesses 8 |
| Per-check capture | 16 MiB stdout + 16 MiB stderr; overflow blocks the check |
| Check duration | explicit per check, 30 min maximum; aggregate 6 h maximum excluding separately correlated 24 h stress |
| Evidence freshness | generated from the exact release request; compiler/platform/runtime evidence maximum age 24 h |
| Warm CLI | p95 <= 250 ms, max RSS <= 256 MiB |
| Warm MCP startup / request | p95 startup <= 500 ms; p95 request <= 100 ms; max RSS <= 512 MiB |
| Warm LSP startup / request | p95 startup <= 1.5 s; p95 representative request <= 150 ms; max RSS <= 768 MiB |
| Performance regression | p95 and max RSS no more than 5% above the recorded approved baseline, while also meeting absolute ceilings |
| Draw IR commands / frame | 65,536 |
| Glyphs / frame | 262,144 |
| Images / frame | 4,096 |
| Path points / frame | 1,048,576 |
| Packed generation bytes | 64 MiB |
| Generation slots / queue / in-flight | 3 / 8 / 2 |
| Rendering latency | p95 <= 16.67 ms, p99 <= 25 ms, worst-case deadline <= 50 ms for the certified 60 Hz profile |
| Rendering RSS | profile baseline + 128 MiB maximum; <= 5% regression |
| Relaxed arena nominal stress | high-water <= 80% of each declared hard quota |
| Allocation exhaustion response | returned synchronously within the provoking operation; no retry/fallback |
| Platform stress | 24 continuous hours per selected row with fixed resource ceilings and zero unaccounted restart |

Benchmarks use versioned realistic fixtures, at least 30 warm samples for CLI startup and 1,000 representative requests/frames for request/render percentiles. Receipts record sample count, fixture/configuration hashes, raw timing artifact, p50/p95/p99/max, and max RSS. A machine/profile change creates a new baseline rather than silently resetting regression history.

## 7. Verification and traceability

| Requirement | Executable evidence obligation |
|---|---|
| REQ-MCI-001, NFR-MCI-001/002 | exact-current receipt; two clean builds; executed discrimination corpus and negative lineage controls |
| REQ-MCI-002, 009/010; NFR-MCI-003/007 | aggregate completeness/duplicate/stale controls; `bounded_process_policy_spec.spl` proves generation-bound reservation/release receipts, identity-bound owner leases, sequenced `TerminationRequested -> ReapPending -> Completed` only after registered reap acknowledgement, and checked incremental stdout/stderr chunks. Negative controls cover replay/stale races, PID reuse, forged PGID, concurrent last-slot reservation, and `limit + 1`. **BLOCKED:** atomic synchronization and canonical process-facade syscall integration are not implemented or claimed; warm latency/RSS evidence remains separate. |
| REQ-MCI-003/004 | all 24 manifest rows visible; selected-row boot/mount/list/execute/lineage/source/run/payload/stress evidence from target |
| REQ-MCI-005/006; NFR-MCI-006 | count/plan/admit boundaries; every dimension overflow; no partial generation; backend/device/readback/interaction/RenderDoc provenance |
| REQ-MCI-007/008; NFR-MCI-004/005 | strict zero-allocation counters; allowed/forbidden context matrix; every injectable failure; isolation and deterministic rollback |
| REQ-MCI-011, NFR-MCI-009 | REQ-tagged non-placeholder SSpec, readable generated operator flow, exact hashes/commands/times/artifacts, final reviewer identity |

Negative controls must deliberately corrupt each identity/hash, expire evidence, omit each required receipt in turn, use synthetic backend handles, overflow each packed column and queue, inject failure at every arena allocation/publication boundary, and pass `0` and negative PIDs. Success assertions must also prove the prior committed generation/storage/domain state is byte-identical after each rejected operation.

## 8. Migration sequence

## 9. Implemented correction details (2026-08-11)

The first implementation/review wave refined four details that are normative
for subsequent adapters:

1. Compiler collectors emit the complete V2 hash-bound receipt; adapters may
   not reduce it to trusted booleans or a claimed function count.
2. SimpleOS subset certification uses the exact canonical 24-row catalog.
   `structurally_valid`, scoped `accepted`, and `umbrella_all_platforms` are
   distinct results; blocked/failed always imply `accepted = false`.
   Manifest serialization schema 2 records canonical `host_identity` on each
   row and receipt, includes it in the manifest hash, and rejects row or receipt
   host relabeling. Schema 1 is not admission-compatible. Existing `*V1`
   source names are retained only to avoid needless caller churn; schema 2 is
   the sole accepted wire contract. Freshness validation rejects future,
   expired/replayed, older-than-86,400-second, and longer-than-86,400-second
   receipt windows using ordered comparisons before unsigned subtraction.
3. DrawIR admission recomputes row/byte totals from counts and fixed packed
   layout metadata. Seal mismatch leaves no published generation and requires
   explicit abort before the next generation.
4. Allocation transactions build a private staging generation from offset
   zero. Commit replaces the visible generation atomically; rollback restores
   the prior committed extent and leaves its references valid. Checkpoint
   arena/domain/generation/cursor/count/epoch fields must exactly match the
   active recorded checkpoint.
5. The sealed allocation profile identity is canonical SHA-256 over its
   length-framed V1 fields; the earlier rolling modulo fingerprint is forbidden
   because multiplication could overflow before reduction.


1. **Contracts first:** add V1 identity, typed error, receipt, policy, and manifest values plus canonical encoders/decoders. Readers reject unknown schema versions. No existing gate may claim V1 PASS yet.
2. **Evidence adapters:** wrap existing compiler/tool/runtime/platform checks through bounded process and evidence ports. Keep old reports visible but mark them legacy/non-admitting. Add negative controls before enabling aggregation.
3. **Compiler and OS admission:** produce exact-current compiler receipts and the explicit 24-row platform manifest. Populate selected rows only from target-executed evidence. Gate release claims on these V1 receipts.
4. **Rendering shadow mode:** introduce packed generation arenas beside current construction, compare semantic/content oracles, measure capacities, and emit rejection telemetry without making the new path authoritative. No private producer-to-backend shortcut is added.
5. **Rendering cutover:** switch GUI and Web canonical owners to count-plan-admit; Engine2D consumes immutable queued generations. Remove active-generation growth/fallback paths only after equivalence and overflow suites pass.
6. **Allocation observe mode:** instrument post-ready allocations and assign domain/context IDs. Define quotas from measured peak plus reviewed headroom; unknown contexts remain strict-forbidden.
7. **Relaxed profile cutover:** preallocate and seal arenas before readiness, migrate one domain at a time, enable fault injection and rollback checks, then prohibit general allocation in migrated contexts. Kernel/ISR/storage/publication contexts never enter relaxed mode.
8. **Aggregate enforcement:** enable one V1 fail-closed result as the release admission authority. Legacy reports become diagnostic links only. Require the 24-hour row evidence and highest-capability review before broad platform claims.

Every migration step is reversible by selecting the previous release artifact, not by runtime fallback inside an admitted operation. Schema V1 remains readable for the release retention period; incompatible contract changes use V2 types and parallel readers rather than changing V1 semantics.
