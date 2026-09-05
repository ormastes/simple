# Feature: Simple Compiler Offload

## Raw Request
`$dev with agents teams impl simple_compiler_offload_plan.md`

Authoritative plan: `doc/03_plan/platform/structural_compute/simple_compiler_offload_plan.md`.

## Task Type
feature

## Refined Goal
Implement offloadable compiler architecture with deterministic sidecars at every MDSOC transform boundary (lexing→parsing, parsing→desugaring, typing→HIR, HIR→MIR, MIR→optimizer, MIR→backend, backend→linker), AOP QueryIR/MutationIR migration, optimizer structural pass contracts, and per-stage execution profiles (cpu_reference, hybrid_vector_gpu, resident_gpu, auto), with artifact hash parity across all three modes and zero allocation when offload is disabled.

## Acceptance Criteria
- AC-1: Six frozen contract files exist under `src/compiler/00.common/structural_contracts/` (sidecars.spl, ports.spl, aop.spl, optimizer.spl, offload_profile.spl, __init__.spl) with versioned exports matching the OFFLOAD_INTERFACE_GUIDE exactly.
- AC-2: One deterministic `SidecarMapper` trait implementation exists for each of the 7 MDSOC transform boundaries, with unit tests under `test/01_unit/compiler/structural/`.
- AC-3: Sidecars (TagShardRef, OriginShardRef, QueryIndexShardRef, ProfileShardRef) round-trip deterministically: same input shards + same boundary ⇒ identical output digests (Wave 1, CPU only).
- AC-4: Extended ports (ParsingOutputPort, OptimizationInputPort, OptimizationOutputPort, LinkingInputPort) and receipts carry only refs and counts; no payload or backend fields; deterministic stage digests enable cross-mode parity verification.
- AC-5: `CompilerOffloadProfile` validates per-stage OffloadMode selections; `cpu_only_profile()` runs on machines with no GPU; all three modes produce identical `StageReceipt.deterministic_hash` on the bootstrap corpus (stage-3 self-compilation).
- AC-6: AOP rules disabled (rules_enabled == 0) ⇒ zero weaving work and zero allocation; output MIR and binary are bit-identical to a build with AOP absent (Wave 2 gate).
- AC-7: `OptimizationPassContract` defines required/produced tags, mutation kinds, effect, legality verifier, backend policy, and cost model; existing pass registry migrated to QueryIR selectors (Wave 2/3).
- AC-8: Fallback selection carries a non-empty `fallback_reason` receipt; RequestRequired policy errors on non-requested mode; AllowCpu silently demotes (hybrid→cpu_reference, resident→hybrid→cpu_reference).
- AC-9: Dependencies (identity/tagmap/mapping/execution owners) are landed and imported; QUERY/MUTATE lanes are referenced only through opaque digest refs; parser_framework lane provides lex/parse acceleration; gpu_mmu lane owns resident placement (Waves 4/9 only).
- AC-10: Modern SSpec scenarios execute Wave 1 sidecar determinism, parity verification, receipt validation, and error-path coverage with direct value assertions and operator-readable Markdown under `doc/06_spec`; no executable `_spec.spl` exists under `doc/06_spec`.
- AC-11: Research, selected feature/NFR requirements, architecture, system-test plan, detail design, agent-task ownership, implementation, generated manual, and offload guide artifacts are current and mutually traceable.
- AC-12: Final high-capability review verifies cooperative merge, contract exactness, owned-path scope, deterministic evidence, and every AC against authoritative current-state evidence before the lane can report `STATUS: PASS`.

## Scope Exclusions
- QUERY/MUTATE lanes own QueryIR and MutationIR definitions; this lane binds only by digest + contract_version.
- gpu_mmu lane owns resident arena placement; Waves 1–2 are CPU only.
- parser_framework lane owns lex/structure acceleration; link_manager_plan.md owns SMF linker details.
- Diagnostics lane owns diagnostic arena and message transport.

## Cooperative Review
- Sidecar lanes: contract definitions + mappers; deterministic shard round-trip; receipt validation; parity evidence.
- Shared interfaces frozen before fan-out: `ShardRef`, `TagShard`, `OriginShard`, `QueryIndexShard`, `AstView`, `MirOptView`, `ParsingOutputPort`, `OptimizationInputPort`, `OptimizationOutputPort`, `LinkingInputPort`, `SidecarMapper`, `TransformBoundary`, `CompilerOffloadProfile`, `OffloadProfile`, `OffloadDecision`.
- Manual primary steps: `Map sidecars at each transform boundary`; `Collect shard digests per stage`; `Verify deterministic round-trip`; `Compare stage receipts across modes`; `Validate fallback policy and reasons`.
- Shared setup/checker helpers: `struct_offload_fixture`, `shard_round_trip_digest`, `expect_mappers_deterministic`, `expect_stage_receipts_equal`, `expect_offload_profile_valid`, and `expect_cpu_only_no_gpu_dependency`.
- Temporary implementations must fail explicitly with `assert(false)` or `fail(...)`; placeholder passes and hard-coded success results are forbidden.
- Merge owner and final reviewer: root Codex, normal/highest-capability review after all sidecar lanes; independent tests/manual sidecar owns the first generated-manual audit, root owns final acceptance.

## Research Summary
### Existing Code
- Frozen structural contracts in OFFLOAD_INTERFACE_GUIDE.md define six contract files with versioned exports.
- Existing compiler stages (frontend, typing, HIR, MIR, optimizer, codegen, linker) pass AST/HIR/MIR artifacts but lack structural sidecars (tags, origins, indexes, profiles).
- Current AOP implementation uses text-pattern pointcuts and line-pattern source matching; QueryIR/MutationIR owners (QUERY/MUTATE lanes) provide the underlying IR but are not yet landed.
- Existing `ExecutionProfile` and `StageReceipt` are imported from `src/lib/common/structural/execution/contracts.spl` and define budgets, devices, and stage evidence.

### Reusable Modules
- `src/lib/common/structural/identity/entity_id.spl` → `EntityRef`, `SnapshotId`, `ArtifactId`.
- `src/lib/common/structural/tagmap/tag_schema.spl` → `TagKey`, tag value/lifetime enums.
- `src/lib/common/structural/mapping/contracts.spl` → `MappingKind`, `MappingGraph`.
- `src/lib/common/structural/execution/contracts.spl` → `ExecutionProfile`, `CostEstimate`, `StageReceipt`.
- Compiler SoA AST/HIR/MIR pools, stable hash utilities, and evidence-receipt validation.
- parser_framework lane for lex/structure acceleration; gpu_mmu lane for resident placement (Waves 4/9).

### Domain Notes
- Sidecars are content-addressed shards (ShardRef identifies one arena segment per snapshot) and never embedded in primary IR.
- Ports carry refs, counts, and receipts only; no payload, no backend fields, no `rt_*` imports in contracts.
- Mode is configuration, not a build variant: one binary, per-stage OffloadMode selection; cpu_reference is the never-deleted oracle.
- Artifact hash parity (`StageReceipt.deterministic_hash`) across cpu_reference, hybrid_vector_gpu, and resident_gpu is the end-to-end test.
- Every fallback (when selected ≠ requested) must emit a non-empty `fallback_reason` in the `OffloadDecision` receipt.

### Open Questions
- NONE — user selected F2 complete phased offload and N2 balanced targets on 2026-07-31.

<!-- sdn-diagram:simple-compiler-offload-dependencies -->
```sdn
simple_compiler_offload = {
  stages: [lex_structure, parse, semantic_type, hir_mir, optimize, codegen, link]
  sidecars_per_boundary: 7
  contract_version: 1
  modes: [cpu_reference, hybrid_vector_gpu, resident_gpu, auto]
  deterministic: artifact_hash_parity
  consumers: [bootstrap_stage3, bootstrap_stage4]
}
```

## Requirements
- REQ-1 (AC-1/2): Frozen contract exports and deterministic mappers for 7 boundaries; shard round-trip digest stability — area: structural contracts + sidecar mapper implementations.
- REQ-2 (AC-3/4): Extended ports with refs/counts/receipts; no payload or backend fields — area: ports.spl + per-stage receipt collection.
- REQ-3 (AC-5/8): Per-stage OffloadMode selection, profile validation, cpu_reference oracle, cpu-only no-GPU guarantee, and fallback reasons — area: offload_profile.spl + execution policy.
- REQ-4 (AC-6): AOP zero-allocation invariant when disabled; bit-identical output — area: aop.spl + weaving gate.
- REQ-5 (AC-7): Optimizer `OptimizationPassContract` defines required/produced tags, mutation kinds, cost model, and backend policy — area: optimizer.spl + existing pass registry migration (Wave 2/3).
- REQ-6 (AC-9): Import identity/tagmap/mapping/execution from landed owners; reference QueryIR/MutationIR by opaque digest — area: __init__.spl + contracts.
- REQ-7 (AC-10/11): Modern SSpec manual plus focused unit/integration boundary coverage — area: test/doc.
- REQ-8 (AC-12): Traceable artifacts, cooperative review, guards, and authoritative final verification — area: plan/doc/verify.

## Architecture

### Module Plan
| Module | Path | Role |
|---|---|---|
| sidecar contracts | `src/compiler/00.common/structural_contracts/sidecars.spl` | ShardRef, TagShard, OriginShard, QueryIndexShard, ProfileShard (SoA columns) |
| port contracts | `src/compiler/00.common/structural_contracts/ports.spl` | AstView, MirOptView, ParsingOutputPort, OptimizationInputPort/Output, LinkingInputPort, SidecarMapper trait, 7 boundaries |
| AOP contracts | `src/compiler/00.common/structural_contracts/aop.spl` | PointcutQueryRef, AdviceTemplateRef, AopRule, WeavingReceipt (opaque QueryIR/MutationIR handles) |
| optimizer contracts | `src/compiler/00.common/structural_contracts/optimizer.spl` | OptimizationPassContract, EffectSummary, OptimizationRemark, BackendPolicy |
| offload profile | `src/compiler/00.common/structural_contracts/offload_profile.spl` | CompilerOffloadProfile, OffloadMode, OffloadDecision, cpu_only_profile() |
| re-exports | `src/compiler/00.common/structural_contracts/__init__.spl` | explicit public exports (no wildcard hub) |

### Dependency Map
- `identity → tagmap → mapping → execution` (all landed in `src/lib/common/structural/`); offload imports downward from there.
- `sidecars → ports → aop/optimizer/offload_profile → __init__` (acyclic within contracts).
- Compiler adapter (60.mir_opt/85.mdsoc/90.tools) imports contracts only; never redefines.
- QUERY/MUTATE lanes define QueryIR/MutationIR; SIMPLE lane references only by digest + contract_version.

### Decisions
- ADR-OFF-1: Sidecars, not wider nodes — primary IR arenas stay unchanged; tags/origins/indexes/profile ride in content-addressed shards keyed by (snapshot, slot, generation).
- ADR-OFF-2: Ports carry refs + receipts only — no payload, no backend fields, no `rt_*` imports; deterministic digests make cross-mode parity checkable per stage.
- ADR-OFF-3: Opaque QueryIR/MutationIR handles — SIMPLE lane binds by digest + contract_version; never forks or embeds the IR (QUERY/MUTATE own it).
- ADR-OFF-4: Mode is config, not variant — one binary; `CompilerOffloadProfile` selects per stage; `cpu_reference` is the never-deleted oracle.
- ADR-OFF-5: Fallback observable — every non-requested selection emits `OffloadDecision` with reason + evidence digest; `RequireRequested` policy errors.
- ADR-OFF-6: Evidence-driven promotion — a stage promotes off CPU only with matching identity, parity, and ≥1.5× median speedup evidence (same as parser framework N2).

### Public API
- `SidecarMapper` trait: `fn boundary() -> TransformBoundary`; `fn map(input, from_snapshot, to_snapshot) -> Result<SidecarBundle, SidecarError>`.
- `validate_offload_profile(profile: CompilerOffloadProfile) -> Result<(), text>`.
- `cpu_only_profile() -> CompilerOffloadProfile` (never touches GPU; runs on hosts with no GPU).
- `StageReceipt.deterministic_hash` parity across all three modes on bootstrap corpus.
- Shard round-trip digest: same input + same boundary ⇒ identical output digest (Wave 1, CPU only).

<!-- sdn-diagram:simple-compiler-offload-architecture -->
```sdn
Compiler Snapshot -> AstView/MirOptView/ObjectFileView
ParsingOutputPort/OptimizationInputPort/OptimizationOutputPort/LinkingInputPort
TagShardRef + OriginShardRef + QueryIndexShardRef + ProfileShardRef
SidecarMapper [7 boundaries]
CompilerOffloadProfile [cpu_reference | hybrid_vector_gpu | resident_gpu | auto]
StageReceipt.deterministic_hash (parity invariant)
```

### Requirement Coverage
- REQ-1/2 → sidecars.spl, ports.spl, 7 SidecarMapper implementations.
- REQ-3/4/5 → offload_profile.spl, aop.spl, optimizer.spl.
- REQ-6 → __init__.spl re-exports + opaque digest refs.
- REQ-7/8 → specs/manual/agent plan and final review.

## Phase
arch-done

## Phase
design-done

## Phase
research-done

## Log
- dev: Created state file with 12 acceptance criteria (type: feature); froze 6 contract files and 7 SidecarMapper boundaries before implementation fan-out.
- research: Authoritative plan (doc/03_plan/platform/structural_compute/simple_compiler_offload_plan.md) exists; frozen interface guide (OFFLOAD_INTERFACE_GUIDE.md) defines contract types exactly; Wave 1 (CPU-only sidecars + mappers) is next.
- requirements: Plan phase (Wave 1–5) covers offload modes, sidecar contracts, AOP/optimizer migrations, hybrid acceleration, and resident compilation; identity/tagmap/mapping/execution owners are landed; QUERY/MUTATE lanes not yet landed (referenced by opaque digest refs).
- arch: Froze 6 contract modules, 7 transform boundaries, SidecarMapper trait, 4 offload modes (cpu_reference/hybrid_vector_gpu/resident_gpu/auto), deterministic receipt model, and fallback policy.
- design: Frozen artifact list: sidecars.spl (CompilerIrKind, ShardRef, TagShard, OriginShard, QueryIndexShard, ProfileShard), ports.spl (AstView, MirOptView, ParsingOutputPort, OptimizationInputPort/Output, LinkingInputPort, SidecarMapper, 7 TransformBoundary variants), aop.spl (PointcutQueryRef, AdviceTemplateRef, AopRule, WeavingReceipt), optimizer.spl (OptimizationPassContract, EffectSummary, OptimizationRemark, BackendPolicy), offload_profile.spl (CompilerOffloadProfile, OffloadMode, OffloadDecision, cpu_only_profile), __init__.spl (re-exports).
- impl: Next — Wave 1 sidecar mapper implementations at 7 transform boundaries (LexingToParsing, ParsingToDesugaring, TypingToHir, HirToMir, MirToOptimizer, MirToBackend, BackendToLinker) + deterministic receipt collection + unit tests under test/01_unit/compiler/structural/.
