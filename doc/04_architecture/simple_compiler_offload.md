<!-- codex-architecture -->
# Simple Compiler Offload Architecture

**Status:** Accepted for Wave 1 implementation
**Parent:** `doc/04_architecture/compiler/mdsoc/mdsoc_plus_tagged_structural_compute_architecture.md` Part III (§11)
**Plan:** `doc/03_plan/platform/structural_compute/simple_compiler_offload_plan.md`

## Decision

The Simple compiler's stages (lex/structure, parse, semantic/type, HIR/MIR, optimize, codegen, link) stay on unchanged primary IR arenas. Tags, origins, query indexes, and profile data ride alongside as content-addressed sidecar shards, crossing each MDSOC transform boundary through a deterministic `SidecarMapper`. Extended feature ports (`ParsingOutputPort`, `OptimizationInputPort`/`OptimizationOutputPort`, `LinkingInputPort`) carry refs and `StageReceipt`s only — never payload. `CompilerOffloadProfile` selects `cpu_reference` / `hybrid_vector_gpu` / `resident_gpu` per stage as configuration, not a build variant: one binary, mode is data. `cpu_reference` is the never-deleted oracle and must run with no GPU present; all three modes must produce identical artifact hashes.

<!-- sdn-diagram:id=simple_compiler_offload.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_compiler_offload.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

FileHashCache -> LexStructure
LexStructure -> Parse
Parse -> SemanticType
SemanticType -> HirMir
HirMir -> Optimize
Optimize -> Codegen
Codegen -> Link
SidecarBundle -> SidecarMapper
SidecarMapper -> Parse
SidecarMapper -> SemanticType
SidecarMapper -> HirMir
SidecarMapper -> Optimize
SidecarMapper -> Codegen
SidecarMapper -> Link
CompilerOffloadProfile -> OffloadDecision
OffloadDecision -> LexStructure
OffloadDecision -> StageReceipt
StageReceipt -> ParityCheck
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_compiler_offload.arch hash=sha256:auto
FileHashCache -> LexStructure -> Parse -> SemanticType -> HirMir -> Optimize -> Codegen -> Link
                      ^            ^         ^              ^          ^          ^         ^
                      +------------+---------+----- SidecarMapper -----+----------+---------+
                                       (SidecarBundle: tags/origins/indexes/profile, x7 boundaries)
CompilerOffloadProfile --stage_modes--> OffloadDecision --receipt--> StageReceipt --> parity check
                                              (cpu_reference / hybrid_vector_gpu / resident_gpu hash match)
```

</details>
<!-- sdn-diagram:end -->

## Modules

| Module | Path | Responsibility |
|---|---|---|
| Sidecar shards | `src/compiler/00.common/structural_contracts/sidecars.spl` | `ShardRef`, `TagShard`/`OriginShard`/`QueryIndexShard`/`MirProfileShard` SoA records |
| Ports + mappers | `src/compiler/00.common/structural_contracts/ports.spl` | View descriptors, per-stage ports, `TransformBoundary`, `SidecarMapper`, `SidecarError` |
| AOP frontend contracts | `src/compiler/00.common/structural_contracts/aop.spl` | Opaque `PointcutQueryRef`/`AdviceTemplateRef`, `AopRule`, `WeavingReceipt` (Wave 2) |
| Optimizer pass contracts | `src/compiler/00.common/structural_contracts/optimizer.spl` | `OptimizationPassContract`, `EffectSummary`, `OptimizationRemark` (Wave 2/3) |
| Offload profile | `src/compiler/00.common/structural_contracts/offload_profile.spl` | `CompilerStage`, `OffloadMode`, `CompilerOffloadProfile`, `OffloadDecision` |
| Public surface | `src/compiler/00.common/structural_contracts/__init__.spl` | Explicit re-export of every public name above; not a wildcard hub |
| MIR optimizer adapter (Wave 1+, not yet created) | `src/compiler/60.mir_opt/structural_adapter/` | Binds `OptimizationInputPort`/`OutputPort` to the pass manager |
| Tagging feature (Wave 2, not yet created) | `src/compiler/85.mdsoc/feature/tagging/` | Populates `TagShard` from AST/HIR/MIR passes |
| Query feature (Wave 2, not yet created) | `src/compiler/85.mdsoc/feature/query/` | QueryIR-backed pointcut/index evaluation |
| Mutation feature (Wave 2, not yet created) | `src/compiler/85.mdsoc/feature/mutation/` | MutationIR-backed advice/optimizer mutation application |
| Boundary sidecar transforms (Wave 1+, not yet created) | `src/compiler/85.mdsoc/transform/**/sidecars/` | Concrete `SidecarMapper` implementations per `TransformBoundary` |
| AOP adapters (Wave 2, not yet created) | `src/compiler/90.tools/` (aop adapters) | QueryIR/MutationIR frontend for `pc{...}` pointcuts and advice |
| Structural unit tests (Wave 1+, not yet created) | `test/01_unit/compiler/structural/` | Contract, mapper, and parity fixtures |

## Dependency rules

- Contracts import only the existing structural identity/tagmap/mapping/execution owners (`entity_id.spl`, `tag_schema.spl`, `mapping/contracts.spl`, `execution/contracts.spl`); no other cross-lane imports.
- No `rt_*` imports and no backend fields anywhere in `structural_contracts/`; ports carry refs and receipts, never payload or device handles.
- `QueryIR`/`MutationIR` are referenced only through opaque digest handles (`PointcutQueryRef.query_digest`, `AdviceTemplateRef.mutation_digest`); this lane never declares QueryIR opcodes or MutationIR plans.
- Compiler-stage adapters (`60.mir_opt`, `85.mdsoc/**`, `90.tools`) depend downward on `structural_contracts/`; contracts never import compiler adapter types.
- Common code (`src/lib/common/**`) never imports compiler types; the dependency arrow is one-way, adapter -> contract -> common owner.
- One `SidecarMapper` per `TransformBoundary`; mappers never import one another.

## Architecture decisions

- **ADR-OFF-1 — Sidecars, not wider nodes.** Primary IR arenas stay unchanged; tags/origins/indexes/profile ride in content-addressed shards keyed by (snapshot, slot, generation).
- **ADR-OFF-2 — Ports carry refs + receipts only.** No payload, no backend fields, no `rt_*` imports in contracts; deterministic digests make cross-mode parity checkable per stage.
- **ADR-OFF-3 — Opaque QueryIR/MutationIR handles.** The SIMPLE lane binds by digest + `contract_version`; it does not fork or embed the IR (QUERY/MUTATE lanes own it).
- **ADR-OFF-4 — Mode is config, not variant.** One binary; `CompilerOffloadProfile` selects per stage; `cpu_reference` is the never-deleted oracle.
- **ADR-OFF-5 — Fallback observable.** Every non-requested selection emits an `OffloadDecision` with reason + evidence digest; `RequireRequested` errors instead of silently falling back.
- **ADR-OFF-6 — Evidence-driven promotion.** Same as parser framework N2: a stage promotes off CPU only with matching identity, parity, and ≥1.5× median speedup evidence.

## MDSOC evaluation

The stage pipeline is the stable capsule; tagging, querying, mutation (AOP/optimizer), and offload mode selection are feature transforms that write through the same sidecar/port/receipt contract rather than widening IR nodes or forking per-stage state. `rules_enabled == 0` on the AOP path means zero weaving work and zero allocation, and output MIR/binary stays bit-identical to a build with AOP absent — the feature composes without reshaping the base capsule.

## Startup, hot path, caches, invalidation

Contract and mapper registration happens once per compiler process. Stage execution reads no environment variables and performs no filesystem scans in the hot compile path — profile selection (`CompilerOffloadProfile`) is resolved once at session start. Shards are invalidated by the triple (snapshot, generation, digest): a stale snapshot, a generation bump, or a digest mismatch forces regeneration rather than reuse. Column-length mismatches across a shard's SoA arrays are rejected at read, not silently truncated.

## Failure contract

`SidecarMapper.map` returns `Result<SidecarBundle, SidecarError>` with `SidecarErrorCode` in `{StaleShard, GenerationMismatch, ColumnLengthMismatch, UnknownBoundary, MappingIncomplete}`, each carrying the offending `TransformBoundary` and a message. `OffloadDecision.fallback_reason` is empty only when `requested == selected`; any other selection must carry a non-empty reason plus `evidence_digest`. Under `OffloadFallbackPolicy.RequireRequested`, a stage that cannot run in the requested mode returns an error instead of stepping down to `hybrid`/`cpu_reference`. `validate_offload_profile` rejects malformed profiles (wrong `stage_modes` length, inconsistent `execution` budgets) before any stage runs.
