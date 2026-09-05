<!-- codex-design -->
# Simple Compiler Offload Detail Design

**Architecture:** `doc/04_architecture/simple_compiler_offload.md`
**Status:** Frozen interface, Wave 1 scope

## Frozen contracts

All five files live under `src/compiler/00.common/structural_contracts/`. Each
block below matches the frozen interface guide verbatim; only the leading
file-path comment is added.

**File 1 — `sidecars.spl`: sidecar shard descriptors** (§11 "sidecars, not
wider nodes"). Primary IR arenas (Ast/Hir/Mir) stay unchanged; tags, origins,
query indexes, and profiles ride alongside in content-addressed shards.

```simple
# src/compiler/00.common/structural_contracts/sidecars.spl
val COMPILER_SIDECAR_CONTRACT_VERSION: i64 = 1

enum CompilerIrKind:
    Ast
    Hir
    Mir

# Generic immutable shard descriptor: identifies one sidecar arena segment
# for one IR snapshot. All sidecar payloads are content-addressed.
struct ShardRef:
    ir: CompilerIrKind
    snapshot: SnapshotId
    shard_slot: u32           # arena-segment descriptor index
    generation: u32
    record_count: i64
    digest: text              # content digest of the shard payload

struct TagShardRef:
    shard: ShardRef

struct OriginShardRef:
    shard: ShardRef

struct QueryIndexShardRef:
    shard: ShardRef

struct ProfileShardRef:
    shard: ShardRef

struct DiagnosticArenaRef:
    shard: ShardRef

# Record layouts (SoA columns; all column lengths must be equal).
class TagShard:
    entities: [EntityRef]
    key_ids: [i64]            # TagKey ids from tagmap schema
    value_kinds: [i64]
    int_values: [i64]
    text_value_ids: [i64]     # -1 = no text payload

class OriginShard:
    sources: [EntityRef]      # entity in the PREVIOUS stage snapshot
    source_snapshots: [SnapshotId]
    targets: [EntityRef]      # entity in THIS stage snapshot
    kinds: [MappingKind]

class QueryIndexShard:
    namespace_ids: [i64]
    value_ids: [i64]
    entities: [EntityRef]

class MirProfileShard:
    entities: [EntityRef]
    execution_counts: [i64]
    sample_weights_milli: [i64]
```

Validation: every `TagShard`/`OriginShard`/`QueryIndexShard`/`MirProfileShard`
construction checks all parallel (SoA) arrays have equal length; a length
mismatch is rejected before the shard is published, never truncated or padded.

**File 2 — `ports.spl`: extended feature ports + sidecar mappers** (§11.1/§11.2).
Views over primary arenas carry identity and counts only; payload access goes
through the owning stage.

```simple
# src/compiler/00.common/structural_contracts/ports.spl
val COMPILER_PORT_CONTRACT_VERSION: i64 = 1

# Immutable view descriptors over primary IR arenas. Views carry identity and
# counts only; payload access goes through the owning stage.
struct AstView:
    snapshot: SnapshotId
    arena_slot: u32
    generation: u32
    node_count: i64
    root_count: i64
    digest: text

struct MirOptView:
    snapshot: SnapshotId
    arena_slot: u32
    generation: u32
    function_count: i64
    instruction_count: i64
    digest: text

struct ObjectFileView:
    artifact: ArtifactId
    symbol_count: i64
    section_count: i64
    digest: text

struct ParsingOutputPort:
    ast: AstView
    tags: TagShardRef
    origins: OriginShardRef
    indexes: QueryIndexShardRef
    diagnostics: DiagnosticArenaRef
    receipt: StageReceipt

struct OptimizationInputPort:
    mir: MirOptView
    tags: TagShardRef
    origins: OriginShardRef
    profile: ProfileShardRef?
    query_indexes: QueryIndexShardRef
    receipt: StageReceipt

struct MutationReceipt:
    plan_digest: text
    applied_count: i64
    rejected_count: i64
    conflict_count: i64
    deterministic_hash: text

struct OptimizationOutputPort:
    mir: MirOptView
    tags: TagShardRef
    origins: OriginShardRef
    mutation: MutationReceipt
    remarks: DiagnosticArenaRef
    receipt: StageReceipt

struct PlacementHintShardRef:
    shard: ShardRef

struct LinkingInputPort:
    objects: [ObjectFileView]
    tags: TagShardRef
    origins: OriginShardRef
    placement_hints: PlacementHintShardRef
    receipt: StageReceipt

# One mapper per MDSOC transform boundary (§11.2). Deterministic: same input
# shards + same boundary => identical output digests.
enum TransformBoundary:
    LexingToParsing
    ParsingToDesugaring
    TypingToHir
    HirToMir
    MirToOptimizer
    MirToBackend
    BackendToLinker

enum SidecarErrorCode:
    StaleShard
    GenerationMismatch
    ColumnLengthMismatch
    UnknownBoundary
    MappingIncomplete

struct SidecarError:
    code: SidecarErrorCode
    boundary: TransformBoundary
    message: text

struct SidecarBundle:
    tags: TagShardRef
    origins: OriginShardRef
    indexes: QueryIndexShardRef
    profile: ProfileShardRef?

trait SidecarMapper:
    fn boundary() -> TransformBoundary
    fn map(input: SidecarBundle, from_snapshot: SnapshotId, to_snapshot: SnapshotId) -> Result<SidecarBundle, SidecarError>
```

Validation: a shard is only readable once its `(snapshot, shard_slot,
generation)` triple is checked live and its `digest` recomputed to match —
otherwise `SidecarError{StaleShard | GenerationMismatch}` is returned, never a
silently-stale read. Every `SidecarMapper.map` result carries a `receipt`
whose `deterministic_hash` is a pure function of the input bundle and
boundary, so re-running a mapper is checkable by hash equality alone.

**File 3 — `aop.spl`: AOP QueryIR/MutationIR frontend contracts** (Wave 2,
§11.3). This lane never sees IR bytes; it addresses compiled QueryIR/MutationIR
programs by digest and validates versions at bind time.

```simple
# src/compiler/00.common/structural_contracts/aop.spl
val COMPILER_AOP_CONTRACT_VERSION: i64 = 1

# Opaque handles into the QUERY/MUTATE lanes. This lane never sees IR bytes;
# it addresses compiled programs by digest and validates versions at bind time.
struct PointcutQueryRef:
    query_digest: text        # digest of compiled QueryIR program
    dialect_id: text          # "simple.pointcut"
    contract_version: i64

enum PointcutSelectorKind:
    Attr
    Within
    Execution
    Call
    Assignment
    Decision
    Condition
    Error

enum AdviceKind:
    Before
    After
    Around

struct AdviceTemplateRef:
    mutation_digest: text     # digest of MutationIR template
    kind: AdviceKind
    contract_version: i64

struct AopRule:
    rule_id: text
    pointcut: PointcutQueryRef
    selectors: [PointcutSelectorKind]
    advice: AdviceTemplateRef

struct WeavingReceipt:
    rules_enabled: i64
    join_points_matched: i64
    mutations_applied: i64
    proceed_violations: i64   # must be 0 for success; around-advice proceed() exactly once
    receipt: StageReceipt
```

Invariant (document, enforce by test): `rules_enabled == 0` implies zero
weaving work and zero allocation on the compile path, and the output MIR/binary
is bit-identical to a build with AOP absent from the source. `proceed_violations`
must be `0`; a nonzero count means an around-advice mutation failed the
exactly-once `proceed()` legality check and is rejected, not silently applied.

**File 4 — `optimizer.spl`: optimizer pass contracts** (Wave 2/3, §11.4).
Replaces line-pattern source matching with structural required/produced tag
keys, mutation kinds, and a named legality verifier per pass.

```simple
# src/compiler/00.common/structural_contracts/optimizer.spl
val COMPILER_OPTIMIZER_CONTRACT_VERSION: i64 = 1

enum BackendPolicy:
    CpuOnly
    CostSelected
    ResidentEligible

struct EffectSummary:
    reads_memory: bool
    writes_memory: bool
    may_trap: bool
    pure: bool

struct OptimizationPassContract:
    pass_id: text
    input_schema: i64          # EntitySchemaId
    output_schema: i64
    required_tag_keys: [i64]
    produced_tag_keys: [i64]
    required_index_namespaces: [i64]
    mutation_kinds: [i64]
    effect: EffectSummary
    legality_verifier_id: text
    backend_policy: BackendPolicy
    cost_model_id: text

struct OptimizationRemark:
    pass_id: text
    entity: EntityRef
    remark_kind: i64           # applied / missed / cost-rejected
    message_id: i64
    hotness_milli: i64         # mapped from MirProfileShard via MappingGraph
```

Validation: a pass only runs when every `required_tag_keys` /
`required_index_namespaces` entry is present in the current sidecar bundle;
`backend_policy` gates whether the pass is eligible for `CostSelected` or
`ResidentEligible` dispatch at all, independent of the active
`CompilerOffloadProfile`.

**File 5 — `offload_profile.spl`: per-stage mode config** (plan "Variable
execution config", §21). Mode is configuration, not a build variant — one
binary, per-stage selection.

```simple
# src/compiler/00.common/structural_contracts/offload_profile.spl
val COMPILER_OFFLOAD_PROFILE_CONTRACT_VERSION: i64 = 1

enum CompilerStage:
    FileHashCache
    LexStructure
    Parse
    SemanticType
    HirMir
    Optimize
    Codegen
    Link

enum OffloadMode:
    CpuReference
    HybridVectorGpu
    ResidentGpu

enum OffloadFallbackPolicy:
    AllowCpu                  # hybrid -> cpu_reference; resident -> hybrid -> cpu_reference
    RequireRequested          # error instead of fallback

# Mode is configuration, not a build variant: one binary, per-stage selection.
struct CompilerOffloadProfile:
    profile_id: text          # "full_offload" | "balanced" | "cpu_only" | "auto"
    contract_version: i64
    stage_modes: [OffloadMode]  # indexed by CompilerStage ordinal; length 8
    fallback: OffloadFallbackPolicy
    deterministic: bool
    execution: ExecutionProfile  # budgets/devices from the EXEC owner

struct OffloadDecision:
    stage: CompilerStage
    requested: OffloadMode
    selected: OffloadMode
    fallback_reason: text     # empty when requested == selected
    evidence_digest: text

fn validate_offload_profile(profile: CompilerOffloadProfile) -> Result<(), text>
fn cpu_only_profile() -> CompilerOffloadProfile
```

Validation: `validate_offload_profile` rejects any profile whose `stage_modes`
length is not exactly `8` (one entry per `CompilerStage` ordinal, `FileHashCache`
through `Link`) before it is bound to a compile run. `cpu_only_profile()` never
touches GPU state — it sets every stage to `CpuReference` and must run
unmodified on hosts with no GPU present.

## Sidecar mapping algorithm

Wave 1 implements one `SidecarMapper` per `TransformBoundary` value
(`LexingToParsing`, `ParsingToDesugaring`, `TypingToHir`, `HirToMir`,
`MirToOptimizer`, `MirToBackend`, `BackendToLinker`). At each boundary, `map`:

1. Reads `from_snapshot`'s `OriginShard` to translate every entity ref carried
   in the `SidecarBundle` (tags, indexes, profile) from the old snapshot into
   `to_snapshot` coordinates.
2. Drops any record whose source entity has no `OriginShard` target — i.e. the
   entity was deleted by the transform (desugaring elision, dead-code removal,
   inlining) — rather than carrying forward a dangling ref.
3. Recomputes the output shard's content `digest` from the translated records.
4. Emits a `StageReceipt` inside the mapper's result wherever the boundary's
   port carries one (`ParsingOutputPort`, `OptimizationOutputPort`, …).

The mapper is deterministic and idempotent: the same `(input, from_snapshot,
to_snapshot)` triple always produces an output `SidecarBundle` with identical
digests, and record order is preserved from source order (no re-sorting), so
re-running a mapper twice is a no-op diff. `UnknownBoundary` is returned for
any `TransformBoundary` value not yet wired to a mapper; `MappingIncomplete`
is returned when the `OriginShard` does not cover every entity the input
bundle references.

## Mode selection and fallback

`OffloadDecision` mirrors the parser framework's `ParseModeDecision` protocol
(`doc/05_design/parser_framework.md`): `requested` and `selected` are recorded
separately, and `fallback_reason` is a single stable string, empty exactly
when `requested == selected`. Under `OffloadFallbackPolicy.AllowCpu`,
`resident_gpu` degrades to `hybrid_vector_gpu` and then to `cpu_reference` on
the first unmet precondition (missing device, cost-model rejection, evidence
gap); under `RequireRequested`, the same precondition failure returns an
error instead of ever running the CPU path for that stage. `evidence_digest`
identifies the benchmark row set (`ParseBenchmarkEvidence`-shaped rows, scoped
to `CompilerStage`) that justified the selection.

Promotion off `cpu_reference` for a given stage requires, per the plan's
Acceptance section: matching identity (dialect/schema/runtime/binary/source
revision), parity with the CPU oracle, and `scalar_median / optimized_median
>= 1.5`. A stage with no retained evidence for the requested mode always
selects `cpu_reference` under `AllowCpu`.

## Cross-mode parity protocol

All three `OffloadMode` values must produce an identical
`StageReceipt.deterministic_hash` for every stage, run over the bootstrap
corpus (stage-3 self-compilation as the end-to-end fixture, per the plan's
Acceptance section). The parity check runs the corpus once per mode, and
compares per-stage `deterministic_hash` values pairwise
(`cpu_reference` vs `hybrid_vector_gpu`, `cpu_reference` vs `resident_gpu`).
The first stage whose hash diverges between two modes is the defect site —
parity checking never aggregates past that point, so a divergence at
`Optimize` does not get masked by matching hashes at `Codegen`/`Link` from an
unrelated resync.

## Wave mapping

- **Phase 1 — Sidecar ports (Wave 1).** `sidecars.spl` shard types,
  `ports.spl` extended feature ports and the 7 `SidecarMapper`s,
  `offload_profile.spl` with every stage pinned to `cpu_reference`. No GPU
  dependency.
- **Phase 2 — AOP migration (Wave 2).** Consumes `aop.spl`:
  `PointcutQueryRef`/`AdviceTemplateRef` bind to compiled QueryIR/MutationIR
  programs; `WeavingReceipt` gates the no-weaving parity test.
- **Phase 3 — Optimizer migration (Wave 2).** Consumes `optimizer.spl`:
  `OptimizationPassContract` replaces line-pattern matching;
  `OptimizationRemark.hotness_milli` reads `MirProfileShard` through
  `MappingGraph`.
- **Phase 4 — Hybrid acceleration (Wave 4).** Consumes `offload_profile.spl`'s
  `HybridVectorGpu` arm and `optimizer.spl`'s `BackendPolicy.CostSelected`
  passes; `gpu_mmu` lane owns placement.
- **Phase 5 — Resident compilation (Wave 9).** Consumes `ResidentGpu` and
  `BackendPolicy.ResidentEligible`; sidecars, indexes, and IR stay resident in
  the Object VM, host receives only `receipt`/diagnostic ports.

## Explicit exports

`__init__.spl` under `src/compiler/00.common/structural_contracts/` explicitly
re-exports every public name declared above; it is not a wildcard hub. No
`rt_*` import, backend-field poke, or QueryIR/MutationIR opcode declaration is
permitted in these five files — this lane addresses those lanes only through
the opaque digest refs in `aop.spl`.
