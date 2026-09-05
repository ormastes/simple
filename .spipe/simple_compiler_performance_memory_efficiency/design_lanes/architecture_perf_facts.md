<!-- codex-architecture -->
# Architecture Lane: Shared Frontend and `PerfFacts`

## Scope and decision

This lane designs the shared parsed/typed-program owner and the reusable intraprocedural MIR fact service required by REQ-006, REQ-009, REQ-013, REQ-014, REQ-017, REQ-019, REQ-023, and NFR-002 through NFR-008. It does not design diagnostics, pass status, CollectionPlan internals, or individual transforms except where they consume or invalidate facts.

The design uses two tree-private capsules with narrow facades:

1. `CompilationRevision` owns source, parsed AST, typed HIR, spans, target/config identities, and revision lifetime.
2. `PerfFacts` owns immutable, revision-bound MIR analyses and their dependency/invalidation graph.

Neither is a process-global semantic cache. A daemon may retain bounded revision owners, but all consumers must present the exact revision/fingerprint. Missing, stale, unsupported, cancelled, or budget-exhausted facts return explicit incomplete evidence; they never become a proof.

## Current-state map

| Concern | Current path | Architectural issue |
|---|---|---|
| Parse result caching | `src/compiler/10.frontend/frontend_parse_cache.spl`, called by `src/compiler/10.frontend/frontend.spl` | Disk cache stores a flat parse-pool blob, but there is no common in-process parsed+typed revision owner for compiler, lint, and LSP. |
| AST/HIR ownership | `src/compiler/10.frontend/**`, `src/compiler/20.hir/**` | Consumers can independently initiate work; revision identity and typed-artifact lifetime are not one contract. |
| MIR graph | `src/compiler/50.mir/mir_instruction_graph.spl` | Stable MIR data owner exists and should remain free of optimizer policy. |
| Loop discovery | `src/compiler/60.mir_opt/mir_opt/loop_detect.spl` | Rebuilds successor/predecessor reachability per candidate, treats block order as candidate discovery, and exposes insufficient canonical-loop facts. |
| Alias/escape approximations | `src/compiler/60.mir_opt/mir_opt/var_reassign_analysis.spl`, `src/compiler/55.borrow/gc_analysis/escape.spl` | Pass-local alias logic and a separate flow-insensitive escape analysis cannot serve as shared transformation proof. |
| Typed region evidence | `src/compiler/50.mir/verification_region_effects.spl` | Exact module-global verification evidence is valuable but deliberately incomplete for pointer/heap/external regions; it is an input adapter, not MemorySSA. |
| Vector/collection analyses | `src/compiler/60.mir_opt/mir_opt/auto_vectorize_analysis.spl`, `collection_opt*.spl`, `bounds_check_elim.spl`, `loop_licm.spl` | Independently derive overlapping loop, access, and range facts with inconsistent proof scopes. |

## To-be layer and module tree

```text
src/compiler/
  00.common/perf_contracts/
    revision_identity.spl       # stable value contracts only
    analysis_outcome.spl        # Available | Incomplete(reason)
    analysis_budget.spl         # bounded/cancellable policy values
    fact_identity.spl           # FactKind and fingerprints
    __init__.spl

  10.frontend/session/
    compilation_revision.spl    # sole module-revision owner
    source_snapshot.spl
    parse_artifact.spl
    revision_store.spl          # bounded in-process retention
    frontend_cache_adapter.spl  # existing .fpc bridge
    __init__.spl

  20.hir/session/
    typed_module_artifact.spl   # typed HIR + symbols + exact spans
    typed_revision_builder.spl  # 10 -> 20 transition
    __init__.spl

  50.mir/analysis_contracts/
    memory_region.spl           # frozen `MemoryRegion`
    memory_access.spl
    mir_revision.spl            # immutable function fingerprint
    effect_adapter.spl          # exact effect input, Unknown otherwise
    __init__.spl

  60.mir_opt/perf_facts/
    perf_facts.spl              # frozen `PerfFacts` facade
    manager.spl                 # dependency-aware cache owner
    dependency_graph.spl
    preservation.spl
    telemetry.spl
    cfg.spl
    dominance.spl
    loop_forest.spl             # frozen `LoopFact`
    def_use.spl
    liveness.spl
    induction.spl
    ranges.spl
    region_alias.spl
    memory_ssa_lite.spl
    escape_adapter.spl
    __init__.spl
```

`00.common` owns only cross-layer value contracts. It must not import AST, HIR, MIR, optimizer, lint, driver, or runtime owners. `10.frontend/session` may expose immutable parse artifacts to `20.hir/session`; it cannot import HIR. `20.hir/session` publishes a typed artifact to MIR lowering. `50.mir/analysis_contracts` owns MIR-shaped stable contracts. Analysis algorithms remain tree-private in `60.mir_opt/perf_facts`; sibling passes access only the `PerfFacts` facade.

No MDSOC feature transform is used on the hot query path. The feature is a virtual capsule at build composition, but runtime analysis is ordinary explicit composition so dependencies, cost, and invalidation remain visible and testable.

## Public interfaces

```text
struct RevisionIdentity:
    source_digest: text
    module_identity: text
    compiler_semantic_version: text
    target_identity: text
    config_identity: text
    imported_summary_digest: text

class CompilationRevision:
    fn identity() -> RevisionIdentity
    fn parse_artifact() -> AnalysisOutcome<ParseArtifact>
    fn typed_module() -> AnalysisOutcome<TypedModuleArtifact>
    fn source_map() -> AnalysisOutcome<SourceMapArtifact>

enum AnalysisOutcome<T>:
    Available(value: T, evidence: FactEvidence)
    Incomplete(reason: AnalysisIncompleteReason)

enum AnalysisIncompleteReason:
    MissingInput(text)
    Unsupported(text)
    StaleRevision(expected: text, actual: text)
    BudgetExceeded(fact: FactKind, limit: i64)
    Cancelled
    InvalidMir(text)
    UnknownEffect(text)

struct MirRevision:
    revision: RevisionIdentity
    function_symbol: i64
    semantic_fingerprint: text

class PerfFacts:
    fn cfg() -> AnalysisOutcome<CfgFacts>
    fn dominators() -> AnalysisOutcome<DominatorTree>
    fn post_dominators() -> AnalysisOutcome<DominatorTree>
    fn loops() -> AnalysisOutcome<LoopForest>
    fn def_use() -> AnalysisOutcome<DefUseFacts>
    fn liveness() -> AnalysisOutcome<LivenessFacts>
    fn inductions() -> AnalysisOutcome<InductionFacts>
    fn ranges() -> AnalysisOutcome<RangeFacts>
    fn regions() -> AnalysisOutcome<RegionAliasFacts>
    fn memory_ssa() -> AnalysisOutcome<MemorySsaLite>
    fn escape() -> AnalysisOutcome<EscapeFacts>

class PerfFactsManager:
    fn for_function(revision: MirRevision, func: MirFunction,
                    budget: AnalysisBudget) -> PerfFacts
    fn apply_change(change: MirChangeReceipt,
                    declaration: FactPreservation) -> AnalysisOutcome<PerfFacts>
    fn telemetry() -> [FactBuildRecord]
```

`PerfFacts` never yields a naked optional or boolean proof. A caller may transform only after matching `Available` and validating its evidence fingerprint. `Incomplete` is suitable for suppression/remarks, never legality.

## Fact dependency graph

```text
MirRevision
  -> CFG(successors, predecessors, reachable, RPO)
       -> Dominators
       -> PostDominators
       -> LoopForest
            -> InductionFacts
                 -> RangeFacts
  -> DefUseFacts
       -> LivenessFacts
       -> RegionAliasFacts
  -> exact EffectFacts + RegionAliasFacts + Dominators
       -> MemorySsaLite
  -> DefUseFacts + RegionAliasFacts + EffectFacts + imported escape summaries
       -> EscapeFacts
```

Construction is lazy, memoized, and single-owner for one `MirRevision`. Each successful result records source fingerprint, dependencies, node/edge counts, elapsed time, and budget consumption. Failed construction is memoized only for the same immutable revision and budget identity; cancellation is not retained.

## Core fact invariants

### CFG

- Every block ID is unique and resolves exactly once.
- Entry resolves and is the sole root used for reachability/RPO.
- Successor and predecessor tables are constructed in one linear edge pass.
- Terminator targets that do not resolve produce `InvalidMir`; they are not dropped.
- Unreachable blocks remain represented and explicitly marked, but cannot silently participate in dominance-backed proof.
- Worklists use a cursor/deque and indexed sets/bitsets; no `array[0:n-1]` popping or repeated linear membership.

### Dominance and post-dominance

- Dominance is computed from CFG edges, never block storage order.
- The entry dominates every reachable block; unreachable blocks have no ordinary dominator proof.
- Post-dominance has an explicit virtual exit for multiple returns/unwind exits.
- Every tree answers `dominates(a,b)` and provides immediate dominator plus preorder intervals for constant-time repeated queries.

### `LoopFact` and loop forest

```text
struct LoopFact:
    id: i64
    header: BlockId
    preheader: BlockId?
    latches: [BlockId]
    body: BlockBitSet
    exits: [CfgEdge]
    dedicated_exits: bool
    parent: i64?
    children: [i64]
    depth: i64
    reducible: bool
    trip_count: TripCountFact
```

- A natural loop backedge is `latch -> header` where header dominates latch.
- Body membership is reverse predecessor closure from latches to header, bounded by dominance.
- A preheader exists only when exactly one outside predecessor has a sole edge to header; normalization is a separate transform, never claimed by analysis.
- Multiple latches are retained, not guessed into one latch.
- Irreducible SCCs are explicit `reducible=false`; general transformations reject them.
- Exact trip count requires proven start, step, bound, comparison semantics, signedness, overflow/no-wrap, and zero-trip behavior. A bound constant alone is not an exact trip count.
- Loop nesting is deterministic by block/RPO identity, not discovery order.

### Def-use, liveness, induction and ranges

- One instruction numbering covers phi/parameter definitions, instructions, and terminator uses.
- Definitions and uses are collected once by MIR-kind visitors; no definitions-by-uses Cartesian scan.
- Ambiguous multiple definitions produce invalid/non-SSA evidence rather than selecting one.
- Liveness is block dataflow over indexed bitsets with deterministic worklist order.
- Range facts are program-point and dominance scoped. A fact from a loop condition cannot apply before it or outside its dominated region.
- Signedness, bit width, overflow/trap behavior, and inclusive/exclusive bounds are part of every range proof.
- Widening/budget exhaustion yields `Unknown`, not an optimistic interval.

### `MemoryRegion`, aliases, effects, and MemorySSA-lite

```text
enum MemoryRegion:
    Stack(local: LocalId)
    UniqueObject(allocation_site: i64)
    Argument(index: i64)
    Global(symbol: i64)
    Device(resource: text)
    Unknown(reason: text)
```

- Regions are semantic identities, never pointer-expression text keys.
- Proven unique/iso ownership may establish disjointness. Immutable sharing proves absence of writes, not distinct identity. Mutable borrow identifies an exclusive region only for its validated lifetime.
- Raw/unsafe pointer arithmetic, unresolved external/indirect calls, missing ownership facts, and unsupported projections collapse affected accesses to `Unknown`, not `NoAlias`.
- Existing `verification_region_effects.spl` contributes exact global effects only when its manifest is closed. Unsupported heap/pointer calls become `Unknown` effect inputs.
- MemorySSA-lite assigns a versioned definition or phi to each write-capable region at CFG joins. Loads link to a dominating memory def/phi or explicit live-on-entry. Unknown writes clobber `Unknown` and every region that may alias it.
- MemorySSA-lite is not a full dependence solver. It supports clobber queries and local legality; affine direction/distance is a later consumer layered on these facts.

### Escape adapter

- The existing `src/compiler/55.borrow/gc_analysis/escape.spl` cannot be treated as transformation proof while unresolved sites finalize to `NoEscape` or flows are incomplete.
- `escape_adapter.spl` initially maps only fully evidenced results into `EscapeFacts`; all other sites are `Unknown/MayEscape` with a proof-reason path.
- Stack promotion/allocation elimination require a future closed receipt proving return, aggregate, field/global, closure, suspension, concurrency, FFI/unknown-call, variant, copy/move, size, alignment, frame, and lifetime obligations.

## Preservation and invalidation

```text
enum FactKind:
    Cfg | Dominators | PostDominators | LoopForest | DefUse | Liveness |
    Inductions | Ranges | Regions | Effects | MemorySsa | Escape

struct FactPreservation:
    pass_name: text
    preserves: [FactKind]
    invalidates: [FactKind]

struct MirChangeReceipt:
    before_fingerprint: text
    after_fingerprint: text
    changed_blocks: [BlockId]
    cfg_changed: bool
    definitions_changed: bool
    memory_accesses_changed: bool
    effects_changed: bool
```

- A changed pass must return a receipt and declaration. Missing or contradictory declarations invalidate all facts.
- `cfg_changed` invalidates CFG and all transitive dependents.
- Definition/operand changes invalidate def-use, liveness, induction, ranges, regions, MemorySSA, and escape.
- Memory access/effect changes invalidate regions, MemorySSA, and escape; if control flow also changes, all CFG dependents are invalidated.
- Preserving a fact is checked in debug/test mode by recomputing it once and comparing canonical hashes. A mismatch fails the pass contract and marks that declaration dishonest.
- No in-place mutation of cached fact objects. A transformed MIR fingerprint selects a new `PerfFacts` generation.

## Shared frontend ownership and lifecycle

`CompilationRevision` is created by the driver/daemon from a normalized module identity, content digest, imported identities, target, and compiler configuration. `simple check`, formatter/source-map consumers, LSP, and compilation request artifacts from this owner. A CLI without a daemon may create one short-lived owner, but lint must not separately call `parse_module_silent_checked` after the compiler session already parsed the same revision.

The existing `.fpc` cache remains a serialization adapter beneath `CompilationRevision`; it is not authoritative revision identity. Corrupt/mismatched entries remain misses. Typed artifacts may be retained in-process first; durable typed caching is deferred until serialization includes all semantic/version identities.

`RevisionStore` is byte/node bounded and uses explicit last-access eviction. It holds no unbounded chain across edits. An edit creates a new immutable revision; prior requests may finish on the old owner, after which eviction is safe. Diagnostics and LSP results carry the revision identity, preventing stale publication.

## MDSOC visibility matrix

| Raw layer | Common node | Public to parent | Public to next-layer sibling |
|---|---|---|---|
| `10.frontend/session` | `00.common/perf_contracts/revision_identity.spl` | `CompilationRevision.identity()` | `ParseArtifact` facade to `20.hir/session` only |
| `20.hir/session` | revision + outcome contracts | `TypedModuleArtifact` internal owner | typed artifact facade to `50.mir` lowering; lint reads through a semantic facade, not HIR private nodes |
| `50.mir/analysis_contracts` | outcome/fact identity | `MirRevision`, `MemoryRegion`, access contracts | stable inputs to `60.mir_opt/perf_facts` |
| `60.mir_opt/perf_facts` | budget/outcome/fact identity | manager/facade internal to optimizer tree | `PerfFacts` query facade to sibling passes and structured-remark producer |
| `55.borrow/gc_analysis` | outcome/revision contracts | escape implementation tree-private | only an evidence adapter; no sibling imports its mutable internals |

Tree-private is the default. If lint needs fast HIR facts it receives a separate typed semantic facade owned by `35.semantics`; it does not import `20.hir/session` internals. If borrow and optimizer require a common MIR escape contract, that value contract belongs in `50.mir/analysis_contracts`, not either sibling's private subtree.

## Failure modes and required behavior

| Failure | Required behavior |
|---|---|
| Stale parse/HIR/MIR fingerprint | `Incomplete(StaleRevision)`; do not publish result or transform. |
| Malformed CFG target/duplicate block | `Incomplete(InvalidMir)` and verifier diagnostic. |
| Unsupported terminator/instruction | Explicit unsupported/unknown fact affecting dependent proofs. |
| Unknown call/effect/pointer alias | Clobber/alias `Unknown`; transform rejected with precise missed reason. |
| Analysis budget/time/cancellation | `AnalysisIncomplete`; default lint suppresses uncertain warning, remarks explain missing evidence. |
| Cache corruption/hash mismatch | Discard entry and rebuild once; never trust partial data. |
| Incorrect preservation declaration | Debug/test hash mismatch fails pass integrity; production conservatively invalidates. |
| Revision-store pressure | Deterministic bounded eviction; active revision handles stay valid. |
| Irreducible/no-preheader loop | Analysis remains available, legality query rejects transforms needing canonical form. |
| Escape proof incomplete | Allocation remains heap-managed; emit `ESCAPE001` remark only. |

## Migration stages

1. **Contracts and telemetry:** add common identities/outcomes/budgets, immutable `MirRevision`, manager telemetry, and no-op facade. Record existing per-pass rebuild sites.
2. **Shared frontend owner:** wrap current frontend and `.fpc` adapter in `CompilationRevision`; route compiler and lint first, then LSP/formatter; preserve old CLI outputs. Measure parse count, warm request scans/processes, time, and RSS.
3. **CFG foundation:** land linear CFG/RPO and dominance/post-dominance with adversarial fixtures. Change `loop_detect.spl` consumers to an adapter over shared `LoopForest`; do not activate transforms.
4. **Def-use and ranges:** centralize MIR-kind use/def enumeration, liveness, induction, and dominance-scoped ranges. Remove pass-local equivalents only after differential fact tests.
5. **Regions and memory versions:** introduce `MemoryRegion`, conservative alias/effect adapters, then MemorySSA-lite. Unknown calls/pointers fail closed. Migrate CSE/GVN/LICM/BCE/vector/collection legality one pass at a time while those transforms remain status-gated.
6. **Escape integration:** correct the escape lattice/flows, add proof reasons and size/lifetime receipts, then expose closed escape facts. No allocation-placement consumer is enabled before REQ-014 evidence passes.
7. **Invalidation enforcement:** require change receipts/preservation declarations, debug recomputation, canonical fact hashes, and CI self-checks. Delete superseded independent builders after repository-wide reference checks.
8. **Bounded interprocedural extension:** attach imported summary hashes and caller invalidation to the same revision model; keep SCC/cost solving out of always-on `PerfFacts` construction.

## Verification evidence

- One revision fixture proves compiler, lint, source mapping, and LSP observe identical source/typed identity and parse count `1`; warm requests prove no subprocess/full-tree scan (REQ-006, NFR-006).
- CFG fixture matrix covers multi-exit, unwind, unreachable, malformed, irreducible, nested, multiple-latch, zero-trip, and earlier-listed exit blocks (REQ-013, NFR-001/002).
- Instrumentation proves CFG/predecessors/RPO build at most once per function revision and records rebuild reasons (NFR-007).
- Differential adapters compare old and new facts during migration without authorizing transformations from disagreement.
- Preservation tests deliberately lie about CFG/def/memory changes and must fail integrity checks (REQ-013, NFR-001).
- Unknown external call/raw pointer/budget/cancellation fixtures prove fail-closed alias, effect, MemorySSA, range, and escape outcomes (REQ-014, NFR-002/010).
- Fixed corpus measurements cover Tier-0/Tier-1 wall time and RSS against the same admitted native pure-Simple binary (NFR-003/004/005/011).

## Requirement mapping

| Requirement | Architecture evidence |
|---|---|
| REQ-006 | `CompilationRevision`, revision store, `.fpc` adapter, single lifecycle owner |
| REQ-009 | typed artifact boundary and single indexed fact-collection ownership; MIR-only alias authority |
| REQ-013 | `PerfFacts`, dependency graph, fact invariants, preservation/invalidation |
| REQ-014 | conservative escape adapter and closed-proof gate |
| REQ-017 | canonical loops, dominance-scoped ranges, regions/effects, MemorySSA query inputs |
| REQ-019 | imported-summary digest in revision identity and bounded later extension |
| REQ-023 | linear CFG construction, indexed worklists, shared builders, telemetry |
| REQ-024 | all proposed owners are pure-Simple compiler layers; target data is an injected identity/input |
| NFR-002 | `AnalysisOutcome` and explicit unknown/incomplete semantics |
| NFR-003/004 | lazy tiered construction plus fixed-corpus gates |
| NFR-005 | bounded revision/fact caches and immutable generations |
| NFR-006/007 | one frontend owner and at-most-once CFG construction |
| NFR-008 | canonical identities, stable ordering, deterministic worklists/hashes |
| NFR-010/011 | budgets, cancellation, telemetry, and measurement provenance |
| NFR-014 | target-independent contracts; target identity/profitability injected |

## Collaboration handoff

- Sidecar lanes: this is the shared-analysis lane; optimizer, diagnostics, tests, and hot-path lanes consume these frozen names. No additional lower-model sidecar is needed for this bounded artifact (`N/A`).
- Merge owner: `/root`.
- Final normal/highest-capability reviewer: `/root`.
- Frozen names honored: `PerfFacts`, `LoopFact`, and `MemoryRegion`; shared helpers and manual step names remain those in `.spipe/simple_compiler_performance_memory_efficiency/state.md`.
