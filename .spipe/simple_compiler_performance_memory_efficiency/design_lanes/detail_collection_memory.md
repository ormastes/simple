<!-- codex-design -->
# Collection, memory, and resource-analysis detail-design lane

## 1. Scope and invariants

This lane designs the collection-planning, typed performance-fact, ownership,
escape, cost-summary, memory-diagnostic, fusion, and pass-rehabilitation parts
of the selected full program. It does not redefine the canonical architecture
or requirements.

Non-negotiable invariants:

1. Unknown facts fail closed. `Unknown`, stale, cancelled, unsupported, or
   budget-exhausted analysis cannot prove purity, non-aliasing, uniqueness,
   bounded cost, non-escape, transform legality, or profitability.
2. Source diagnostics describe actionable source problems. A missed compiler
   transformation is an optimization remark. An optimizer-integrity defect is
   a compiler CI failure.
3. Typed HIR may identify values and candidate regions, but MIR/ownership facts
   are authoritative for aliasing, memory versions, last use, and movement.
4. Collection substitutions preserve equality, hashing, order, uniqueness,
   callback/effect ordering, exception/destruction timing, and allocation
   observability where the language exposes it.
5. No dormant transform becomes active by changing only a wrapper. Activation
   requires its contract, witnesses, verifier, differential tests, and target
   evidence.

Primary mappings: REQ-009--REQ-022 and REQ-025; supporting REQ-001--REQ-005,
REQ-007--REQ-008, REQ-023--REQ-024; NFR-001--NFR-005, NFR-007--NFR-012,
NFR-014--NFR-015.

## 2. Module ownership and dependency direction

The following are proposed pure-Simple modules unless marked existing.

```text
src/compiler/20.hir/perf/
  model.spl                 PerfEvent, HIR value/origin IDs, confidence
  fact_collector.spl        the one typed-HIR performance traversal
  fact_index.spl            immutable per-revision indexes
  operation_registry.spl    generated operation-summary reader
  collection_plan_extract.spl

src/compiler/35.semantics/lint/perf/
  diagnostic_model.spl      PerfRuleId/PerfDiagnostic production adapter
  collection_rules.spl      COLL/COPY/ALLOC candidates over HirPerfFacts
  memory_rules.spl          layout/copy/retention candidates
  suppression.spl           fixed-bound, cold, unknown, config policy

src/compiler/50.mir/perf/
  cow_ops.spl               proposed semantic COW MIR operations
  resource_markers.spl      allocation/copy/collection instrumentation IDs

src/compiler/55.borrow/perf/
  uniqueness.spl            bounded COW uniqueness dataflow
  escape.spl                conservative escape solver and proof reasons
  lifetime_proof.spl        last-use/destruction/suspension boundaries

src/compiler/60.mir_opt/perf_facts/
  service.spl               revision-bound PerfFacts owner
  memory_regions.spl        Region and alias relations
  memory_versions.spl       MemorySSA-lite definitions/uses/phis
  dependence.spl            access-pair direction/distance answers
  invalidation.spl          preservation/invalidation declarations

src/compiler/60.mir_opt/collection_plan/
  model.spl                 logical CollectionPlan
  properties.spl            cardinality/order/uniqueness/effect derivation
  physical_planner.spl      physical candidates and bounded costing
  fusion.spl                pipeline/reduction/general-loop fusion decisions
  lowering.spl              verified plan-to-MIR lowering
  remarks.spl               stable rejection/choice evidence

src/compiler/60.mir_opt/resource/
  cost_expr.spl             canonical bounded symbolic algebra
  operation_summary.spl     time/memory/effect/access contract
  function_summary.spl      CostSummary/PerfSummary
  summary_solver.spl        bounded call-SCC fixed point
  summary_cache.spl         fingerprints and caller invalidation

src/compiler/90.tools/perf/
  sperf_codec.spl           versioned deterministic summary records
  sperf_diff.spl            regression classification and CI policy
  curve_runner.spl          bounded multi-size empirical measurement
  sprof_v2_codec.spl        optional extended profile records
  profile_rank.spl          waste ranking only, never legality

config/compiler/collection_operations.sdn
  machine-owned collection/cost/effect contracts
```

Existing integration owners remain:

- `src/compiler/35.semantics/lint/collection_patterns.spl`: compatibility
  facade for COLL001--COLL008/COLL019 until individually migrated.
- `src/compiler/35.semantics/value_struct_layout.spl` and
  `src/compiler/35.semantics/layer_eq_real_layout.spl`: authoritative layout.
- `src/compiler/50.mir/mir_effects.spl` and
  `src/compiler/00.common/effects.spl`: effect vocabulary; perf code does not
  invent a second incompatible effect system.
- `src/compiler/55.borrow/gc_analysis/escape.spl`: legacy escape adapter. It
  must stop converting unresolved `Unknown` to `NoEscape`; consumers migrate
  to the new proof-bearing result before allocation placement.
- `src/compiler/60.mir_opt/mir_opt/collection_opt*.spl`: compatibility entry
  and initial pattern inventory, progressively delegated to CollectionPlan.
- `src/compiler/60.mir_opt/mir_opt/loop_detect.spl`: compatibility adapter to
  shared `PerfFacts.loops`; it may not rebuild a private graph.
- `src/compiler/95.interp/execution/sprof_hotspot_bridge.spl`: existing
  function-count consumer, extended through versioned optional records.

Dependency direction is HIR facts -> logical CollectionPlan -> MIR facts ->
physical plan/transform -> summaries/profile. Lint may consume HIR facts and
read-only summaries but may not invoke the MIR optimizer. Profile data may
rank candidates but may not turn an illegal rewrite into a legal one.

## 3. Typed HIR fact collector

### 3.1 Interface

```simple
struct HirPerfKey:
    module_revision: ModuleRevisionId
    target_layout: TargetLayoutId
    operation_model_version: text

struct HirPerfFacts:
    key: HirPerfKey
    events: [PerfEvent]
    loops: Dict<HirLoopId, HirLoopFact>
    values: Dict<HirValueId, HirValueFact>
    calls: Dict<HirCallId, ResolvedCallFact>
    operations: Dict<HirCallId, OperationInstance>
    layouts: Dict<TypeId, LayoutSummary>
    by_rule_seed: Dict<PerfSeedKind, [PerfEventId]>
    incomplete: [IncompleteReason]

fn collect_hir_perf_facts(
    module: TypedModuleView,
    layouts: LayoutQuery,
    operations: OperationRegistry,
    budget: HirPerfBudget
) -> AnalysisResult<HirPerfFacts>
```

`fact_collector.spl` is the only recursive traversal. It emits enter/leave-loop,
resolved call, collection operation, allocation, copy/move, parameter/return,
field access, capture, suspension, and type-layout events. Rule modules query
`by_rule_seed` and stable value/call/loop maps; they never recursively revisit
the HIR. Source spans come from HIR links, not textual search.

The traversal is O(HIR nodes + emitted events). Layout is memoized by
`(TypeId, TargetLayoutId)`. Operation lookup is O(1) by resolved semantic ID,
not method spelling. If an operation has no registry entry, it produces
`UnknownOperation(resolved_id)`; it never inherits a same-named builtin cost.

### 3.2 Invalidation and failure policy

- Any typed-module revision change invalidates the module fact set.
- Layout-only target change invalidates layouts and layout-derived rules.
- Registry model-version change invalidates operations, costs, and dependent
  diagnostics without forcing parsing again.
- Imported function-summary changes invalidate only rules that consume those
  imported summaries.
- Cancellation returns `AnalysisIncomplete(Cancelled)` with no partial result
  eligible for transformation or CI certification. Editor UI may retain an
  explicitly stale previous diagnostic display but must label it stale.

This realizes REQ-009/REQ-012 and NFR-003/NFR-006/NFR-008.

## 4. Operation and resource contracts

### 4.1 Core types

```simple
enum CostExpr:
    Zero
    Constant(value: i64)
    Size(symbol: SizeSymbol)
    Add(parts: [CostExprId])
    Multiply(parts: [CostExprId])
    Maximum(parts: [CostExprId])
    Log2(value: CostExprId)
    Expected(value: CostExprId)
    Amortized(value: CostExprId)
    Unknown(reason: UnknownCostReason)

struct OperationSummary:
    semantic_id: SemanticOperationId
    worst_time: CostExprId
    expected_time: CostExprId?
    allocation_count: CostExprId
    allocation_bytes: CostExprId
    peak_live_bytes: CostExprId?
    cardinality: CardinalityExpr
    effects: EffectSummary
    access: AccessProperty
    order: OrderProperty
    uniqueness: UniquenessProperty
    laziness: LazinessProperty
    enumerates_receiver: EnumerationCount
    enumerates_arguments: Dict<i64, EnumerationCount>
    invalidation: InvalidationContract
```

`CostExprArena` hash-conses structural nodes. `Add`/`Multiply` flatten nested
nodes, remove identities, fold checked constants, sort operands by stable ID,
and absorb any `Unknown`. Expected and amortized wrappers are never silently
compared as hard worst-case bounds. Caps are explicit: expression nodes,
depth, polynomial degree, independent size symbols, and coefficient width.
Exceeding any cap produces `Unknown(BudgetExceeded(kind, limit))`.

The SDN registry is validated at build time against semantic IDs and backend
symbol manifests. Duplicate IDs, missing required fields, invalid negative
costs, or references to absent runtime operations are build failures. Inferred
user functions use the same in-memory type, but never rewrite the shipped
registry.

### 4.2 `CostSummary` / `PerfSummary`

```simple
struct CostSummary:
    stable_function_id: StableFunctionId
    semantic_fingerprint: Fingerprint
    time_steps: CostExprId
    traversals: Dict<CollectionOrigin, CostExprId>
    allocation_count: CostExprId
    allocation_bytes: CostExprId
    copied_bytes: CostExprId
    stack_bytes: CostExprId
    peak_live_bytes: CostExprId?
    reads: RegionSet
    writes: RegionSet
    effects: EffectSummary
    enumerated_parameters: BitSet
    returned_aliases: AliasSummary
    escaping_parameters: BitSet
    confidence: SummaryConfidence
    assumptions: [SummaryAssumption]
    unknown_reasons: [IncompleteReason]
```

The solver builds the call graph once, condenses SCCs, and iterates each SCC in
stable function order. It stops at convergence or declared iteration/node/time
caps. Recursive growth outside the algebra widens to `Unknown(RecursiveGrowth)`.
Callers are re-solved only if the callee public summary fingerprint changes.
Fingerprint inputs are canonical typed-HIR/MIR identity, imported public
summary hashes, target layout, optimization config, and operation-model version.

Mappings: REQ-012, REQ-019; NFR-002, NFR-007, NFR-008, NFR-010.

## 5. CollectionPlan

### 5.1 Logical model

```simple
enum CollectionPlanKind:
    Source
    Map
    Filter
    CompactMap
    FlatMap
    Find
    Any
    All
    Fold
    Count
    Take
    Drop
    DistinctBy
    IndexBy
    GroupBy
    SemiJoinBy
    AntiJoinBy
    JoinBy
    LeftJoinBy
    CartesianProduct
    SortBy
    MergeBy
    CollectArray
    CollectSet
    CollectMap

struct CollectionPlan:
    id: CollectionPlanId
    kind: CollectionPlanKind
    inputs: [CollectionPlanId]
    operation: SemanticOperationId?
    callbacks: [HirCallableId]
    effects: EffectSummary
    cost: CostExprId
    cardinality: CardinalityExpr
    order: OrderProperty
    uniqueness: UniquenessProperty
    memory: MemoryExpr
    ownership: OwnershipProperty
    source_span: SourceSpan
```

Extraction runs after type and effect completion. Both explicit loops and
functional chains normalize to the same nodes only when resolved calls and
iteration semantics match a registry contract. Unknown callbacks remain opaque
plan barriers. Extraction is non-destructive; unsupported syntax falls through
to ordinary MIR with an optional analysis remark.

Property derivation is bottom-up and monotone. It may weaken from known to
unknown, never strengthen by heuristic. A physical candidate contains a list
of required proofs. `physical_planner.spl` evaluates candidates in stable order
under a bounded candidate count and chooses only a legal plan with a strictly
positive target-aware benefit. Index advice records construction time, bytes,
expected and worst lookup cost, equality/hash/order changes, and therefore is a
lint/fix suggestion unless all semantics are internal and proved equivalent.

### 5.2 Pipeline fusion

Initial automatic fusion is restricted to producer/consumer plans whose
callbacks are proven non-throwing and effect-compatible, ordering is preserved,
cardinality is bounded, and the intermediate is non-escaping. `Map -> Filter ->
Map -> CollectArray` lowers to one loop and one builder; exact output size uses
an exact-capacity constructor, an upper bound uses `reserve`, and unknown size
uses normal growth. Reserve failure behavior remains that of the existing
collection contract.

Intermediate elimination requires: one consuming plan, no external alias,
no identity observation, no destructor-order change, no suspension crossing,
and no callback access to the intermediate. Failure emits a stable missed
reason rather than materializing a speculative substitute.

Mappings: REQ-012, REQ-016; NFR-001/NFR-002/NFR-014.

## 6. COW uniqueness and escape

### 6.1 Explicit COW evidence

The following are proposed MIR semantic operations, lowered later to existing
runtime/backend primitives:

```simple
CowEnsureUnique(buffer, source_site)
CowClone(buffer, estimated_bytes, source_site)
CowMutate(buffer, operation, source_site)
```

Backends must not infer or erase these until optimizer/profile consumers have
run. If a backend cannot preserve their semantics, it lowers them conservatively
to current clone/check/mutate behavior.

```simple
enum UniquenessState:
    Unique(proof: UniquenessProofId)
    Shared(reason: ShareReason)
    Unknown(reason: UnknownUniquenessReason)
    Moved(destination: ValueId)
    Escaped(reason: EscapeReasonId)
```

The forward dataflow joins identical `Unique` proofs as unique; every conflicting
owner, phi, unknown call, capture, store to unknown/global, concurrency transfer,
or unresolved alias joins to `Shared` or `Unknown`. It tracks bounded alias sets
by MIR value/region, not source names. Transfer functions consume ownership
annotations in `mir_call_ownership.spl`. Clone elimination additionally needs
the source last-use proof, no observer between ensure and mutation, unchanged
destruction order, no suspension, safe unwind behavior, and compatible size and
alignment. Profile hotness never supplies these proofs.

COPY001 evidence includes clone site, loop multiplicity, estimated copied bytes,
and the first stable lost-uniqueness reason. Counters are inserted only in
profile builds and reference stable source/MIR site IDs.

### 6.2 Conservative escape

```simple
enum EscapeState:
    NoEscape(proof: EscapeProofId)
    ArgumentEscape(index: i64, reason: EscapeReasonId)
    ReturnEscape(reason: EscapeReasonId)
    FieldEscape(region: Region, reason: EscapeReasonId)
    GlobalEscape(reason: EscapeReasonId)
    ConcurrencyEscape(reason: EscapeReasonId)
    ForeignEscape(reason: EscapeReasonId)
    MayEscape(reason: EscapeReasonId)
```

There is no bottom `Unknown` that finalization demotes to `NoEscape`. New sites
begin `MayEscape(Unanalysed)`; `NoEscape` is produced only after a complete
function proof closes every flow from the site. The solver tracks direct and
aggregate return, field/global store/load, variants/options, closures, async or
generator suspension, task/thread/process/device transfer, copies/moves, and
unknown/FFI calls. Imported summaries may prove `noescape` only when their
fingerprints and ABI contracts validate.

Every result carries a predecessor chain so ESCAPE001 can render the shortest
stable path. Stack promotion/allocation elimination are separate consumers and
remain disabled until they also verify object size/alignment, frame budget,
lifetime endpoint, GC-root equivalence, unwind/destruction behavior, and target
stack constraints. A solver cap or inconsistent points-to field key yields
`MayEscape`, never `NoEscape`.

Invalidation: CFG/value/ownership/call-summary changes invalidate uniqueness and
escape; pure debug-span changes do not. Escape changes invalidate allocation,
stack-frame, retention, and CollectionPlan intermediate-elision decisions.

Mappings: REQ-014/REQ-015; NFR-001/NFR-002/NFR-005.

## 7. General loop fusion

CollectionPlan pipeline fusion and adjacent MIR loop fusion are separate passes.
General fusion consumes shared canonical loop facts and accepts only when all
answers below are `Proven`:

1. natural loops have real preheaders, normalized latches, dedicated exits, and
   explicit loop-exit uses;
2. control equivalence or adjacency has no intervening observable effect;
3. lower, upper, step, direction, signedness, no-wrap behavior, and trip count
   are equal or compatibly mapped;
4. all `L1.write/L2.read`, `L1.write/L2.write`, and `L1.read/L2.write` pairs have
   legal dependence direction/distance;
5. regions are disjoint or exact MemorySSA-lite/ownership facts prove ordering;
6. I/O, wait, unknown mutation, throws, panic, allocation/destruction timing,
   atomics, volatile/device access, locks, nondeterminism, callback effects,
   break/continue/return/yield, and reduction order are preserved;
7. target profitability is strictly positive.

```simple
struct FusionDecision:
    legality: ProofResult
    profitability: ProfitabilityResult
    required_facts: FactSet
    rejection_reasons: [StableRemarkReason]
    estimated_removed_traversals: CostExprId
    estimated_removed_bytes: CostExprId
    added_live_values: i64
    vectorization_delta: VectorizationEstimate
```

The target-independent benefit model counts removed control, shared loads,
removed intermediate bytes, and locality. Costs include duplicated computation,
code size, live ranges/spill risk, vectorization loss, prefetch change, and lost
parallel/GPU occupancy. Target data is injected through existing profitability
owners, not OS branches. Unknown profitability means no transform and an
analysis remark. Runtime alias versioning is a later Aggressive/PGO candidate,
not an initial fallback.

Mappings: REQ-017; NFR-001/NFR-002/NFR-004/NFR-014.

## 8. Rule catalog and placement

### 8.1 Always-on typed diagnostics

| Rule | Required facts | Action/failure policy |
|---|---|---|
| COLL009 nested dynamic iteration | nested loop symbols/cardinality | warn only when both dimensions can grow; suppress proven small fixed inner bound |
| COLL010 functional linear lookup | resolved linear operation inside callback/loop | suggest index/set with time-memory/order caveat; no generic rewrite |
| Multiple enumeration | lazy operation and enumeration count | suggest combine/materialize; warn about repeated effects when applicable |
| COLL011 repeated materialization | invariant origin/version and allocation | hoist/fuse only with MIR proof; otherwise warning |
| COLL012 sequential indexing | collection access capability | iterator/cursor fix only if borrow/lifetime semantics prove equivalent |
| COLL013 repeated sort/setup | mutation version and callback effects | warning; transform waits for MIR proof |
| Missing reserve | exact/upper pushes and capacity contract | machine fix only for builtin/internal collection with invisible capacity behavior |
| Duplicate lookup | receiver/key identity and no intervening mutation | use lookup/entry fix when return/ordering semantics match |
| COPY002--COPY004 | layout, uses, move/borrow eligibility | conservative fix applicability; public ABI change is advisory |
| LAYOUT001--LAYOUT003 | target layout and ABI exposure | advisory; private field reordering remains explicit source choice |
| ALLOC003/ALLOC004 | representation/lifetime facts | advisory or proven view fix |
| RETENTION001/003 | capture/suspension or monotone global/member growth | narrow-capture/bound advice; unknown lifetime suppresses fix |

Existing COLL001--COLL008/COLL019 behavior stays in its compatibility owner
until parity tests prove matching text, severity, ordering, suppression, fixes,
and exit status.

### 8.2 Remarks or deep/profile rules

- COPY001, COPY005, ALLOC001/002, ESCAPE001, MEM001/002 are MIR remarks unless
  a high-confidence source bug or critical policy promotes them.
- COLL014--COLL018, adjacent fusion, poor stride, offload batching, recursion
  resource bounds, peak live space, and data-structure advice use bounded deep
  summaries; uncertainty is shown, not warned as fact.
- CACHE001--CACHE003, RETENTION002, false sharing, and actual allocation/copy/COW
  waste are profile-primary. Layout/hardware advice remains advisory.
- Missed vectorization reports the precise blocker and never claims a speedup.

Stable diagnostic evidence contains rule ID, exact and related spans, tier,
confidence, symbolic expression, assumptions, suppression rationale, fix
applicability, and optional hotness. Stable sort key is module ID, primary span,
rule ID, related-span key.

Mappings: REQ-007--REQ-011; NFR-008/NFR-009.

## 9. `.sperf` and `.sprof-v2`

### 9.1 `.sperf`

The codec writes a versioned header, provenance, stable ordered function
records, and a checksum. Each record includes stable function ID, semantic
fingerprint, cost/allocation/copy/stack/peak expressions, confidence,
assumptions, unknown reasons, target, operation-model version, and imported
summary hashes. Reader rejection is explicit for unsupported version, corrupt
checksum, target/model mismatch, duplicate function ID, or invalid expression.

Diff classification compares normalized expression domains, not rendered text.
Confident polynomial-degree and critical peak-space regressions may fail CI;
coefficient/allocation regressions follow policy. Known -> unknown is never a
pass and is an error only for selected critical policy. Missing baseline is
`NoBaseline`, not improvement.

### 9.2 `.sprof-v2`

V2 preserves existing function/block/edge records and adds optional tagged
records for loop trip sketches, collection cardinality, allocation count/bytes/
capacity, copy bytes, COW clone bytes, escape destination, suspension retention,
hardware/cache sample, and optimizer candidate outcome. Unknown tags can be
skipped using record lengths; invalid lengths/checksums fail the file.

Hot paths update preallocated/saturating counters or bounded sketches only.
Disabled profiling performs no allocation and no I/O. Flush/merge owns I/O
outside request/loop hot paths. Site IDs are stable semantic IDs, and merge
rejects provenance/model mismatches unless explicitly requested as a diagnostic
operation. Ranking computes `execution_count * avoidable_work_or_bytes`, marks
sample uncertainty, and cannot provide semantic legality.

The curve runner accepts at least three distinct sizes and multiple repetitions,
records startup separately, fits a bounded model with confidence, and returns
`Inconclusive` for timeout-only, excessive noise, insufficient sizes, or invalid
fixture scaling. It never emits an asymptotic class from one timeout.

Mappings: REQ-020--REQ-022; NFR-008/NFR-010--NFR-012.

## 10. Staged pass rehabilitation

Every stage first changes registry truth; inactive transforms are absent from
the effective pipeline or marked AnalysisOnly/RemarkOnly. A stage may advance
only with positive witness, negative witness and reason, verifier, idempotence,
semantic differential execution, and applicable malformed CFG/overflow/FP/trap/
zero-trip/alias/unsafe-pointer/target evidence.

| Order | Pass | Required activation gate |
|---:|---|---|
| 0 | auto-vectorization containment | unsafe rewrite excluded; analysis remarks retained; exact `+1` induction, dependence, alias/effect, target gates before reactivation |
| 1 | constant folding | exact target width, overflow/checked-op, FP, trap and exceptional semantics |
| 2 | copy propagation | complete def-use, mutation/ownership invalidation, phi correctness |
| 3 | DCE | backward liveness, memory/effect/trap model, no quadratic later-use scans |
| 4 | local CSE | structural expression keys, dominance within scope, memory version and trap safety |
| 5 | LICM | real preheader, dominance, MemorySSA-lite, speculatability, zero-trip safety |
| 6 | reserve insertion | exact/upper trip bound and builtin capacity contract |
| 7 | bounds-check elimination | dominance-scoped range proof and collection mutation invalidation |
| 8 | stack promotion | complete proof-bearing escape, size/alignment/frame/lifetime/GC/unwind evidence |
| 9 | TCO | parallel argument assignment, ownership, exception/debug/destruction semantics |
| 10 | GVN | real dominator traversal, structural value numbers, memory versions |
| 11 | strength/string/general fusion/unrolling | individual signed/range, lifetime, dependence, profitability, and code-size gates |

CollectionPlan fusion may activate independently only for its narrower proven
pipeline subset; it does not certify general LICM or adjacent-loop fusion.
Three failed fix/verify cycles stop that slice and preserve its inactive status.

Mappings: REQ-001--REQ-005, REQ-017--REQ-018; NFR-001/NFR-002/NFR-015.

## 11. Invalidation matrix

| Change | Invalidated facts/products |
|---|---|
| typed HIR semantic revision | all HIR facts, plans, MIR facts and summaries for module |
| source span/debug-only revision | diagnostic rendering only; semantic facts reusable if fingerprint proves equality |
| target layout | layouts, copy/stack rules, profitability, summaries, `.sperf` comparability |
| operation registry version | operation instances, plans, costs, dependent diagnostics/summaries |
| CFG edge/block mutation | CFG-derived facts, dominance, loops, liveness, MemorySSA, escape, dependence |
| instruction/value mutation | def-use/liveness, memory versions, ownership, escape, cost; CFG retained only if declared preserved |
| memory/effecting instruction mutation | MemorySSA, alias/effect, escape, LICM/fusion/BCE legality |
| imported summary public hash | consuming caller summaries and dependent deep rules only |
| profile-only update | ranking/profitability estimates only; never legality or static summaries |

Each transform returns `PreservationReport`; undeclared preservation means
invalidate. Debug/test builds may recompute a preserved fact and compare its
fingerprint to catch dishonest declarations.

## 12. Failure and observability contract

All public analyses return `AnalysisResult<T>` with `Complete`, `Incomplete`,
or `InvalidInput`; no empty collection or default scalar stands for failure.
Stable reasons include missing registry contract, unknown external call, alias
unknown, effect unknown, irreducible loop, no preheader, unsupported recurrence,
budget kind, cancellation, stale revision, target unavailable, corrupt profile,
and verifier failure.

Counters/timers required per revision/function include fact cache hit/miss and
rebuild reason, HIR/MIR node/edge/event counts, analysis elapsed time, budget
exhaustion, plan candidates/legal/rejected/transformed, summary SCC iterations,
profile records/drops, and diagnostic suppression reason. These are emitted only
through structured developer telemetry/remarks and must not contaminate JSONL
stdout.

## 13. Requirement traceability

| Requirement | Design evidence in this lane |
|---|---|
| REQ-001--REQ-005 | pass containment/rehabilitation and verifier gates |
| REQ-007--REQ-011 | one HIR collector, rule placement, compatibility boundary |
| REQ-012 | operation/resource contracts and bounded `CostExpr` |
| REQ-013 | dependency on revision-bound shared MIR facts and invalidation matrix |
| REQ-014 | proof-bearing conservative escape lattice and consumers |
| REQ-015 | explicit COW evidence, uniqueness transfer and profile counters |
| REQ-016 | logical/physical CollectionPlan, property derivation and lowering |
| REQ-017 | complete fusion legality/profitability decision |
| REQ-018 | staged pass-by-pass activation table |
| REQ-019 | fingerprinted SCC summary algorithm and caller invalidation |
| REQ-020 | versioned `.sperf` and semantic diff policy |
| REQ-021 | optional bounded `.sprof-v2` and waste ranking |
| REQ-022 | bounded empirical curve runner and inconclusive policy |
| REQ-023--REQ-024 | linear collectors, cached graphs/summaries, pure-Simple owners |
| REQ-025 | stable module/API names and evidence hooks for system specs/docs |
| NFR-001--NFR-002 | proof gates and fail-closed result model |
| NFR-003--NFR-005 | one-pass facts, selective MIR/deep work, bounded caches |
| NFR-007--NFR-010 | one graph owner, deterministic bounded outputs, compatibility |
| NFR-011--NFR-012 | provenance and disabled-profile hot-path requirements |
| NFR-014--NFR-015 | target injection, no OS forks, bounded verification cycles |

## 14. Implementation handoff gates

Before implementation begins, the merge owner must resolve exact placement of
the generated operation registry within the existing build graph and confirm
that the shared MIR-fact lane exports the names used here (`PerfFacts`,
`Region`, `MemoryVersion`, `ProofResult`, `PreservationReport`). No transform
may create a private substitute.

The first implementation slice is containment and evidence: disable unsafe
vector rewriting, make escape finalization fail closed, add status/remarks,
then land the HIR fact collector and compatibility diagnostics. CollectionPlan,
COW elimination, stack promotion, and general fusion remain non-active until
their respective proof services and acceptance evidence exist.
