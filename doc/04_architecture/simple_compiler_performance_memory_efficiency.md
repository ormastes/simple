<!-- codex-architecture -->
# Simple Compiler Performance and Memory Efficiency Architecture

## Status

Accepted design for selected Feature Option C / NFR Option 1. Implementation remains staged and incomplete until executable evidence passes.

## Context

At commit `37bd406e219cc35cae049b4130f5167c21801864`, canonical optimizer pipelines include identity/empty adapters, narrow active vector rewriting has an unsafe induction-step matcher, lint reparses through a measured dominant parser path, loop/def-use/range/alias analyses are duplicated, and escape facts are not safe allocation-placement evidence. The architecture must fix these owners without creating a second linter, optimizer, profile system, grammar, or platform-specific application path.

## Decision

Use one revisioned compiler session and two explicit analysis capsules:

```text
CompilationRevision (source -> AST -> typed HIR -> exact spans)
        |
        +-- 35.semantics/perf: one typed fact collector + source diagnostics
        |
        +-- MIR lowering
              |
              +-- 60.mir_opt/perf_facts: CFG/dominance/loops/def-use/
              |                         ranges/regions/memory/escape
              |
              +-- CollectionPlan lowering + proven transforms
              +-- structured optimizer remarks
              +-- bounded interprocedural PerfSummary/.sperf
                         |
                         +-- optional .sprof-v2 correlation
```

This is a virtual capsule at build composition, not an MDSOC feature transform on the hot query path. Dependencies and invalidation remain explicit ordinary composition.

## Layer ownership

| Layer | Owner | New/extended responsibilities |
|---|---|---|
| `00.common/perf_contracts` | Stable cross-layer value contracts | Revision/fact identities, `AnalysisOutcome`, budgets; no AST/HIR/MIR imports |
| `10.frontend/session` | Parsed source revision | Immutable source/parse artifacts and bounded revision store over existing frontend cache |
| `20.hir/session` | Typed revision | Typed module, symbols, exact spans, semantic fingerprint |
| `35.semantics/perf` | Typed diagnostics and CollectionPlan extraction | One HIR visitor, `PerfRuleId`, `PerfDiagnostic`, operation registry, compatibility adapters |
| `50.mir/analysis_contracts` | MIR-shaped stable values | `MirRevision`, `MemoryRegion`, access/effect contracts |
| `55.borrow` | Ownership/escape/COW proofs | Conservative proof production; no optimizer-policy ownership |
| `60.mir_opt/perf_facts` | Intraprocedural MIR analysis | Cached fact manager, analysis algorithms, invalidation receipts |
| `60.mir_opt/perf_summary` | Bounded interprocedural analysis | `PerfSummary`, SCC propagation, `.sperf` semantic owners |
| `60.mir_opt` pass registry | Optimization planning/execution | Truthful status, expectation, delegation, effective pipeline, run records |
| `80.driver` | Compiler session/CLI orchestration | Reuse artifacts, route diagnostic/remark/deep modes, no semantic duplication |
| `90.tools/perf` | Tool projections | `.sperf`/curve/report commands over compiler owners, not a separate analyzer |

The first shared-analysis implementation uses declared-local bucket indexes for def/use
sites. A fact build is a single MIR traversal; growing per-local arrays are owned by a
dense outer array so recording a use does not repeatedly copy a dictionary-held array.
Coverage is explicit: an unknown instruction or undeclared local reference makes
`def_use_complete=false`. No consumer may interpret partial coverage as absence of uses.

Pass preservation is fail-closed. Until proved otherwise, a changed active pass
invalidates CFG, dominators, and def/use. Analysis-only, remark-only, skeleton, and
disabled routes preserve all facts because they cannot replace MIR.

`40.mono` remains monomorphization; no `40.collection_plan` sibling is introduced. No undocumented `65` layer is introduced. CollectionPlan extraction belongs in `35.semantics/perf/collection_plan`, while MIR planning/lowering and interprocedural MIR summaries remain under `60.mir_opt`.

## Frozen contracts

### Revision and outcomes

```text
enum AnalysisOutcome<T>:
    Available(value: T, evidence: FactEvidence)
    Incomplete(reason: AnalysisIncomplete)

struct RevisionIdentity:
    source_digest
    module_identity
    compiler_semantic_version
    target_identity
    config_identity
    imported_summary_digest
```

Every artifact, diagnostic, fact, summary, cache entry, and profile correlation carries the relevant revision/fingerprint. Missing, stale, unsupported, cancelled, invalid, or budget-exhausted evidence never becomes a proof.

### Optimizer integrity

```text
PassStatus = Active | AnalysisOnly | RemarkOnly | Skeleton | Disabled(reason)
PassExpectation = MayTransform | MustTransformSentinel | NeverTransforms
BackendDelegation = NotDelegated | Delegated(backend, reason) | Rejected(reason)

PassRunRecord:
    requested/effective identity, status, expectation, delegation
    functions, candidates, transformed, rejected
    before/after instruction counts, elapsed, stable rejection reasons
    verifier receipt, fact preservation/invalidation receipt
```

Only `Active` entries dispatch transforms. `AnalysisOnly` and `RemarkOnly` may inspect but never replace MIR. `Skeleton`/`Disabled` never dispatch. Unknown pass names, invalid status combinations, and missing required facts fail pipeline planning. Requested and effective pipelines are separate immutable evidence.

### Diagnostic model

```text
PerfRuleId                 # stable COLL/COPY/LAYOUT/ALLOC/ESCAPE/... identity
PerfDiagnosticKind = SourceDiagnostic | RemarkPassed | RemarkMissed |
                     RemarkAnalysis | RemarkFailure | CompilerIntegrity
PerfDiagnostic             # exact spans, policy, tier, confidence, cost,
                           # hotness, fixes, suppression, incomplete/rejection
OperationSummary           # time/resources/cardinality/effects/access/order/
                           # uniqueness/laziness/enumeration/invalidation
CostExpr                   # bounded canonical symbolic algebra + Unknown(reason)
```

Warnings/errors describe likely actionable source defects. Passed/missed/analysis/failure records are opt-in optimizer remarks and do not affect ordinary lint exit status. Compiler-integrity findings fail compiler CI and cannot be suppressed by source attributes.

### `PerfFacts`

`PerfFactsManager` is keyed by immutable `MirRevision` and lazily constructs:

```text
CFG -> dominators/post-dominators -> LoopForest -> induction -> ranges
MIR -> def-use -> liveness -> region aliases
effects + aliases + dominance -> MemorySSA-lite
def-use + aliases + effects + imported summaries -> escape facts
```

Core invariants:

- CFG successors/predecessors/RPO are built in one edge pass per revision.
- Dominance derives from CFG, never block storage order.
- A natural backedge requires `header dominates latch`; irreducible SCCs are explicit.
- Exact trip count proves start, step, comparison, signedness, no-wrap, reachability, and zero-trip behavior.
- Range facts are program-point/dominance scoped.
- Raw/unsafe/unresolved pointers and calls collapse affected regions/effects to `Unknown`.
- Unknown writes clobber every possibly aliased region.
- Escape `NoEscape` requires a closed proof path plus size/alignment/frame/lifetime evidence.

### Invalidation

Every changed pass returns `MirChangeReceipt` plus `FactPreservation`. Missing or contradictory declarations invalidate all facts. CFG changes invalidate CFG and all dependents; def/operand changes invalidate def-use/liveness/induction/range/region/memory/escape; memory/effect changes invalidate region/memory/escape. Debug/test builds recompute declared-preserved facts once and compare canonical hashes. Cached facts are immutable and cannot be queried after revision change.

## Collection and memory architecture

The one-pass typed collector emits indexed loop/call/collection/allocation/copy/read/write/suspend events. Standard-library `OperationSummary` metadata is generated/versioned with the library; user summaries are inferred and fingerprinted; unknown operations remain top/unknown.

CollectionPlan preserves source-level ordering, cardinality, callbacks, ownership, and materialization decisions:

```text
typed HIR -> extract logical plan -> cost/cardinality/effect analysis
          -> proven fusion/index/materialization plan -> MIR lowering
```

Automatic planning requires equality/order/effect/alias/cardinality proof. Otherwise the plan remains unchanged and emits a precise diagnostic or missed remark. General MIR fusion additionally requires compatible canonical loops, dependence direction/distance, effect/exception/destruction order, early-exit equivalence, numeric-order preservation, and positive target-aware profitability.

COW instructions (`CowEnsureUnique`, `CowClone`, `CowMutate`) are proposed explicit MIR vocabulary. The uniqueness lattice is `Unique | Shared | Unknown | Moved | Escaped`. Clone elimination requires ownership, last-use, alias, effect, destruction-order, lifetime, and profitability proof.

## Interprocedural and profile architecture

`PerfSummary` records time, traversals, allocation count/bytes, copied bytes, stack and optional peak-live bytes, regions/effects, enumeration, returned aliases, escape, confidence, assumptions, and unknown reasons. Bounded SCC fixed points invalidate callers only when imported semantic hashes change.

`.sperf` is deterministic static-summary evidence used by differential CI. `.sprof-v2` extends existing function/block/edge profiling with optional loop/cardinality/allocation/copy/COW/escape/suspension/cache/remark-outcome records. Disabled profiling performs no hot-path allocation or I/O. Profiles rank candidates; they never prove transform legality.

## CLI and tool flow

| Surface | Contract |
|---|---|
| `simple check` | High-confidence typed source diagnostics; remarks off |
| `simple lint` | Compatibility renderer over shared revision; no second parse |
| `simple build -O2 --remarks=perf` | Opt-in passed/missed/analysis/failure records |
| `--print-effective-pipeline` / `--emit-opt-report` | Requested/effective/status/delegation/run evidence |
| `--verify-each` | Stop on the first changed-pass verifier failure |
| `simple perf --deep` | Bounded interprocedural/static analysis with explicit incomplete results |
| `simple perf curve` | Multi-size repeated empirical measurement with provenance |
| `simple run --profile=perf,memory` | Optional `.sprof-v2` evidence |

LSP publishes source diagnostics by default and remarks through a separate requested capability. MCP/LSP startup and warm requests reuse bounded indexes/revisions; no request performs a recursive tree scan or launches a compiler subprocess.

## Migration and safety gates

1. Contain unsafe active vector rewriting; land common contracts and truthful pass descriptors.
2. Add effective-pipeline/run evidence, compiler self-lints, sentinels, and verifier receipts.
3. Introduce revisioned frontend ownership and exact spans; migrate lint and LSP without compatibility changes.
4. Land CFG/dominance/loop/def-use/range facts and adapters while transforms remain status-gated.
5. Land region/memory/escape/COW facts and proof reasons.
6. Implement first-release typed rules through one collector.
7. Execute CollectionPlan only for proven cases.
8. Rehabilitate scalar/loop transforms one at a time.
9. Add bounded summaries, `.sperf`, `.sprof-v2`, curves, and profile ranking.
10. Remove superseded builders only after reference/differential evidence.

## Failure behavior

Malformed MIR, unknown effects/aliases, stale artifacts, unavailable facts, solver limits, cancellation, cache corruption, verifier failure, and schema mismatch are explicit typed failures. Transforms preserve the original MIR on failure and stop the affected pipeline. Diagnostic render failure emits one minimal valid machine record and details on stderr; JSONL never contains logs or partial JSON.

## Consequences

Positive: one source of compiler truth, bounded reuse, safer transformations, actionable diagnostics, and measurable hot paths. Negative: large multi-release migration, compatibility adapters, memory for bounded caches, and many passes remain disabled until individually proven. Neutral: downstream LLVM optimization remains separate backend delegation evidence and does not make a Simple MIR identity adapter active.

## References

- `doc/01_research/local/simple_compiler_performance_memory_efficiency_audit.md`
- `doc/01_research/local/simple_compiler_linter_performance_memory_bug_detection.md`
- `doc/02_requirements/feature/simple_compiler_performance_memory_efficiency.md`
- `doc/02_requirements/nfr/simple_compiler_performance_memory_efficiency.md`
- `doc/04_architecture/compiler/perf/simple_optimization_plugin.md`
- `doc/01_research/compiler/collection_planner/collection_plan_ir_2026-07-31.md`
