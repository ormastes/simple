
<!-- user-supplied research; source-level claims require the validation addendum below -->

# Simple Compiler & Linter Performance / Memory Bug Detection Research

**Target:** `ormastes/simple`

**Date:** 2026-08-22

## Scope and evidence

This is a static source audit of `ormastes/simple` at commit
`37bd406e219cc35cae049b4130f5167c21801864`. The compiler, tests, and
benchmarks were not executed for this research. Statements about source shape
are observed facts; performance or correctness consequences are derived risks
unless tied to an existing repository measurement. Commands, types, rules,
formats, and pipelines described as recommendations are proposed interfaces,
not claims that the current compiler exposes them.

## Executive conclusion

Simple should use four tiers of performance diagnostics:

| Tier | Runs in | Purpose |
|---|---|---|
| Fast typed checks | `simple check`, LSP, normal build | High-confidence collection/copy/allocation/layout lints |
| MIR optimization + remarks | Optimized builds | Safe transforms and explanations for missed transforms |
| Deep analysis | `simple perf --deep`, CI | Symbolic complexity, interprocedural resource bounds |
| Profile-guided diagnosis | Benchmarks/production | Rank issues by real hotness, cardinality, allocation and copy bytes |

Priorities: make optimizer activation truthful, share parser/HIR state
with lint, consolidate loop analysis, harden alias/effect/escape facts,
and implement the existing CollectionPlan architecture.

## 1. Repository findings

Simple already contains collection lints and a CollectionPlan proposal
covering nested dynamic iteration, functional linear lookup, repeated
materialization, sequential indexing, repeated sort, unbounded flat-map,
accidental Cartesian products, missing indexes, complexity regressions,
and unknown hot callbacks.

Current source/AST checks are too syntactic for many performance
decisions. Typed HIR should become the primary lint layer because it can
provide resolved receiver/callee identity, collection capabilities, types,
layout, and effect inputs. Authoritative alias and memory-version facts belong
to the shared MIR/ownership analysis rather than typed HIR alone.

Repository measurements also show lint is dominated by its parsing path
rather than the lint rules. Compiler, lint and LSP should therefore
share one parsed/typed representation instead of reparsing.

Several MIR facilities have implementations while representative public
adapters may still behave as identity functions. Every transform needs
an explicit status (`Active`, `AnalysisOnly`, `RemarkOnly`, `Skeleton`, or
`Disabled(reason)`) plus a separate expectation (`MayTransform`,
`MustTransformSentinel`, or `NeverTransforms`). Backend delegation is a
dispatch decision, not a substitute for implementation status. Each active
transform also needs a positive activation witness, a negative witness,
post-transform IR verification, statistics, and rejection reasons.

Narrow elementwise auto-vectorization is already active at the audited commit.
Its step matcher accepts constants beyond exact `+1` without proving operand
identity, so containing or repairing that rewrite is a Phase-0 correctness
gate, not merely a future missed-vectorization improvement.

Loop work should converge on one shared
CFG/dominator/natural-loop-forest implementation with preheaders,
normalized latches, dedicated exits, LCSSA-like boundaries, induction
facts, trip bounds and invalidation rules.

Escape analysis must be conservative: `Unknown`/`MayEscape` must never
authorize stack allocation. Handle returns, aggregates, fields, globals,
captures, suspension, concurrency transfer, FFI/unknown calls and
interprocedural summaries before using escape facts for memory-changing
transforms.

## 2. Diagnostic placement

| Finding | Transform | Default lint | Remark | Deep/profile |
|---|---|---|---|---|
| Exact local rewrite | Yes | Optional | Yes | No |
| Bad API/data structure | Usually no | Yes | Optional | Rank |
| Large copy/layout | Rarely | Yes | Yes | Validate |
| Alias/effect blocks optimization | No | No | Yes | Resolve |
| Complexity regression | No | Obvious only | No | CI |
| Loop fusion | If proven | Advisory | Yes | Profitability |
| Heap escape | If proven | No | Yes | Allocation profile |
| Retention/cache locality | Rarely | Advisory | Yes | Primary |

Recommended interfaces: `simple check`,
`simple build -O2 --remarks=perf`, `simple perf --deep`, and
`simple run --profile=perf,memory`.

## 3. Loop and algorithmic rules

| Rule | Detect | Placement/action |
|---|---|---|
| Adjacent traversal fusion | Adjacent loops over compatible domains | MIR transform after dependence/effect proof |
| COLL009 | Nested runtime collection iteration | Report symbolic `O(A*B)` |
| COLL010 | Linear lookup inside map/filter/fold callback | Suggest set/index |
| Multiple enumeration | Deferred sequence enumerated repeatedly | Materialize/combine |
| COLL011 | Repeated collect/clone/conversion | Hoist/reuse/fuse |
| COLL012 | Sequential structure repeatedly indexed | Iterator/cursor |
| COLL013 | Repeated sort without relevant mutation | Hoist/index |
| COLL014 | Unbounded flat-map cardinality | Deep cardinality bound |
| COLL015 | Accidental Cartesian product | Keyed join/index |
| COLL016 | Repeated scans by same key | Dict/HashSet/index |
| COLL017 | Complexity degree regression | CI failure when confident |
| COLL018 | Hot callback with unknown cost | Profile/remark |
| Invariant work | Pure unchanged expression in loop | LICM |
| Missing reserve | Known N pushes into empty collection | Suggest `reserve(N)` |
| Duplicate lookup | `contains(k)` then `get(k)` | Single lookup/entry API |
| Repeated normalization/hash/parse | Same pure expensive operation | Hoist/cache |
| Missed vectorization | Known blocker prevents vectorization | Explain blocker |
| Poor stride | Cache-hostile inner-loop access | Interchange/tile advice |
| Tiny repeated offload | Many small GPU/process launches | Batch/fuse |

## 4. Memory inefficiency rules

| Rule | Detect | Action |
|---|---|---|
| COPY001 | Hidden COW deep copy in loop | Warn + profile clone bytes |
| COPY002 | Redundant clone/copy | Machine fix only with last-use, ownership, alias, effect, and destruction-order proof; otherwise lint |
| COPY003 | Large read-only loop-variable copy | Borrow/view |
| COPY004 | Large read-only by-value parameter | Reference/view |
| COPY005 | Repeated large return/assignment copy | Remark/lint |
| LAYOUT001 | Large enum variant disparity | Advisory |
| LAYOUT002 | Large stack frame/object | Warning |
| LAYOUT003 | Excessive padding/stride | Advisory |
| ALLOC001 | Allocation in hot loop | Remark/critical lint |
| ALLOC002 | Pipeline temporary collections | Fuse |
| ALLOC003 | Box per small collection element | Representation advice |
| ALLOC004 | Allocating substring where view works | Fix only with lifetime/escape proof; otherwise lint |
| ESCAPE001 | Avoidable heap escape | Remark first |
| RETENTION001 | Large object live across await/yield | Narrow capture |
| RETENTION002 | Large retained capacity | Profile |
| RETENTION003 | Unbounded cache | Lint |
| MEM001 | Duplicate conversion buffer | Reuse/cache |
| MEM002 | Large overlapping temporaries | Sequence/reuse |
| CACHE001 | AoS/SoA mismatch | Profile/deep advice |
| CACHE002 | False sharing | Padding/partition advice |
| CACHE003 | Hot pointer chasing | Representation advice |
| STACK001 | Recursion depth x frame exceeds budget | Critical-mode error |

## 5. First-class COW analysis

Introduce the following proposed COW MIR operations; they do not describe
existing audited MIR vocabulary:

``` text
CowEnsureUnique(buffer)
CowClone(buffer, estimated_bytes)
CowMutate(buffer, operation)
```

Use a small uniqueness lattice:

``` text
Unique | Shared | Unknown | Moved | Escaped
```

Example diagnostic:

``` text
COPY001 hidden_cow_copy_in_loop
  loop bound: N
  copied value: self.items
  estimated copy bytes: N * size(self.items)
  reason: receiver and argument may share the same owner
```

Profile `cow_clone_count`, `cow_clone_bytes`, maximum cloned capacity,
source/MIR site and hotness.

## 6. Multiple-loop fusion

Fusion is not merely "two loops have the same bound." Prove compatible
domains:

``` text
lower1 == lower2
upper1 == upper2
step1 == step2
iteration_order compatible
```

Then prove dependence safety for `L1.write <-> L2.read`,
`L1.write <-> L2.write`, and `L1.read <-> L2.write`.

Because fusion changes global execution order, reject or prove safe
around I/O, unknown/shared mutation, exceptions, allocation/destruction
timing, atomics, volatile operations, locks,
break/continue/return/yield, nondeterminism and callback effects.

Profitability model:

``` text
benefit =
    eliminated traversal cost
  + eliminated temporary bytes
  + shared-load/locality gain
  - duplicated computation
  - code growth
  - register pressure
  - vectorization loss
  - parallelism/occupancy loss
```

Transform only when legality is proven. If profitability is uncertain,
emit a remark and use profile data.

## 7. Performance-analysis IR

Use a bounded symbolic algebra:

``` text
CostExpr =
    Zero
    Constant(i64)
    SizeOf(ValueId)
    Add([CostExpr])
    Multiply([CostExpr])
    Maximum([CostExpr])
    Log2(CostExpr)
    Unknown(Reason)
```

Function summary:

``` text
PerfSummary:
    time_steps
    collection_traversals
    allocation_count
    allocation_bytes
    copied_bytes
    stack_bytes
    peak_live_bytes
    reads
    writes
    effects
    enumerated_arguments
    returned_aliases
    escaping_arguments
    confidence
    unknown_reasons
```

Collection-operation metadata should record receiver kind, lazy/eager
behavior, ordering, allocation/copy behavior, enumeration count, result
cardinality, lookup/append cost, random access and reference stability.

Pipeline:

``` text
typed HIR
 -> collection/type-layout/effect facts
 -> CollectionPlan
 -> fusion + complexity + index candidates
 -> MIR
 -> CFG/dominators/loop forest/use-def/alias/trip/COW/escape
 -> transforms + structured remarks
 -> cached interprocedural summaries
 -> deep analysis + profile correlation
```

## 8. Keep compiler and lint light

Always-on analysis should be linear or near-linear and shared. Run
affine solvers, symbolic resource solving and polyhedral search only on
selected candidates or in deep mode.

Cache summaries using typed-HIR/MIR hash, imported-summary hashes,
target layout, optimization configuration and cost-model version.

Bound function size, SCC size, candidate count and solver time. Support
editor cancellation. Missing facts or timeout must return
`AnalysisIncomplete(reason)`, never silently become "safe," "pure,"
"non-escaping," or O(1).

## 9. Complexity regression

Persist `.sperf` summaries containing stable function ID, IR hash, time
bound, allocation-count/byte bound, copy-byte bound, stack bound,
confidence and assumptions.

Suggested CI policy:

| Change | Response |
|---|---|
| O(n) -> O(n^2) | Error |
| O(n log n) -> O(n^2) | Error |
| Same degree, much larger coefficient | Warning/budget failure |
| Known -> unknown | Warning; critical code may error |
| Allocation O(1) -> O(n) | Warning/error |
| Peak space O(n) -> O(n^2) | Deep/critical error |

For dynamic code, add empirical curves:

``` text
simple perf curve benchmark --size 100,200,400,800     --metric time,alloc_bytes,cow_clone_bytes
```

Fit `metric ~= c * n^k` after subtracting fixed startup cost. Never
classify complexity from a single timeout.

## 10. `.sprof-v2`

Extend existing profile infrastructure with optional records for:

-   loop iterations/trip histograms;
-   collection cardinality;
-   allocation count/bytes/capacity;
-   copy count/bytes;
-   COW clone count/bytes;
-   escape destinations;
-   bytes retained across suspension;
-   optional cache/hardware samples;
-   optimization candidate/outcome.

Rank diagnostics by approximately:

``` text
estimated_waste = execution_count * avoidable_cost_per_execution
```

## 11. Prior art

| System | Lesson for Simple |
|---|---|
| LLVM loop infrastructure | Canonical loop form and scalar-evolution facts before aggressive transforms |
| LLVM/MLIR optimization remarks | Separate user lints from passed/missed/analysis/failure optimization records |
| MLIR affine fusion | Separate legality from profitability; fuse producer-consumer and sibling loops carefully |
| Rust Clippy | Conservative local copy/layout lints with confidence and applicability |
| clang-tidy | Narrow high-confidence rules such as reserve and expensive copies |
| .NET CA1851 | Multiple enumeration requires laziness/enumeration metadata |
| Infer Cost | Symbolic resource bounds and differential complexity CI |
| SPEED | Interprocedural symbolic execution-count bounds |
| RaML/AARA | Deep amortized resource analysis for selected critical functions |
| ThinLTO | Compact cached summaries for scalable interprocedural work |
| Futhark | Preserve high-level array structure and explicit memory representation |
| Cozy | Offline data-structure/index advice from query patterns |
| Alive2 | Translation validation for optimizer rewrites |
| Optimuzz | Generate tests specifically to activate optimizations and find miscompiles |

## 12. Implementation sequence

### Phase 0 --- truthful optimizer + shared frontend

-   disable or repair the active unsafe vector step matcher and prove exact
    induction/step legality;
-   pass status and activation witnesses;
-   pass statistics/rejection reasons;
-   `--verify-each`;
-   shared parser/HIR cache for compiler/lint/LSP;
-   reliable source spans.

### Phase 1 --- cheap typed lints

Implement typed versions of existing collection lints plus:

The migration must preserve the current `COLL001`-`COLL008`/`COLL019`
severity, exit-status, suppression, fix, and diagnostic behavior until each
rule is separately baselined and deliberately migrated.

-   hidden COW copy;
-   multiple enumeration;
-   missing reserve;
-   expensive loop-variable copy;
-   large by-value parameter;
-   redundant clone;
-   duplicate map lookup;
-   repeated sort/materialization;
-   allocating substring;
-   large stack frame;
-   padding/layout diagnostics.

### Phase 2 --- sound MIR facts

-   dominators + canonical loop forest;
-   def-use/liveness;
-   memory versions + region alias;
-   explicit unknown effects;
-   COW uniqueness;
-   conservative escape;
-   scalar evolution/trip bounds.

### Phase 3 --- CollectionPlan execution

Activate collection-plan extraction, local cost summaries, pipeline
fusion, index candidates and MIR lowering. Initially transform only
pure, proven-safe cases.

### Phase 4 --- interprocedural complexity

-   compact summaries;
-   SCC propagation;
-   COLL009-COLL018;
-   `.sperf`;
-   complexity/allocation regression CI;
-   performance-critical/no-allocation policies.

### Phase 5 --- deep/profile-guided optimization

-   affine dependence;
-   selected AARA-style resource analysis;
-   profile-ranked data-structure advice;
-   `.sprof-v2`;
-   empirical complexity curves;
-   profile-guided fusion/layout advice;
-   hardware-sampling correlation.

## 13. Recommended first-release priorities

| Priority | Feature |
|---:|---|
| 1 | Contain unsafe active vectorization and enforce optimizer pass activation conformance |
| 2 | COPY001 hidden COW copy in loop |
| 3 | Multiple deferred enumeration |
| 4 | Nested linear lookup / accidental O(n²) |
| 5 | Repeated sort/materialization |
| 6 | Missing reserve |
| 7 | Expensive loop-variable copy |
| 8 | Large by-value parameter / stack object |
| 9 | Duplicate associative lookup |
| 10 | Improved loop-invariant work |
| 11 | Allocation/COW optimization remarks |
| 12 | Complexity-regression CI |

## Final architecture

``` text
Shared parsed + typed program
        |
        +-- Fast typed PerfFacts
        |      +-- high-confidence lints
        |
        +-- CollectionPlan + MIR facts
               +-- safe transforms
               +-- structured optimization remarks
               |
               +-- cached interprocedural CostSummary
                       +-- deep/CI bounds
                       +-- .sprof runtime evidence
```

This design maximizes coverage while keeping normal compilation light:
obvious bugs are caught immediately, safe opportunities are optimized,
uncertain cases are explained rather than guessed, expensive analyses
are selective, and runtime evidence resolves cases static analysis
cannot.

---

## Validation relationship

This cleaned research is interpreted together with [the companion performance and memory-efficiency audit](simple_compiler_performance_memory_efficiency_audit.md) and its Codex validation addendum. At commit `37bd406e219cc35cae049b4130f5167c21801864`, the source audit confirms the overall architecture and priorities, with two material refinements: narrow elementwise auto-vectorization is already active and has an unsafe step-matching exposure; escape field keys are structurally consistent inside the analysis API but receive inconsistent store/load inputs at the production integration boundary.
