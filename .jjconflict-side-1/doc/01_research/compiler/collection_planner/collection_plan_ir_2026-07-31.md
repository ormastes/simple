# Complexity-aware collection planning for Simple

**Date:** 2026-07-31
**Status:** research — readiness re-verified against the live tree, design accepted, execution gated on P0
**Supersedes as the collection-perf entry point:** `doc/01_research/compiler/performance/performance_optimization_plan.md` (still valid for non-collection passes)

## 0. Thesis

Simple should build a **complexity-aware collection planner**, not ban nested
loops and not mechanically rewrite loops into `map`/`filter`.

```
explicit loops ───────┐
                      ├─> CollectionPlan IR ──┬─ complexity analysis
map/filter pipelines ─┘                       ├─ stream/loop fusion
                                              ├─ index and join selection
                                              ├─ profile-guided plan selection
                                              └─ verified MIR lowering
```

The distinction that matters: **`map`/`filter` make intent analysable; hash
sets, hash maps, indexing, sorting and join planning are what actually turn
O(n²) into O(n) or O(n log n).** A functional rewrite alone changes nothing
asymptotically — Clippy makes the same point about its own `manual_find` family.

## 1. Readiness — verified, not assumed

Every row below was checked against the working tree on 2026-07-31. Four rows
**correct** the prior informal assessment; those are called out explicitly
because two of them change the plan.

| Area | Status | Verified finding |
|---|---|---|
| Typed MIR + pass registry | Green | Typed SSA MIR, explicit pass identities, optimisation levels, provider contracts, backend policies. |
| Seed lint infrastructure | Green | `src/compiler_rust/compiler/src/lint/` — Allow/Warn/Deny, JSON diagnostics, `EasyFix` with confidence levels, 8 registered checkers. |
| MIR collection optimiser | Amber | `60.mir_opt/mir_opt/collection_opt{,_core,_patterns}.spl`, **1,533 lines**. Recognises collection accesses, loop-invariant calls, concatenation, linear scans. No symbolic cost model, no index synthesis. |
| **Source complexity lint** | **Green — CORRECTION** | **Not text/indentation scanning.** `35.semantics/lint/collection_patterns.spl` (**712 lines**) is a typed-AST walker over `decl_get_body`/`stmt_get_tag`/`expr_get_tag` with **eight live rules already shipping**: see §2. The proposed `PERF001/002/003/011` are **duplicates of COLL001–004/006/007**. |
| Functional collection API | Amber | `map`, `filter`, `flat_map`, `compact_map`, `reduce`, `group_by` documented as canonical. |
| **Functional runtime parity** | **Red — SHARPER THAN REPORTED** | `rt_array_map` is not merely absent. It is **declared and called by two backends with no definition anywhere**: `70.backend/backend/llvm_lib_translate.spl:416` declares it, `compiler_rust/…/codegen/llvm/functions.rs:2790` maps `Array::map` onto it. Both emit a call to a symbol that does not exist. Closures are demoted JIT→interpreter on ABI defects; predicate `any`/`all` diverge by backend. |
| **Pure `unique` / `group_by`** | **Red — CONFIRMED VERBATIM** | `gc_async_mut/pure/collections.spl:55` (`unique`) and `:73` (`group_by`) both use a growing result array with an inner linear scan. Genuinely O(n²). |
| **Pure HashMap / HashSet** | **Red — WORSE THAN REPORTED** | `nogc_sync_mut/src/collections/hashmap.spl:86` is `fn get(key: text) -> text?` — text-keyed **and text-valued**. `hashset.spl:112` is `fn contains(value: text) -> bool`. These cannot back a generic `IndexedBy<K,V>` at all; this is not a specialisation, it is a monomorphic text dictionary. |
| Built-in `Dict` native correctness | Red | `.set(k,v)` silently drops inserts under native codegen (`d[k] = v` works in both engines). The planner must never synthesise the `.set` path. |
| Effect analysis | Amber/Red | Rich HIR effect enum (`Pure`, `IO`, `Async`, `Throws`, `Mutates`, `Allocates`) exists, but the repo's own audit says the facts are duplicated across partial systems and not populated or propagated through one pipeline. |
| PGO infrastructure | Green foundation | `.sprof` has stable function/block/edge counters, merge, saturation, hot-path policy (`app/optimize/sprof_loader.spl`, `95.interp/execution/sprof_hotspot_bridge.spl`). Extensible with collection records. |

Independent evidence that hidden operation cost is a real Simple problem, not a
theoretical one: `char_code_at(i)` walks UTF-8 from byte 0 in all three engines,
so every character-index scan is O(n²). Fixing those sites produced a material
speedup; the next profile then surfaced repeated declaration lookups and wide
record reconstruction as the new dominant cost.

### 1.1 What the two corrections change

1. **The lint layer is further along than assumed.** Do not open a `PERF001…`
   namespace. Extend `collection_patterns.spl` with the genuinely new rules
   (join/cartesian/index-candidate/regression) and keep the `COLL` prefix.
   A parallel `checker_performance.rs` in the seed would be a **third**
   implementation of the same knowledge — exactly the duplication §4 exists to
   stop. The seed lint should consume the registry, not re-derive it.
2. **The index substrate does not exist.** A generic `HashMap<K,V>` is not a
   Priority-3 nicety; it is a hard prerequisite for every rewrite in §8. Nothing
   in §8 can land before it.

## 2. Rules that already ship

`35.semantics/lint/collection_patterns.spl`:

| Code | Pattern | Severity |
|---|---|---|
| COLL001 | `arr = arr + [x]` in loop — "array concat in loop (O(n^2))" | CRITICAL |
| COLL002 | `.contains()` on array in loop — "(O(n) per iteration)" | HIGH |
| COLL003 | `.remove(0)` queue drain in loop — "(O(n) shift per iteration)" | HIGH |
| COLL004 | loop-invariant method call | MEDIUM |
| COLL005 | chained `.filter().filter()` (expression-level, not loop-dependent) | MEDIUM |
| COLL006 | `str = str + x` in loop — "string concat in loop (O(n^2))" | CRITICAL |
| COLL007 | `arr = arr[0:len-1]` array rebuild to pop | HIGH |
| COLL008 | unbounded module-global `.push()` with no reset | MEDIUM |
| COLL019 | `d[k].push(x)` / `a[i].field.push(x)` — mutation through indexed access silently lost (ADR-004 value semantics; a correctness rule, not a cost rule; 009–018 stay reserved for §7) | HIGH |

Gaps these leave: no symbolic cost algebra (severity is a hardcoded label, not a
derived bound), no interprocedural summaries, no alias awareness, no
cardinality/order/uniqueness facts, no join or cartesian-product recognition, no
index-candidate analysis, no regression detection, and **no coverage of the
functional forms** — `xs.filter { |x| ys.contains(x) }` is invisible to COLL002
because it is not a `for` statement. That last gap is the important one: today,
functional syntax is a way to hide an O(n²) operation from the linter.

## 3. Do not literally replace loops with `map`/`filter`

Both of these must lower to the same plan:

```
var result = []                        val result = items
for item in items:                         .filter(valid)
    if valid(item):                        .map(convert)
        result.push(convert(item))
```

```
CollectionPlan
  Source(items) → Filter(valid) → Map(convert) → Collect(Array)
```

and the backend emits **one** loop with a pre-reserved builder — never a
materialised filtered array traversed a second time by `map`. This is classic
stream fusion: high-level pipelines compile to hand-written-quality imperative
loops with no intermediate collections, closure allocations, or tuples. Futhark
gets the same benefit by treating `map`/`reduce` as compiler-recognised semantic
operations rather than opaque library calls.

For Simple this means: **functional operations must become compiler-recognised
semantic operations, not ordinary eager runtime methods.**

It also means the compiler can optimise manual loops internally *before* the
lambda backends are repaired — which matters, because per §1 they are not
repaired. A user-facing source fix from loops to lambda-based `map`/`filter`
stays disabled until interpreter, JIT, LLVM AOT and self-hosted native agree.

## 4. CollectionPlan IR

MIR pattern infrastructure is too low-level: its generic rule pass supports
mainly single-instruction patterns, while these are structural multi-block
rewrites. Add a semantic IR between typed HIR and ordinary MIR.

```
enum CollectionPlanKind:
    Source, Map, Filter, CompactMap, FlatMap, Find, Any, All, Fold, Count, Take, Drop
    DistinctBy, IndexBy, GroupBy
    SemiJoinBy, AntiJoinBy, JoinBy, LeftJoinBy
    IntersectBy, DifferenceBy, CartesianProduct
    SortBy, MergeBy
    CollectArray, CollectSet, CollectMap

struct CollectionPlan:
    kind: CollectionPlanKind
    inputs: [CollectionPlan]
    effects: EffectSummary
    cost: CostExpr
    cardinality: CardinalityExpr
    order: OrderProperty
    uniqueness: UniquenessProperty
    memory: MemoryExpr
    source_span: AstLink
```

Nodes carry **facts**, not just an operation name. Example — a nested membership
loop becomes `SemiJoinBy(left: xs, right: ys, left_key: x.id, right_key: y.id,
preserve_left_order: true)`, with candidate physical plans `NestedLoopSemiJoin`,
`HashSemiJoin`, `MergeSemiJoin`, `DirectIndexSemiJoin`, `BitsetSemiJoin`.
**The planner chooses — not the parser, not the programmer.** This is the
logical/physical split databases have used for decades: PostgreSQL picks among
hash and merge joins, SQLite picks indexes from collected statistics, neither
changes the result.

## 5. One machine-readable operation-cost registry

Collection cost knowledge is currently duplicated across the source lint, the MIR
optimiser, runtime dispatch tables, stdlib implementations, backend symbol
tables, docs and lint logic. The `rt_array_map` finding in §1 is that duplication
failing in production: documented in one place, mapped in a second, defined in
none.

Single source of truth: **`config/compiler/collection_operations.sdn`**

```
operation array.contains:
    receiver: Array<T>
    effect: { reads: receiver }
    cost: { expected: linear(len(receiver)), worst: linear(len(receiver)) }
    allocation: constant

operation hash_set.contains:
    receiver: HashSet<T>
    effect: { reads: receiver }
    cost: { expected: constant, worst: linear(len(receiver)) }

operation text.codepoint_at:
    receiver: text
    cost: { expected: linear(index), worst: linear(bytes(receiver)) }

operation array.filter:
    effect: { combines: callback }
    cost: { expected: len(receiver) * cost(callback) }
    cardinality: { min: 0, max: len(receiver) }
    order: preserves
    allocation: output
```

Generated from it: lint cost models, HIR/MIR cost summaries, IDE hover, runtime
dispatch manifests, **backend symbol checks** (which would have caught
`rt_array_map` at build time), reference docs, contract tests, optimiser
legality tests.

## 6. Purity, effects and complexity are four separate questions

The current optimiser's `PURE_METHODS` set includes `contains`. But:

```
Is it pure?          yes        Is it constant-time?   not on Array
Does it allocate?    no         Can it be hoisted?     only if receiver+arg invariant
```

**A pure operation can still be O(n); repeating it n times is a hidden O(n²)
defect.** Maintain four independent summaries:

- **Effect** — `reads_receiver`, `writes_receiver`, `reads_global`,
  `writes_global`, `allocates`, `io`, `throws`, `suspends`, `nondeterministic`.
- **Cost** — `CostExpr`: `Constant | Size(sym) | Log | Add | Multiply | Max |
  OutputSize | Expected | Worst | Amortized | Unknown(reason)`.
- **Cardinality** — `map`: out = in; `filter`: 0 ≤ out ≤ in; `find`/`any`/`all`:
  scalar with early exit; `flat_map`: Σ child sizes; `cartesian_product`: l × r.
- **Order & uniqueness** — preserves left order / preserves inner order per key /
  unordered / stable / unique by key / sorted by key.

Order and uniqueness are what make a hash substitution *provably* observationally
equivalent. Without them the rewrite is a guess.

## 7. Diagnostics

Two families, kept apart.

**A. Functional-intent lints** (clarity + allocation; usually *not* asymptotic).
Manual `map`/`filter`/`compact_map`/`find`/`any`/`fold`/`retain` reimplementations,
with machine-applicable fixes via the existing `EasyFix` infrastructure. Clippy
is the model — and Clippy is careful to say when a rewrite does not change
asymptotics. So must Simple.

**B. Complexity lints** — extending the COLL namespace, not a new PERF one:

| Code | Default | Meaning | Status |
|---|---|---|---|
| COLL001–008 | as §2 | shipping | **done** |
| COLL009 nested_dynamic_iteration | Warn | two input-dependent iteration regions nested | new |
| COLL010 functional_linear_lookup | Warn / Deny in strict | linear op inside a **lambda** in a hot pipeline — closes the §2 gap | new |
| COLL011 repeated_materialization | Warn | `to_array`/`keys`/`flatten` recreated per iteration | new |
| COLL012 sequential_indexing | Warn | repeated indexed access that is linear (code-point indexing, linked data) | new |
| COLL013 repeated_sort | Warn | same collection sorted repeatedly | new |
| COLL014 unbounded_flat_map | Warn | nested output cardinality unknown/multiplicative | new |
| COLL015 accidental_cartesian_product | Warn / Deny in strict | every left/right pair examined or emitted | new |
| COLL016 missing_index | Warn | repeated key lookup with a safe index candidate | new |
| COLL017 complexity_regression | CI error | inferred polynomial degree or resource bound increased | new |
| COLL018 unknown_hot_callback_cost | Warn | callback in hot iteration has no cost summary | new |

Infer's cost analysis is the model for this layer: symbolic upper bounds from
instruction cost × loop bounds × constraints, comparable across revisions to
catch linear→quadratic regressions, and applicable to resources other than time
(allocations).

**Loop and functional syntax must produce the same diagnostic.** All three of
these are one defect:

```
for x in xs:                    xs.filter { |x| ys.contains(x) }
    if ys.contains(x): …        xs.filter { |x| ys.any { |y| x.id == y.id } }
```

### 7.1 Diagnostic shape

```
error[COLL010]: repeated linear lookup inside dynamic iteration
  ast://orders/process_orders/loop#2
      val user = users.find { |u| u.id == order.user_id }
                 ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Cost derivation:
    outer iteration   orders.len
    users.find        users.len × cost(id equality)
    estimated total   O(orders.len × users.len)

Candidate plans:
    1. Hash index   build users.index_by { |u| u.id }
                    expected O(users.len + orders.len), memory O(users.len)
    2. Merge lookup available when both inputs are SortedBy(user_id)
    3. Nested scan  retained when users.len is statically small

Automatic index rewrite was not applied:
    current backend cannot yet prove HashMap<K,V> support for key type UserId
```

It must explain the cost multiplication, which sizes are independent, candidate
algorithms, extra memory, **legality blockers**, and whether a machine fix
exists. The "not applied, because" line is what makes the diagnostic honest
while §1's P0 defects are open.

## 8. The rewrites worth automating

Each carries its own proof obligation. All are blocked on a generic `HashMap<K,V>`.

| # | Pattern | Plan | Cost |
|---|---|---|---|
| 8.1 | membership / existence | `ys.to_hash_set(key)` + `contains` | O(n·m) → exp. O(n+m), mem O(m) |
| 8.2 | first matching value | `index_by_first` | same |
| 8.3 | all matching pairs | `group_by` + `get_all` | exp. O(l + r + **output**) |
| 8.4 | no matching element | `anti_join_by` | exp. O(n+m) |
| 8.5 | match count | `frequency_by` | exp. O(n+m) |
| 8.6 | duplicate elimination | `distinct_by` w/ `HashSet` | O(n²) → O(n) |
| 8.7 | both inputs sorted | two-pointer merge | O(n+m+output), no hash |
| 8.8 | dense integer/enum keys | direct-index table or bitset | cheaper and deterministic |
| 8.9 | range predicates | sort+sweep, interval tree, binary search | **suggest only**, do not auto-apply |
| 8.10 | numeric kernels | loop interchange, tiling, vectorisation, GPU | **route to affine optimiser, never to hash** |

Three details that are easy to get wrong:

- **8.3's `output.len` term is not optional.** If every element shares one key,
  the result genuinely contains l × m pairs and no optimiser can avoid emitting
  them. A cost model that omits it will promise speedups it cannot deliver.
- **8.2 must not have a default duplicate policy.** Ship `index_by_first`,
  `index_by_last`, `index_by_unique`. A bare `index_by` that silently picks one
  is a correctness trap.
- **8.6 must not go through the current `array_uniq` text-key technique** —
  converting arbitrary values to text is costly and does not faithfully
  represent typed equality.

8.10 is the anti-goal: matrix multiply, convolution, rendering and DP legitimately
nest loops and need tiling/vectorisation/parallelism, which is Polly's domain,
not the planner's. Forcing them into hash form makes them slower.

## 9. API surface

```
# one-input
map filter compact_map flat_map find any all fold count_where sum_by distinct_by
# index construction
to_hash_set index_by_first index_by_last index_by_unique group_by frequency_by
# two-input
semi_join_by anti_join_by join_by left_join_by intersect_by difference_by
# explicitly output-sensitive
cartesian_product
```

Types that carry optimiser facts: `IndexedBy<K,V>`, `GroupedBy<K,V>`,
`SortedBy<K,V>`, `UniqueBy<K,V>`, `SmallBound<N,C>`. A signature like
`fn merge_join<K,A,B>(left: SortedBy<K,A>, right: SortedBy<K,B>)` removes the
uncertainty entirely — the proof is in the type, not in an analysis.

Functional source does not imply persistent immutable structures: specification →
private mutable `HashMapBuilder`/`ArrayBuilder` → freeze. Referentially
transparent source, transient implementation.

## 10. Fusion, and when it is illegal

```
map(f).map(g) → map(g∘f)              filter(p).count()  → count_where(p)
filter(p).filter(q) → filter(p∧q)     filter(p).any()    → any(p)
filter(p).map(f) → fused loop         filter(p).first()  → find(p)
map(f).fold(z,op) → one loop          filter(p).take(k)  → early-exit loop
```

Not unconditionally legal. Check: callback effects, exception **order**,
mutation and aliasing, observation of partially constructed output,
short-circuit behaviour, allocation-failure semantics, async suspension.
MLIR's rewriter is the structural model — a pattern declares an expected
benefit, must complete matching before mutating, and all IR changes go through
one controlled rewriter.

## 11. Cost-based selection — do not always pick the hash

```
NestedCost = N_outer × N_inner × C_equality
HashCost   = N_inner × (C_hash + C_insert) + N_outer × (C_hash + C_probe) + Alloc(cap)
```

Nested wins when the inner collection has 2–3 elements, a single lookup occurs,
hashing is expensive, allocation is forbidden, the path is cold, or the target is
constrained bare metal. Hash wins when the inner collection is nontrivial, many
lookups reuse one index, equality is expensive, the loop is hot, or the index can
be hoisted.

When static information is insufficient, emit a **guarded plan**:

```
if users.len <= optimizer_threshold(UserId):
    nested_lookup(…)
else:
    indexed_lookup(…)
```

The threshold is measured per backend, key type, equality/hash implementation,
memory model, target CPU and expected probe count. **No universal hardcoded
constant is correct.**

## 12. Profile-guided planning

Extend `.sprof` from function/block/edge counters to collection behaviour:
`collection_size`, `loop_trip_count`, `lookup_count`, `distinct_key_count`,
`join_output_count`, `filter_selectivity`, `hash_probe_count`,
`hash_collision_count`, `allocation_bytes`, `materialization_count`,
`early_exit_position` — keyed by **stable AST identity**
(`ast://module/function/collection-site#hash`), never line numbers. Store
`count/min/max/mean/p50/p95/sampled_histogram`.

With `users.len p95 = 24,000`, `orders.len p95 = 130,000`, distinct keys 23,900,
probe mean 1.3, the planner can hoist an index with confidence instead of
guessing. Chameleon showed runtime collection metrics driving automatic
collection adaptation; adaptive-join work defers the physical choice to runtime
with on-the-fly sketches when static statistics are missing.

## 13. Index sharing

A naive planner builds redundant indexes. Given observed lookups on `id`,
`company_id + role`, and `company_id`, choose `Index(id)` and
`Index(company_id, role)` — the composite covers the `company_id` prefix — rather
than all three. Soufflé formalises this as minimum-index-set selection covering
all searches.

Lifetime: build at the nearest dominator where the source is available and will
not mutate before all uses, and enough lookups reuse it; invalidate on mutation.
Cache by **collection identity + mutation/version ID + key-function identity** —
never by pointer alone, since storage can mutate in place.

## 14. Robust mode

Hash lookup is *expected* O(1), not guaranteed. Simple's `HashMap` chains and its
`HashSet` open-addresses, so adversarial collisions still degrade to long scans.
Represent `expected` / `amortized` / `worst` distinctly. Under
mission-critical/adversarial profiles prefer B-tree or ordered map (O(log n)
worst), direct-index array, bitset, tree-converted collision chains, keyed or
randomised hashing with collision monitoring, bounded-probe tables with rehash
fallback, or sorted vector + binary search for immutable data.

```
@complexity(expected_time <= linear(input.len), worst_time <= n_log_n(input.len))
```

rejects an unguarded hash plan whose worst case violates the contract. This ties
directly into the existing profile ladder (`moderate|strict|robust|critical`).

## 15. Legitimate nested loops

Not every nested loop is a defect. `for byte in packet: for bit in 0..8:` is
O(8n) = O(n). `for row in matrix: for col in matrix:` may be intentionally
quadratic. `for x in xs: for y in ys: emit(x,y)` may have quadratic *required
output*. Support explicit acknowledgement:

```
@allow(coll_nested_dynamic_iteration, reason = "all-pairs collision; entities.len <= 32")
@bounded(entities.len <= 32)
@complexity(time <= quadratic(entities.len), reason = "exact pairwise semantics")
```

An explicit `xs.cartesian_product(ys)` communicates that O(nm) output is
intended. It may still draw a budget warning, but it is not an accidental hidden
search.

## 16. Prior art applied

| Source | What Simple takes |
|---|---|
| Clippy | local AST recognition, applicability classification, machine fixes, honesty about non-asymptotic rewrites |
| Infer Cost | symbolic polynomial summaries, loop-bound multiplication, unknown propagation, allocation resources, differential regression checking |
| Stream fusion / Futhark | compiler-recognised operators; one imperative loop, no intermediates |
| PostgreSQL / SQLite | logical vs physical split driven by cardinality, indexes, ordering, memory, statistics |
| Cozy | longer-term synthesis of specialised representations from declarative retrieval |
| Soufflé | minimal shared index set covering all access patterns |
| Chameleon / adaptive joins | runtime metrics, guarded multi-version plans |
| MLIR | controlled region/DAG rewriting with explicit benefit and legality |
| egg / equality saturation | explore equivalent plans, extract cheapest — **bounded regions only** |
| AARA | optional deep-mode symbolic time/allocation bounds |
| Alive2 | translation validation of optimised vs original IR |
| Polly | separate affine numeric-loop path (§8.10) |

Equality saturation is a **later optional** feature. The research explicitly
documents e-graph explosion on long functional rewrite sequences; a small typed
CollectionPlan with bounded candidate enumeration is the safe first
implementation.

## 17. Compiler integration

New provider facts: `typed_hir`, `canonical_effect_summary`,
`collection_cost_summary`, `loop_bounds`, `alias_summary`, `mutation_summary`,
`cardinality_summary`, `order_summary`, `uniqueness_summary`, `collection_plan`,
`index_candidates`, `selected_collection_plan`. The existing optimiser-provider
architecture already models required/produced facts, cost classes, safety classes
and backend policies — extend `PassKind` and the descriptor registry rather than
adding ad-hoc invocations.

```
HIR type/effect completion → collection_plan_extract → complexity_summary
  → collection_fusion → index_candidate_analysis → collection_cost_planner
  → collection_plan_lowering → collection_opt → CSE/LICM/bounds → vectorise/lower
```

```
src/compiler/20.hir/collection_plan.spl
src/compiler/30.types/perf/cost_expr.spl
src/compiler/30.types/perf/collection_summaries.spl
src/compiler/40.analysis/collection_plan_extract.spl
src/compiler/40.analysis/complexity_analysis.spl
src/compiler/60.mir_opt/mir_opt/collection_fusion.spl
src/compiler/60.mir_opt/mir_opt/index_selection.spl
src/compiler/60.mir_opt/mir_opt/collection_plan_lowering.spl
```

**Do not replace `collection_opt`** (1,533 lines of working canonicalisation).
Split responsibilities: CollectionPlan owns algorithm selection, fusion, semantic
rewrites, indexes and joins; `collection_opt` keeps canonicalisation, CSE, length
reuse, bounds specialisation, concat/push cleanup, invariant hoisting.

## 18. Source auto-fix ≠ compiler optimisation

```
simple lint --group performance        report only
simple fix  --performance-style        loops → clearer functional source (unambiguous cases)
simple optimize --apply-safe           internal fusion/hoisting/capacity, no source change
simple optimize --apply-indexed        proved data-structure substitution
simple optimize --profile w.sprof      measured cardinalities and hotness
simple optimize --explain-collection-plan
```

`--explain-collection-plan` prints original complexity, candidate plans, the
selection, rejected plans **with reasons**, extra memory, required facts, and
static vs profile evidence. These are proposed interfaces; today's workflow still
distinguishes optimiser application from a fully exposed top-level command.

## 19. Verification

Algorithm-changing rewrites need more evidence than peephole optimisations.

- **Semantic tests** per rewrite: empty, singleton, duplicate keys,
  first-vs-last match, all-match output ordering, custom equality,
  hash/equality disagreement **rejection**, mutation during traversal,
  exceptions in key/predicate functions, side effects, nil/optionals, text
  normalisation, integer boundaries, deliberate hash collisions.
- **Cross-engine**: tree-walk interpreter, Cranelift JIT, LLVM AOT, self-hosted
  native, and the supported SimpleOS backend. Non-negotiable — current test
  defaults miss JIT-only collection and closure defects, which is precisely the
  §1 Red row.
- **Differential execution** on bounded random inputs: compare output, output
  order, side-effect trace, error result, resource constraints.
- **Scaling**: geometric sizes n, 2n, 4n, 8n. Record equality calls, hash calls,
  probes, loop-body count, allocations, copied bytes. **Operation counts are
  primary; wall time is supporting evidence only** — shared-host timing is noisy,
  as the style-producer investigation already showed.

```
describe "indexed semi-join scaling":
    it "keeps lookup work linear":
        val samples = measure_scaling([1_000, 2_000, 4_000, 8_000])
        expect(samples.hash_operations).to_scale_at_most(power: 1.15)
        expect(samples.equality_operations).to_be_less_than(samples.input_size * 4)
```

System tests invoke real compiled executables, never mocked collections.

## 20. Compilation-cost control

Default mode: one AST/HIR traversal, cached function summaries, SCC-based
interprocedural propagation, bounded candidate plans per region, **no
whole-program equality saturation**. Shape: O(function IR size) local,
O(nodes+edges) per affected SCC, O(recognised plans) comparison.

`--perf-deep` (hot functions, complexity contracts, explicit modules,
profile-identified bottlenecks only) may run restricted AARA, bounded equality
saturation, structure synthesis, translation validation, polyhedral analysis.

Cache key: function MIR hash + callee-summary hashes + registry version + target
capabilities + policy version. Unchanged body and callees ⇒ no re-analysis.

## 21. Priorities

**P0 — correctness prerequisites. Nothing in §8 may land before these.**

1. `rt_array_map` — implement and register, or remove the two dangling backend
   references. Currently both LLVM paths emit a call to an undefined symbol.
2. Closure object construction and tagged indirect-call ABI, JIT **and** LLVM.
3. Predicate forms of `any`/`all`.
4. Built-in `Dict` native insertion, before any Dict-backed index is synthesised.
5. Execution-based cross-backend functional collection tests.

Until complete: internal closureless loop fusion allowed; warnings and plan
explanation allowed; **source machine-fixes to lambda APIs gated; Dict index
synthesis disabled.**

**P1 — remove O(n²) from stdlib.** Replace `pure/collections.spl:55` `unique`
and `:73` `group_by` with set/map-backed implementations. Audit `array_uniq`,
`array_sort_by`, repeated slicing in small-array insertion sort, eager
flat-map/materialisation, duplicated collection implementations across runtime
families.

**P2 — generic index substrate** (promoted from P3 by §1.1). `HashMap<K,V,Hash,Eq>`
and `HashSet<K,Hash,Eq>` with specialisations for text, integers, enums, tuples,
interned symbols. **This is a prerequisite for P4/P5, not a nicety.**

**P3 — typed cost lint.** COLL009–012, COLL018 first (highest confidence, no
algorithm substitution needed), plus the functional-form coverage that closes the
§2 gap.

**P4 — CollectionPlan + fusion.** Normalise loops and chains to one plan; emit
closureless loops.

**P5 — equality-key index planner.** High-confidence forms only: semi-join,
anti-join, first match, all equijoin matches, frequency, distinct. **Not**
arbitrary predicates.

**P6 — PGO and adaptive planning.** `.sprof` v2 + guarded nested/hash/merge.

**P7 — research features.** Index sharing, composite indexes, range/spatial plans,
bounded equality saturation, AARA deep mode, polyhedral numerics, translation
validation.

## 22. Policy

1. Explicit nested iteration over two dynamic inputs warns by default.
2. A linear operation inside input-dependent iteration is a stronger warning,
   and an error in performance-strict mode.
3. **Functional syntax does not bypass complexity checks.**
4. Functional operations lower to a semantic plan and fuse into imperative loops.
5. The compiler may substitute an index only when equality, duplicate behaviour,
   ordering, effects, mutation, memory and profitability are proven or guarded.
6. Intentional Cartesian products and bounded nested loops are permitted via
   explicit operators or checked contracts.
7. Expected, amortized and worst costs stay distinct, especially for hashes.
8. Every algorithm-changing optimisation emits an explainable plan and is covered
   by execution parity, differential correctness and scaling tests.

Target architecture: functional intent + typed symbolic complexity analysis +
loop/stream fusion + cost-based HashSet/HashMap/join selection + profile-guided
adaptive plans + robust effect/order/duplicate proofs + translation and scaling
verification.

This makes functional code the *safer* path in Simple without pretending that
`map` and `filter` alone remove quadratic algorithms.

## 23. Open questions

- Does `IndexedBy<K,V>` need to be a real type, or is a phantom refinement on
  `[T]` enough? A real type forces API churn; a refinement is harder to preserve
  across calls.
- Where does the cost registry live at runtime — baked into the binary, or read
  from `config/`? Baking is faster; reading makes the registry testable without
  a rebuild.
- Is `@bounded(expr)` checked, assumed, or profile-verified? All three have
  precedent; only the first is sound.

## Cross-references

- Plan: `doc/03_plan/agent_tasks/collection_planner_parallel_agents_2026-07-31.md`
- Existing lint: `src/compiler/35.semantics/lint/collection_patterns.spl`
- Existing MIR pass: `src/compiler/60.mir_opt/mir_opt/collection_opt*.spl`
- Dict native pitfalls: `doc/07_guide/language/dict_native_pitfalls.md`
- Prior perf plan: `doc/01_research/compiler/performance/performance_optimization_plan.md`
