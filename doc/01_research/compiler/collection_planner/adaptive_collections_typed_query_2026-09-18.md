# Adaptive collections + typed dataframe queries — next step for the collection planner

**Date:** 2026-09-18
**Status:** research — merges two external design reports (2026-09-16) into the
accepted collection-planner line; readiness re-verified against `origin/main`
`c3927751dc1`. No build/test/benchmark was run for this document.
**Follows:** `collection_plan_ir_2026-07-31.md` (same directory). That document
stays the entry point for the CollectionPlan IR, the COLL lint family and the
P0–P7 priorities. This one adds two extensions on top of it and does not
replace any of its decisions.
**Plan:** `doc/03_plan/compiler/collection_planner/adaptive_collections_typed_query_rc1_plan_2026-09-18.md`
**Design:** `doc/05_design/compiler/collection_planner/adaptive_collections_typed_query_design.md`

Merged sources (not checked in, summarized here):

- **Report A** — *Simple Adaptive Collections: unified profiling, in-place
  attributes, and safe physical-plan switching* (pinned `6a133cf2bd2`).
- **Report B** — *Simple Typed DataFrame-able Collections and Query Optimizer*
  (observed `41187e926c5`).

The two reports overlap ~40% (profiling, CollectionPlan, storage layout, GPU,
verification). This merge keeps each decision once.

## 0. Thesis

One logical model, one evidence system, several independent physical decisions.

```
source loops / map / filter ─┐     @col(...) local attrs ─┐
typed query  xs[.f >= 1]  ───┼─> typed HIR ─> QueryExpr   ├─> ResolvedCollectionPolicyV1
set literal  {a, b}  (later) ┘        │                    │      (one resolver)
                                      ▼              SDN policy DAG ┘
                              logical CollectionPlan  (the 07-31 IR, extended)
                                      │  cardinality/order/uniqueness/effects/cost
                     O1 local │ O2 bounded │ O3 cost+profile   (existing opt levels)
                                      ▼
                           PhysicalCollectionPlanV1
             primary+indexes │ StorageLayoutPlanV1 (frozen, reused) │ scalar/SIMD/GPU
                                      ▼
                       verified MIR → interp / JIT / native
                                      │
             ProfileSessionV2 (.sprof v2): counters, regions, samples,
             collection summaries, alloc/COW, field co-access, device
                                      └──> report / advice SDN / plan receipt
```

Five merged decisions:

1. **Typed record collections are dataframe-able.** `xs[.age >= 18][.name, .score]`
   on `[User]` lowers to CollectionPlan nodes. `.field` is a compiler-resolved
   `FieldId`, never a string. `std.df.DataFrame` stays the dynamic-schema escape
   hatch. (B)
2. **`col<T>` is a capability alias, not a keyword or a boxed object.** Semantic
   families (sequence / set / map) never change with a profile; only physical
   representation may. (A)
3. **Local attributes and SDN produce one `ResolvedCollectionPolicyV1`.** Hard
   constraints intersect (conflict = error); soft hints use a fixed precedence. (A)
4. **One profiling architecture, several collectors.** Collection counts, region
   timings, CPU samples, alloc/COW, field and device records share session and
   identity metadata but keep their distinct meanings. Profiles are cost
   evidence, never proof of immutability, ownership or aliasing. (A+B)
5. **Optimizer cost is budgeted by the existing O-levels.** No `--df-opt-level`.
   O0 = faithful lowering, O1 = cheap local fusion, O2 = bounded complexity
   safety, O3 = profile/cost/GPU search with hard caps and fallback to the O2
   plan. (B)

Ordering: contracts + report-only analysis first, transformations later,
runtime switching last. Grammar changes (`.field`, `{a, b}`) are **post-RC1**
(§6).

## 1. Readiness — re-verified 2026-09-18 against `c3927751dc1`

Both reports and the 07-31 table disagree in places; this table is the current
truth. "Planned" = named in a design doc, absent from the tree.

| Area | Status | Verified finding | Changes |
|---|---|---|---|
| `.sprof` v1 loader | Green | `src/app/optimize/sprof_loader.spl` — function/block/edge records only, saturating merge, hot-path policy. | Collection records need a versioned v2 codec (§4). |
| Native counter transport | Green | `src/app/compile/native_profile_counter_runtime.spl` — same three record kinds. | Extend, don't add a second exporter. |
| Region profiler | Amber | `src/compiler/90.tools/perf/profiler.spl` — clock read + text-keyed dict per event. | Too heavy for per-lookup probes; keep for regions only. |
| Compiler-stage adapter | Amber | `85.mdsoc/adapters/in/profiler_adapter.spl` — stage count + last stage, no durations. | Keep compiler self-profile separate from program profile (`subject_kind`). |
| JIT hotspot bridge | Green | `95.interp/execution/sprof_hotspot_bridge.spl` — primitive inputs, no app import. | Keep direction; add typed collection-profile query. |
| Optimizer plugin registry | Green | `60.mir_opt/optimizer_plugin.spl` — scope/application/cost descriptors. | Registration ≠ activation; transforms need witnesses. |
| MIR collection optimiser | Amber | `60.mir_opt/mir_opt/collection_opt{,_core,_patterns}.spl` is the **real** owner. | Report A/B roots `60.mir_opt/collection_plan`, `20.hir/perf`, `config/compiler/collection_operations.sdn` are **MISSING** — planned only. |
| Storage layout | Green (narrow) | `common/structural/storage_layout/{storage_layout_contracts,planner}.spl` — frozen `StorageLayoutPlanV1`, AoS/SoA/AoSoA/Grouped/Tiled/Packed/…; x86_64 custom-native typed-storage path only. | Compose, never extend V1; public `T[]` switching is not available. |
| Generic `Map<K,V>` | Amber — **CORRECTS 07-31 §1.1** | `nogc_sync_mut/src/map.spl:20` `struct Map<K,V> where K: Hash + Eq`, bucket lists + cached hash. | The index substrate is not absent; it is unaudited for backend parity. P2 becomes "audit + adopt `Map`", not "write one". |
| Text HashMap / HashSet | Red (unchanged) | `collections/hashmap.spl:86` `get(key: text) -> text?`; `hashset.spl:120` `contains(value: text)`. | Never use as generic index. |
| `rt_array_map` (07-31 P0.1) | Green — **CLOSED** | Defined in `runtime_native.c`, declared in `runtime.h`, present in `runtime/src/value/collections.rs`. | P0.1 needs only a parity test, not implementation. |
| Pure `unique` (07-31 P1) | Green — **FIXED** | `gc_async_mut/pure/collections.spl:61` Dict-backed. | — |
| Pure `group_by` (07-31 P1) | Amber | Same file, linear slot scan, O(n·k), carries a `# ponytail:` upgrade note. | RC1 lane. |
| `std.df` unique | Red — **CONFIRMED** | `df/mod.spl:194,214` `unique_f64`/`unique_i64` grow `seen` + `*_group_index` linear search → O(n²). | RC1 lane. |
| Seed brace parsing | Fact | `compiler_rust/parser/.../collections.rs` routes `{…}` to dict; `{}` = empty Dict. | `{a,b}` is an additive grammar change; `{}` keeps Dict meaning. |
| Attribute helper | Amber | `10.frontend/parser_extensions.spl` handles `@name(scalar args)`; local-binding retention end-to-end unproven. | Must be proven before `@col` is accepted. |
| SDN includes | Unverified | Shared SDN parser exists; no recursive include contract found. | Includes are a policy-loader feature, not SDN syntax. |
| Opt levels | Green | `60.mir_opt/_OptimizationPasses/engine.spl` — None/Basic/Standard/Aggressive + Debug/Size/Speed. | Query planning joins these. |
| COLL lint | Green | `35.semantics/lint/collection_patterns.spl` + `app/io/cli_lint_commands.spl`. | New complexity rules extend `COLL`, no new prefix. |

Still open from 07-31 P0 (unverified here, keep as gates): closure/indirect-call
ABI in JIT+LLVM, predicate `any`/`all` parity, native `Dict.set` insert drop,
cross-backend functional tests.

## 2. Language surface (merged)

| Surface | Meaning | Rule |
|---|---|---|
| `[a, b]` | ordered sequence with duplicates | unchanged |
| `{k: v}` / `{}` | exact map; `{}` is empty Dict | unchanged |
| `{a, b}` | exact set | additive parser change, **post-RC1**; until then `Set<T>.new()` |
| `col<T>` | multipass collection capability | library alias; monomorphised, no implicit boxing |
| `xs[.f]`, `xs[pred]`, `xs[.a, .b]` | field column / filter / projection over current row | **post-RC1** grammar; `.f` resolved against element record type |
| `obj.f` / `.f` / `@tag` / `$x` | explicit field / implicit row field / attribute / existing dollar | keep the four roles disjoint |

Capability chain: `Iterable<T>` ⊃ `col<T>` ⊃ `Bidirectional` ⊃ `RandomAccess`;
orthogonal `MutableElements`, `RangeReplaceable`, `KeyLookup`,
`UniqueMembership`, `ContiguousStorage` (only when guaranteed). A sequence with
heavy membership tests may gain a side index; it may never become a set.

Joins and correlated queries need explicit row binders
(`users.join(orders, \u, o: u.id == o.user_id)`); implicit `.f` is single-scope
only. Nested paths (`.profile.address.city`) resolve to `FieldPath`. Runtime-
dependent schemas (pivot on data values, untyped JSON, string column names)
leave the typed path for `DataFrame`; `df.cast<Row>()?` re-enters it after
runtime validation.

Lexer rule to pin (regression corpus): `DOT IDENT` → implicit field ref;
`DOT DIGIT` keeps tuple-index rules (`t.0`, `n.0.1`); `.5` stays invalid
(`0.5`); ranges `1..2`, `1..=2`, `1...` unaffected. `(.a > 0) and .b` must parse
without special `[.` dispatch — this also keeps it GPU-parser friendly (flat
`ImplicitFieldRef(token)` node, binding on CPU).

## 3. Local attributes + SDN policy

Proposed local forms (existing `@name(args)` spelling, constant args only):

```simple
@col(auto, lookup_heavy, build_then_read)
@col_site("compiler.resolve.symbols")
var symbols: {text: Symbol} = {}

@col_impl(flat_hash)          # physical pin: admitted impl or error
@col(no_switch)
var fixed: {i64: i64} = {}
```

Categories: workload hint (may be wrong, stays correct), objective
(`compact`/`throughput`/`startup`/`latency`), switch permission
(`no_switch`/`switch_at_boundary`), physical pin (must hold or error),
assurance requirement (proved, never weakened), site label (namespace-unique).
`in_place_only` is a real execution constraint: no replacement payload buffer,
diagnostic if no legal in-place kernel. Unknown tags, bad attachment, or a
silently dropped attribute are **errors**.

SDN: plain data fields; `includes` / `optional_includes` interpreted by the
policy loader (relative paths, cycle detection, depth/file/byte bounds, root
restriction, digest recorded). Precedence:

- **hard constraints intersect** — ABI, ownership, assurance, explicit pins;
  conflict is an error, never last-writer-wins;
- **soft hints**: local source > exact-site SDN rule > named policy >
  module/project default > accepted generated advice > compiler default;
  same-rank conflict on one field is an error.

Three artifacts stay separate: observed `.sprof`, generated advice SDN (never
overwrites hand-authored policy), selected plan receipt (reproducible builds
consume reviewed advice + frozen receipt).

## 4. Profiling and `.sprof` v2

| Collector | Answers | Must not be inferred |
|---|---|---|
| Region timer | inclusive elapsed per region | op counts, exclusive container time |
| CPU sample / PMU | where time/stalls concentrate | coverage from absent samples |
| Fn/block/edge counters | executed paths | sizes, mutations |
| Collection summary | per-origin op mix, hit/miss, sizes, phases | ns/op from counts |
| Alloc / COW | allocations, copies, detaches per generation | unique ownership |
| Field co-access | fields read together per loop | disjointness |
| Query site (B) | input/output size, selectivity, join/group cardinality, temp bytes | correctness |
| Device | launch/transfer/wait per plan generation | end-to-end speedup from kernel time |

Identity: `RunId/WorkloadId/SubjectBuildId/TargetFingerprint`,
`CollectionOriginId` (semantic creation origin + canonical type fingerprint,
not a pointer or line), `CollectionOperationId` (resolved semantic op, not
spelling), `StorageGeneration`, `LoopOrKernelId`, policy/plan digests. Moves
keep lineage; semantic copies create a new logical value; COW detach and
migration create a new storage generation. Resize reinsertions are maintenance,
not user inserts.

Metrics that planning needs and are easy to get wrong: insert-attempt vs
new-key, erase-attempt vs existing-key, value-replace vs key-mutate;
instance-weighted vs operation-weighted vs time-weighted size (never average
percentiles; bucketed p95 is an interval); censored lifetimes at shutdown;
fixed op-count phase windows (final lifetime is unknown online).

Modes: `off` (probes, TLS, header fields and deps absent from the binary —
verified in generated code), `basic` (per-thread numeric site slots, no clock,
no text key), `sampled` (inclusion probabilities retained, randomized
windows), `deep` (selected sites), `adaptive-runtime` (opt-in, overhead
reported separately). Recorder uses a non-instrumented arena with a recursion
guard.

`ProfileSessionV2`: schema major/minor, subject kind/build, workload + weight,
target, instrumentation manifest digest, clock domains, sampling description,
shards, completeness/dropped data; typed optional records with explicit
kind/version/length/required flag. Unknown required → fail; unknown optional →
skip; v1 inputs still read; explicit v1 export for legacy consumers. Dedup by
run/shard/sequence; saturating merge; missing ≠ zero; no plaintext keys/values
by default. Profile data is untrusted optimizer input.

## 5. Planning, cost, switching (merged catalogue)

**Plan nodes to add to the 07-31 IR** (not a separate `DfPlan`): `Project`,
`ExtendRecord`, `Aggregate`, `GroupAggregate`, `Window`, `Scan`, `TopK`,
`Limit`, `Slice`, `Pivot`, `Melt`, `Zip`, `AsofJoin`, `ScanSource`,
`Materialize`. Each carries schema, cardinality, ordering
(`Unordered`/`PreservesInputOrder`/`SortedBy`/`Stable`), uniqueness, effects,
cost, memory, span.

**Rewrites by level** (legality gate per rewrite; B §6):

| Level | Rewrites |
|---|---|
| O0 | none — faithful scan/predicate/emit; must work in interpreter |
| O1 | expr simplify/const-fold, filter+filter / filter+project fusion, required-field set, reserve, trivially-safe known-quadratic stdlib fixes |
| O2 | predicate/projection/limit pushdown, join/semi-join recognition, hash/direct/sort distinct + group, `IndexBy` for repeated equality filters, TopK, sort reuse, prefix/incremental windows, SIMD legality, COLL remarks when blocked |
| O3 | profile import, bounded join-order DP (≤ cap, else greedy), secondary-index synthesis, common subplans, late materialization, dictionary encoding, layout feedback, GPU/offload costing |

**O(n²) prevention** (B §7): nested membership → semi-join; nested equality
find → hash/merge/index join; cross-product+equality → join; growing `seen` →
hash/sort/bitset distinct; scan-existing-groups → hash/direct group; repeated
filter per key → `IndexBy` once; sort+head → TopK; expanding/rolling
recompute → prefix/incremental; concat/string concat in loop → builder
(existing COLL001/006); row-object per element → column loop. Planning uses
asymptotic cost **plus** estimated cardinality, build cost, memory and reuse —
a 4-element nested loop can be correct and fastest. `COLL017
complexity_regression` compares symbolic summaries across revisions; fails CI
only at high confidence.

**Physical plan is a product** (A §6.2): primary storage × indexes ×
`StorageLayoutPlanV1` ref × residency × dispatch × admitted transitions ×
evidence refs × steady/peak memory × fallback. Search = legality prune →
backend capability prune → bounded beam/Pareto, reason emitted on early stop.
Time model sums construction, per-op × size-bucket calibrated cost, index
maintenance, resize, dispatch, alloc/COW, conversion, transfer, launch, sync,
deopt. Memory models (flat hash ≈ `C·(K+V+1)`, side index, MPHF, direct index
over range `R`, bitmap) are models, not measured Simple sizes. Peak =
old + new + scratch + indexes + device mirrors + unreclaimed generations.

**Switching modes** kept distinct: static/AOT, creation-time, growth
promotion, phase/boundary, temporary view, online adaptation, JIT code
specialization. Changing code ≠ changing storage. Every specialization has a
valid-operation fallback that preserves the original error/resource contract;
a profile that never saw an insert does not authorize removing insert.
Hysteresis: minimum evidence, conservative gain, dwell time, byte/latency
budget, transition cap, separate promote/demote thresholds, stop on
prediction error. Runtime reevaluation never reopens SDN or plans on a lookup
path.

**Migration** starts exclusive/quiescent only: admit → exclusive or snapshot →
build B within peak budget → validate → publish generation g+1 at safe point →
retire A after leases/fences. Failure leaves A live. Escaping/raw borrows pin;
iterator invalidation guarantees preserved; COW aliases isolated; view key =
source generation + schema + layout + field versions + device. FFI/MMIO/DMA/
wire ABI pins are hard; `@layout(soa)` never overrides a C-ABI AoS pin.

**UDFs:** `AnalyzablePure` inline into `QueryExpr`; opaque/effectful are
barriers (no reorder, no GPU, cost unknown). **Nulls:** Simple `Option`
semantics defined explicitly (nil equality, nil predicate, nil join keys,
nil sort order, aggregate skip) — not SQL, not pandas; `std.df` keeps its
documented mask behavior. **GPU:** batch/residency only, transfer-inclusive
cost, real completion fences, no per-lookup offload; unavailable device =
`Blocked`, never "passed by simulation".

**Optimizer self-cost** (B §9, LLVM new-PM lessons): one cached analysis
snapshot per revision; passes grouped per function/plan region; worklist
revisits only affected nodes; rewrite-round and node-growth caps; hash-consed
numeric expression IDs (no text keys); arena-allocated transient nodes;
incremental cache keyed by HIR digest + registry digest + level + profile +
target digests; per-build metrics (nodes before/after, time per phase, peak
plan memory, rewrites applied/rejected, budget exhaustions). Budget hit →
keep last valid plan, remark, continue — never a compile failure.

**Interpreter:** compact typed query bytecode on the cold path, cached
O1/O2 canonical plan per (plan hash, schema, layout generation), hot plans
tier into the existing tiered JIT with deopt on representation/schema/residency
change; plan cache bounded.

## 6. RC1 scope decision

RC1 is a stabilization release (`X.Y.Z-rc.N` per
`doc/07_guide/infra/software_release.md`; latest tag `v1.0.1-beta.1`). Grammar
changes need seed-Rust + self-hosted + formatter + IDE + GPU-lexer parity and
therefore cannot be RC1 work.

- **RC1-eligible (additive, report-only or correctness):** remaining 07-31 P0
  parity tests, `group_by` and `std.df` unique O(n²) fixes, `Map<K,V>` audit,
  semantic contract + origin IDs, `.sprof` v2 schema with v1 compatibility,
  collection counters in `basic` mode with compiled-out proof, report-only
  planner + explain, COLL complexity lint extensions, dot-number lexer
  regression corpus (tests only), optimizer compile-time/RSS baselines.
- **Post-RC1:** `.field` / `{a,b}` grammar, `@col` acceptance end-to-end, any
  representation-changing transform, runtime switching, layout switching of
  public arrays, SIMD/GPU execution, O3 global search.

Nothing enabled in RC1 may change program output; every RC1 artifact is
either a correctness fix with a spec or an opt-in report.

## 7. Prior art (combined)

Report A: Makor et al. 2025 (allocation-site PGO replacement), Cozy / Loncaric
ICSE'18 (query + update synthesis), LLAMA 2022 and LLAMA/AdePT 2023 (logical
vs physical layout, field heatmaps), Radtke & Weinzierl 2025 (annotation-guided
AoS→SoA views), PyPy storage strategies (fallback), Roaring bitmaps
(chunk-local adaptation), Swift collection protocols (capabilities), Clang PGO
(sampling ≠ instrumentation), Futhark short-circuiting (memory/dependence),
SoCal 2026 preprint (recursive ADT layout, later), Abseil Swiss tables.
Report B: pandas user guide (coverage, vectorization), Kotlin DataFrame
compiler plugin (static schema tracking), Polars and DuckDB optimizers
(pushdown, join order, TopN, dynamic join filters), DataFusion, Apache Arrow
columnar format (interop), Weld (cross-library fusion), LLVM New Pass Manager
(analysis caching, avoiding quadratic compile time).

## 8. Open questions (added to 07-31 §23)

- Does the projected schema of `xs[.a, .b]` get a structural or nominal type?
  Structural is simpler; nominal is required once it crosses a public API.
- Is `@col_site` namespace per module or per package?
- Can `ProfileSessionV2` live in `src/lib/common` (so compiler core consumes it
  without importing `app.optimize`) without pulling file I/O below the app layer?
- Which O2 budget defaults are safe? Must come from the compile-time corpus
  (plan W0), not from the illustrative numbers in Report B §21.
