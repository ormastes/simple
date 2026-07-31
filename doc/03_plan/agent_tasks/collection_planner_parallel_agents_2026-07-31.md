# Collection planner — parallel agent plan

**Date:** 2026-07-31
**Research:** `doc/01_research/compiler/collection_planner/collection_plan_ir_2026-07-31.md`
**Method:** disjoint-ownership lanes, fail-closed gates, orchestrator verifies every
lane against the live tree. **No lane is accepted on its own report alone.**

## Ground rules

1. **Disjoint file ownership.** Two lanes never edit the same file. The Owns
   column is the contract; a lane that needs a file it does not own files a
   request instead of editing.
2. **Agents do not commit.** The orchestrator reviews diff + evidence, then pushes.
3. **Evidence bar per lane:** the exact command run, its output, and a
   before/after on a real repo file. A lane reporting "should work" is `blocked`,
   not `pass`.
4. **Every lane records `pass` / `blocked` / `filed`.** No lane self-declares
   production-ready.
5. **P0 gate is hard.** No lane in Wave 3+ may synthesise a lambda-based rewrite
   or a Dict-backed index until W1 lanes are green in all five engines.

## Wave 0 — landed 2026-07-31 (this session)

| Lane | Owns | Result |
|---|---|---|
| **AF1** span plumbing | — | **Abandoned, reverted.** Added `span: i64` to `CollectionLintWarning` fed from `stmt_get_span`/`expr_get_span`. A probe showed the AST span pool is **empty on the lint CLI path** (`e=7 espan=0 sspan=0 left=0`, `span_is_valid` false), so no span-based fix can work here. `collection_patterns.spl` is byte-identical to origin. Two traps found on the way, both worth knowing: `stmt_assign_stmt` has **zero callers** — the parser emits assignments as `STMT_EXPR` wrapping `EXPR_ASSIGN`, so every `STMT_ASSIGN` branch in that lint is dead code. |
| **AF2** COLL EasyFix | `90.tools/lint/_LintMain/entry_and_fixes.spl` | **Landed `9feda786614a`.** `collection_easy_fix()` emits a real `Replacement` for COLL001 (`arr = arr + [x]` → `arr.push(x)`, Certain); COLL diagnostics report the **offending line** instead of the enclosing `fn` line. Location is recovered **textually**, matching `lint_cli_find_fn_line`, because of the AF1 finding. Multi-element `arr + [a, b]` warns without a fix. Verified by `test/01_unit/compiler/lint/collection_easy_fix_spec.spl` — 3 examples, 0 failures, and the spec discriminates (it reported "line 1, expected 4" against the span attempt). COLL007's `.pop()` rewrite is present but **unreachable**: the rule never fires. Filed as `doc/08_tracking/bug/coll007_does_not_fire_on_array_rebuild_2026-07-31.md`. |

**Not deployed.** `bin/release/<triple>/simple` still predates this, so `simple lint --fix`
does not yet offer the COLL001 fix. Stage 4 is blocked on two `A`-staged files from
another session (`vulkan_backend.spl:1008` parse error,
`cranelift_codegen_adapter.spl:305,312` dict/int type mismatch).

Why only two rules: COLL002 needs a hoisted `HashSet` (blocked — the pure
`HashSet` is text-keyed, `hashset.spl:112`), COLL003 needs a whole-loop cursor
rewrite, COLL005 needs predicate merging across two closures (blocked on the
lambda ABI), COLL006 needs a builder declared outside the loop. Shipping a fix
for those before the substrate exists would produce wrong code with an
auto-apply flag on it.

## Wave 1 — P0 correctness prerequisites (BLOCKING)

Nothing downstream may assume a working functional collection path until these
close. Run in parallel; all five must be green before Wave 3 starts.

| Lane | Owns | Task | Done when |
|---|---|---|---|
| **P0-MAP** | `70.backend/backend/llvm_lib_translate.spl`, `compiler_rust/…/codegen/llvm/functions.rs`, runtime | `rt_array_map` is **declared at `llvm_lib_translate.spl:416` and mapped at `functions.rs:2790` with no definition anywhere** — both LLVM paths emit a call to an undefined symbol. Implement it, or remove both references. | `Array::map` executes under LLVM AOT, or the two dangling references are gone and the compiler rejects the call with a clear error. |
| **P0-ABI** | closure construction + tagged indirect call, JIT and LLVM | Closures demote JIT→interpreter on ABI defects. Fix the object layout and indirect-call convention. | Same closure program gives identical results in interpreter, JIT and LLVM AOT, with no demotion log line. |
| **P0-PRED** | `any` / `all` predicate forms | Backends diverge on the predicate-taking overloads. | Cross-engine parity spec green. |
| **P0-DICT** | built-in `Dict` native insert | `.set(k,v)` silently drops inserts under native codegen. | Native `.set` round-trips, **or** `.set` is removed and every site uses `d[k] = v`. |
| **P0-TEST** | `test/01_unit/compiler/collections/` | Execution-based cross-backend functional collection suite: interpreter, JIT, LLVM AOT, self-hosted native, SimpleOS backend. | Suite exists and runs all five; failures visible, not skipped. |

**Gate:** P0-TEST green across five engines. Until then, `--fix` may not emit any
lambda-based rewrite, and no index may be synthesised on `Dict`.

Naming note: `P0-MAP` here is a collection-lowering lane and is unrelated to the
structural-compute `MAP` (mapping-graph) lane in
`doc/03_plan/platform/structural_compute/README.md`; keep the `P0-` prefix when
cross-referencing to avoid the collision.

## Wave 2 — stdlib, runnable now (independent of Wave 1)

| Lane | Owns | Task | Done when |
|---|---|---|---|
| **STD-UNIQ** | `gc_async_mut/pure/collections.spl` | `unique` (`:55`) and `group_by` (`:73`) both grow a result array with an inner linear scan — genuinely O(n²). Replace with set/map-backed versions. | Scaling test at n, 2n, 4n, 8n shows equality-call count growing ≤ linearly. |
| **STD-HASH** | `nogc_sync_mut/src/collections/hashmap.spl`, `hashset.spl` | These are **monomorphic text dictionaries**, not specialisations: `hashmap.spl:86` is `fn get(key: text) -> text?`, `hashset.spl:112` is `fn contains(value: text) -> bool`. Add `HashMap<K,V,Hash,Eq>` / `HashSet<K,Hash,Eq>` with fast paths for text, integers, enums, tuples, interned symbols. | A generic map with a non-text key type round-trips in all five engines. |
| **STD-AUDIT** | `array_uniq`, `array_sort_by`, small-array insertion sort | Audit for repeated slicing, eager materialisation, text-key coercion of typed values, duplicated implementations across runtime families. | Findings filed with file:line; quadratic ones fixed or filed. |

**STD-HASH is a hard prerequisite for Wave 4 and Wave 5.** It was previously
scheduled as a P3 nicety; the audit shows it is the substrate everything else
needs. Sequence it first inside this wave.

## Wave 3 — cost registry and lint extension (after Wave 1 gate)

| Lane | Owns | Task | Done when |
|---|---|---|---|
| **REG1** | `config/compiler/collection_operations.sdn` (new) | Single machine-readable operation registry: effect, expected/worst cost, allocation, cardinality, order, uniqueness per operation. | File exists, parses, covers every operation the lint and the MIR optimiser currently hardcode. |
| **REG2** | registry codegen | Generate lint cost models, HIR/MIR cost summaries, IDE hover, runtime dispatch manifests, **backend symbol checks**, reference docs, contract tests from REG1. | The backend symbol check independently rediscovers the `rt_array_map` gap from Wave 1. That is the acceptance test. |
| **LINT1** | `35.semantics/lint/collection_patterns.spl` | Add COLL009 (nested dynamic iteration), COLL011 (repeated materialisation), COLL012 (sequential indexing), COLL018 (unknown hot callback cost). | Each fires on a crafted fixture and stays silent on a bounded-inner-loop fixture. |
| **LINT2** | new file under `35.semantics/lint/` | **COLL010 — the functional-form gap.** Today `xs.filter { \|x\| ys.contains(x) }` is invisible to COLL002 because it is not a `for` statement. Functional syntax must not be a way to hide O(n²). | Loop form and both lambda forms of the same defect produce the same diagnostic code. |
| **LINT3** | `90.tools/lint/_LintMain/entry_and_fixes.spl` | Extend `collection_easy_fix` as rules gain safe rewrites. **Do not** open a `PERF001…` namespace — COLL001–008 already ship and PERF001/002/003/011 would duplicate them. The seed's `checker_performance.rs` should consume REG1, not re-derive the knowledge. | New rules attach fixes only where the rewrite is statement-local. |

## Wave 4 — CollectionPlan IR (after Wave 3 + STD-HASH)

| Lane | Owns | Task |
|---|---|---|
| **CP1** | `20.hir/collection_plan.spl` | `CollectionPlanKind` enum + `CollectionPlan` node carrying effects/cost/cardinality/order/uniqueness/memory/span. |
| **CP2** | `30.types/perf/cost_expr.spl`, `collection_summaries.spl` | `CostExpr` algebra and the four independent summaries. **Purity, allocation, constant-time and reorderability are four separate questions** — the current `PURE_METHODS` set conflates them, which is how a pure O(n) `contains` hides inside a loop. |
| **CP3** | `40.analysis/collection_plan_extract.spl` | Lower **both** explicit loops and functional chains to the same plan. |
| **CP4** | `40.analysis/complexity_analysis.spl` | Symbolic bounds; interprocedural via SCC; feeds COLL017 regression detection. |
| **CP5** | `60.mir_opt/mir_opt/collection_fusion.spl` | Fusion rules with the legality checks: callback effects, exception **order**, aliasing, partially-constructed output, short-circuit, allocation failure, async suspension. |
| **CP6** | `60.mir_opt/mir_opt/collection_plan_lowering.spl` | Emit one closureless loop with a pre-reserved builder. Never materialise an intermediate. |

**Do not touch `collection_opt*.spl`** (1,533 working lines). It keeps
canonicalisation, CSE, length reuse, bounds specialisation, concat/push cleanup
and invariant hoisting. CollectionPlan owns algorithm selection only.

## Wave 5 — index planner (after Wave 4)

| Lane | Owns | Task |
|---|---|---|
| **IDX1** | `60.mir_opt/mir_opt/index_selection.spl` | Candidate detection for the six high-confidence forms only: semi-join, anti-join, first match, all equijoin matches, frequency, distinct. **Not** arbitrary predicates. |
| **IDX2** | cost model | `NestedCost` vs `HashCost`; emit a **guarded plan** when static info is insufficient. No universal hardcoded threshold — measure per backend, key type, hash/eq impl, memory model, CPU. |
| **IDX3** | API | `index_by_first` / `index_by_last` / `index_by_unique` as **distinct** operations. A bare `index_by` that silently picks a duplicate winner is a correctness trap. |
| **IDX4** | diagnostics | `--explain-collection-plan`: original complexity, candidates, selection, **rejected plans with reasons**, extra memory, legality blockers. The "not applied, because" line is what keeps the diagnostic honest. |

Cost model must include the **output term** for `join`. If every element shares a
key the result genuinely contains l × m pairs; a model that omits it promises
speedups it cannot deliver.

## Wave 6+ — deferred

PGO (`.sprof` v2 collection records keyed by stable AST identity, never line
numbers), index sharing (Soufflé minimum-cover), composite indexes, range/spatial
plans, bounded equality saturation, AARA deep mode, polyhedral numerics (§8.10 —
numeric kernels route here, **never** to hash form), translation validation.

## Verification per algorithm-changing lane

Non-negotiable for any lane in Wave 4+:

- **Semantic:** empty, singleton, duplicate keys, first-vs-last, all-match output
  ordering, custom equality, hash/equality disagreement **rejection**, mutation
  during traversal, exceptions in key/predicate fns, side effects, nil, text
  normalisation, integer boundaries, deliberate collisions.
- **Cross-engine:** interpreter, JIT, LLVM AOT, self-hosted native, SimpleOS.
- **Differential:** bounded random inputs; compare output, order, side-effect
  trace, error result.
- **Scaling:** n, 2n, 4n, 8n. **Operation counts are primary evidence; wall time
  is supporting only** — shared-host timing is noisy.

## Dependency order

```
Wave 0 (done) ─────────────────────────────────┐
Wave 2 STD-HASH ──┬──────────────────┐         │
Wave 2 STD-UNIQ ──┘                  │         │
Wave 1 P0 (gate) ─────► Wave 3 ─────►┴─ Wave 4 ─► Wave 5 ─► Wave 6+
```

Wave 1 and Wave 2 are independent and start together. Wave 3 needs the Wave 1
gate. Wave 4 needs Wave 3 **and** STD-HASH.

## Risk register

| Risk | Mitigation |
|---|---|
| A rewrite is applied that changes semantics | Confidence gating: only `Certain`/`Safe` auto-apply under `--fix`; `Likely` needs `--fix-all`. Differential execution per rewrite. |
| The planner picks hash where nested is faster | Guarded plans; measured per-target thresholds; never a hardcoded constant. |
| Cost knowledge diverges again | REG1 is the single source; REG2's backend symbol check is the fail-closed gate. `rt_array_map` is the worked example of what divergence costs. |
| Analysis slows compilation | Default mode: one traversal, cached summaries, bounded candidates, no whole-program equality saturation. Deep mode opt-in only. |
| Mirror trees drift | `test/unit/` mirrors `test/01_unit/`; **run both sides before reconciling** — direction is per-spec, never assumed. |
