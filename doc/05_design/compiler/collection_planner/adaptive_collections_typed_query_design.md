# Adaptive collections + typed queries — design contracts

**Date:** 2026-09-18
**Status:** design — proposed contracts; none implemented. RC1 implements only
the records marked **RC1** below.
**Research:** `doc/01_research/compiler/collection_planner/adaptive_collections_typed_query_2026-09-18.md`
**Plan:** `doc/03_plan/compiler/collection_planner/adaptive_collections_typed_query_rc1_plan_2026-09-18.md`
**Base IR:** `doc/01_research/compiler/collection_planner/collection_plan_ir_2026-07-31.md` §4

All names are proposals. Paths marked *(new)* do not exist on `origin/main`
`c3927751dc1`; run a collision census before creating one.

## 1. Ownership map

| Contract | Owner path | Layer | RC1 |
|---|---|---|---|
| `CollectionSemanticContractV1` | `src/lib/common/collections/semantic_contract.spl` *(new)* | common, pure | **RC1** |
| `CollectionOriginV1`, `CollectionOperationId` | `src/compiler/20.hir/` beside typed-HIR collectors *(new file)* | compiler | **RC1** |
| Operation registry | `config/compiler/collection_operations.sdn` *(new)* — shared by lint + MIR opt | config | **RC1** |
| `ProfileSessionV2` DTO/codec/query | `src/lib/common/profile/` *(new)*; app I/O stays in `src/app/optimize/` | common + app adapter | **RC1** |
| Collection counters (`basic`) | `src/app/compile/native_profile_counter_runtime.spl` (extend) | app/runtime | **RC1** |
| Report-only planner + explain | `src/compiler/60.mir_opt/mir_opt/collection_opt*.spl` (extend; this is the existing owner) | compiler | **RC1** |
| COLL complexity rules | `src/compiler/35.semantics/lint/collection_patterns.spl` (extend) | compiler | **RC1** |
| `ResolvedCollectionPolicyV1` + SDN loader | `src/compiler/*/collection_policy/` *(new)* | compiler | post-RC1 |
| `QueryExpr`, `ImplicitFieldRef` | frontend + `20.hir` | compiler | post-RC1 |
| `PhysicalCollectionPlanV1` | collection_opt owner | compiler | post-RC1 |
| `StorageLayoutPlanV1` | `src/lib/common/structural/storage_layout/` — **unchanged** | common | reuse only |
| `CollectionTransitionReceiptV1` | runtime | runtime | post-RC1 |
| Pass activation | `60.mir_opt/optimizer_plugin.spl` | compiler | reuse |

Dependency direction: `common` ← `compiler` ← `app`. Compiler core never imports
`app.optimize`; the JIT bridge (`95.interp/execution/sprof_hotspot_bridge.spl`)
keeps primitive inputs and gains a typed query over `ProfileSessionV2` views.

## 2. Semantic contract (RC1)

```simple
enum CollectionFamily:
    Sequence
    Set
    Map

struct CollectionSemanticContractV1:
    family: CollectionFamily
    ordered: bool                 # iteration order observable and promised
    duplicates: bool              # Sequence only
    key_eq_hash_pure: bool        # false => planner may not add hash/eq calls
    mutability: i64               # bitmask: elements | keys | length
    stable_refs: bool             # outstanding refs/iterators survive growth
    lookup_bound: i64             # 0 none, 1 expected O(1), 2 O(log n)
```

A physical choice is admitted only if it satisfies every field. A profile can
never change a contract field.

## 3. Identity (RC1)

```simple
struct CollectionOriginV1:
    module_revision: text         # existing semantic module identity
    ast_origin: i64               # stable AST origin, not line/column
    creation_kind: i64            # literal | ctor | factory | field-default
    type_fingerprint: text        # canonical, cross-module stable
    site_label: text              # from @col_site, "" if none (post-RC1)
    inline_parent: i64            # -1 if not inlined

struct CollectionOperationId:
    origin: CollectionOriginV1
    op: i64                       # registry id: resolved semantic op, not spelling
    op_site: i64
```

Remap across edits only via a sidecar with source fingerprint; ambiguous remap
is rejected, not guessed. Implementation events (probe, resize, rehash,
reinsert) carry a separate `maintenance` op class.

## 4. Operation registry (RC1)

One SDN file, read by the lint rule set and the MIR optimiser (07-31 §5 —
closes the "three registries" risk):

```sdn
schema: "simple.collection-operations.v1"
operations:
    map_get:        { family: "map", class: "lookup",  expected: "O(1)", worst: "O(n)" }
    map_set:        { family: "map", class: "insert",  expected: "O(1)", amortized: true }
    seq_contains:   { family: "sequence", class: "lookup", expected: "O(n)" }
    seq_push:       { family: "sequence", class: "insert", amortized: true }
```

Expected / amortized / worst stay separate columns.

## 5. Profile session v2 (RC1)

```text
ProfileSessionV2
  schema_major=2 / schema_minor
  run_id, subject_kind (compiler | program), subject_build_id
  workload_id, workload_weight, target_fingerprint
  instrumentation_manifest_digest, policy_digest, plan_digest
  sampling_description, completeness, dropped_records
  records[]: { kind, version, length, required, payload }
```

RC1 record kinds: `FunctionCounter`, `BlockCounter`, `EdgeCounter` (v1
compatible), `CollectionSummaryV1`. Others (`RegionTiming`, `CpuSample`,
`Allocation`, `CowCopy`, `CollectionSizeHistogram`, `CollectionPhaseWindow`,
`CollectionFieldSummary`, `QuerySite`, `DeviceExecution`,
`CollectionTransition`) reserve kind numbers only.

```text
CollectionSummaryV1
  origin, type_fingerprint, family
  instances_observed, live_censored
  lookup_hit, lookup_miss
  insert_attempt, insert_new_key
  erase_attempt, erase_existing_key
  replace_value, scan_start, scan_elements
  indexed_read, indexed_write
  max_len_observed            # observed, never a proven bound
  exactness, saturation, missing_mask
```

Codec rules: unknown required → reject; unknown optional → skip; v1 file →
read unchanged; `export --v1` writes only function/block/edge. Merge dedups on
`(run_id, shard, sequence)`, saturates, keeps `missing_mask` (missing ≠ 0).
Input bounds on length, count, UTF-8 and total bytes.

## 6. Instrumentation (RC1: `off` and `basic` only)

- `off`: no probe, no TLS init, no header field, no recorder dependency in the
  program. Proof = symbol/IR scan of a built binary, not a flag read.
- `basic`: each instrumented op site compiles to a numeric slot in a
  per-thread counter block reached via cached pointer; `+1` with saturation; no
  clock, no text key, no lock on the hot path. Blocks registered on a cold
  first-touch path; merged at thread exit / flush. Recorder uses its own arena
  and never instruments itself.

`sampled`, `deep`, `adaptive-runtime` are post-RC1.

## 7. Report-only planner (RC1)

Input: CollectionPlan + registry + optional `ProfileSessionV2`. Output: a
`CollectionPlanReport`, **no IR mutation**.

```text
CollectionPlanReport
  site, family, contract
  symbolic_cost { expected, worst }        # from registry
  observed { op mix, max_len, hit ratio } | "no profile"
  candidates[] { name, admitted: bool, reason }
  recommendation | "keep"
  status: AnalysisOnly
```

Surfaced as `remark[COLL-PLAN]` and `simple optimize --collection-explain=<site>`
(proposed flag). Status is always `AnalysisOnly` in RC1; wording never says a
transform ran.

## 8. Post-RC1 contracts (fixed now so RC1 records stay compatible)

```text
ResolvedCollectionPolicyV1
  semantic_contract_ref, hard_constraints, allowed_representations,
  workload_hints, objective, budgets, switch_policy, layout_policy_ref,
  named_policy_deps, per_field_provenance, canonical_digest

QueryExpr (hash-consed, numeric ids)
  Field(FieldId) | FieldPath([FieldId]) | Literal | Parameter
  | Add..Mod | Eq..Ge | And/Or/Not | IsNil | Coalesce | Cast
  | Intrinsic(id) | PureCall(fn) | OpaqueCall(fn)          # OpaqueCall = barrier
  facts: type, nullable, effects, deterministic, may_throw, cost,
         vectorizable, gpu_legal, referenced_fields

PhysicalCollectionPlanV1
  semantic_contract_digest, primary_storage, indexes[],
  storage_layout_plan: StorageLayoutPlanV1 (by value, unchanged V1),
  residency, dispatch, admitted_transitions[], evidence_refs,
  steady_mem, peak_mem, costs, confidence, fallback_ref, digest

CollectionTransitionReceiptV1
  origin, from_generation, to_generation, from_plan, to_plan,
  ownership_proof_ref, peak_bytes, outcome (published | rolled_back)
```

Rules fixed now: `.field` resolves to `FieldId` before HIR→MIR; `{}` stays
Dict; hard constraints intersect, soft hints use research §3 precedence;
migrations are exclusive/quiescent first; `StorageLayoutPlanV1` extended only
through a versioned wrapper.

## 9. Verification matrix (one for all phases)

| Group | RC1 cases |
|---|---|
| Contract | every registry op maps to exactly one family; contract fields round-trip |
| Identity | same origin across whitespace/comment edits; distinct origins for two literals on one line; ambiguous remap rejected |
| Profile codec | v1 fixtures read byte-identical; v2 round-trip; unknown-required reject; unknown-optional skip; duplicate import not double-counted; saturation; truncated/oversized input rejected |
| Accounting oracle | duplicate insert, failed erase, value replace, early-exit scan, resize reinsert counted as maintenance |
| Off-mode | built binary has no collection-probe symbol/TLS reference |
| Planner | report is deterministic; no IR diff with report enabled vs disabled; status `AnalysisOnly` |
| Complexity fixes | `group_by`, `unique_f64`, `unique_i64`: same output order as before + scaling test 1K→16K shows ~linear growth |
| Lexer corpus | `t.0`, `n.0.1`, `0.5`, `1..2`, `1..=2`, `1...` unchanged (tests only; `.field` not accepted yet) |

Post-RC1 groups (literal/attribute parity, policy DAG, switching fault
injection, layout oracle, device fences, JIT deopt) follow research §5 and are
out of scope here.

## 10. Goal extension (2026-09-18): typed frame API, profiler, lint + auto-fix

Scope decision: in RC1 "the dataframe way" means a **typed library API over
`[Record]`**, reached through key lambdas. The `.field` / `{a, b}` grammar stays
post-RC1 (P1/P3) because it needs seed-Rust, self-hosted and GPU-lexer parity.
The lint names the library call to switch to. That is the fast path the user
asked for.

### 10.1 `std.common.frame` — `src/lib/common/frame.spl` *(new)*


The module lives in the `common` family: pure code, no I/O, importable from
every family. Compiler, loader and interpreter code mostly import
`std.common.*` / `std.nogc_sync_mut.*`. The code uses only the Dict subset shown
safe in `gc_async_mut/pure/collections.spl:55-68`: `d[k] = v` and `contains_key`.
It never calls `.set()` (which silently drops inserts under native codegen) and
never calls `.get()`. Dicts are always **locals**, never class fields: a
class-field Dict bracket-read of an array value SEGVs natively
(`dict_native_pitfalls.md`).

| Function | Semantics | Cost |
|---|---|---|
| `key_set<T,K>(xs: [T], key: fn(T) -> K) -> Dict<K, bool>` | membership index | O(n) expected |
| `index_by<T,K>(xs: [T], key: fn(T) -> K) -> Dict<K, i64>` | key → **first** row position. **Caller contract:** call `contains_key(k)` before `d[k]`, because a missed `d[k]` returns `0` silently, which is indistinguishable from row 0 | O(n) |
| `distinct_by<T,K>(xs: [T], key: fn(T) -> K) -> [T]` | first occurrence per key, input order | O(n) |
| `group_by_key<T,K>(xs: [T], key: fn(T) -> K) -> [(K, [T])]` | first-encounter group order, members in input order. **Implementation idiom required:** `Dict<K, i64>` key→slot plus parallel `keys: [K]` / `members: [[T]]`, zipped at the end. `groups[j].1.push(x)` mutates a discarded tuple copy and drops members (`pure/collections.spl:72-76`) | O(n) |
| `count_by<T,K>(xs: [T], key: fn(T) -> K) -> [(K, i64)]` | first-encounter order, same slot idiom | O(n) |
| `semi_join<L,R,K>(l: [L], r: [R], lk: fn(L) -> K, rk: fn(R) -> K) -> [L]` | rows of `l` with a match, in `l` order, duplicates kept | O(l + r) |
| `anti_join<L,R,K>(l: [L], r: [R], lk: fn(L) -> K, rk: fn(R) -> K) -> [L]` | rows of `l` with no match | O(l + r) |
| `top_k_by<T>(xs: [T], k: i64, score: fn(T) -> i64) -> [T]` | k highest scores, **output in descending score**, ties keep input order. `k <= 0` → `[]`; `k >= len` → all rows, sorted the same way | O(n·k) using a sorted k-buffer, never a full sort |

`group_by_key` is the canonical O(n) grouping. L12 also re-points
`gc_async_mut/pure/collections.spl` `group_by` at it, so the pure `group_by`
becomes O(n) with identical output. That is why the old L1 is folded into L12.

Order and duplicate behaviour are part of the contract, so every function has
an order-preservation spec. Every function also has a 1K→16K scaling spec.

**Closure caveat (G-P0):** lambdas are fine in library code and in interpreted
code. Compiler, loader and interpreter sources that bootstrap compiles
natively must use the **inline Dict-index form** instead: a local
`Dict<K, bool>` or `Dict<K, i64>` built before the loop, not a lambda helper.
This holds until the closure/indirect-call ABI gate is green. Lint messages
always show both forms.

### 10.2 Collection profiler — `src/lib/common/collection_profile.spl` *(new)*

This is opt-in and explicit: nothing is instrumented automatically in RC1
(`off` = the module is not imported). It uses numeric site slots. The hot path
has no text keys, no clock and no allocation.

```simple
struct CollectionSiteStats:
    name: text
    lookups: i64          # membership/find calls
    lookup_hits: i64
    scanned: i64          # elements visited by linear lookups/scans
    inserts: i64
    max_len: i64

# profiler state: stats: [CollectionSiteStats]
fn coll_site(p, name: text) -> i64                  # cold, once per site
fn coll_on_lookup(p, site: i64, hit: bool, scanned: i64, len: i64)
fn coll_on_insert(p, site: i64, len: i64)
fn coll_report(p) -> [text]                         # one row per site
fn coll_advice(p) -> [text]                         # switch recommendations
```

`coll_advice` rules match the lint vocabulary. Linear lookups with
`scanned / lookups > 32` and `lookups > 64` produce `use key_set/index_by`. A
site whose `inserts` stay near 0 after build produces `build once, then index`.
Advice text always names the evidence counts. It is cost evidence, never proof.
`CollectionSummaryV1` (§5) serialises these counters; that is L6 follow-up.

### 10.3 Lint rules + auto-fix (extends `collection_patterns.spl`)

COLL009–018 are **reserved** with fixed meanings (07-31 research §7 table,
`src/app/cli/query_lint.spl:39-40`). COLL010 is lambda-only and already has a
message contract (`test/01_unit/compiler/lint/perf_diagnostic_record_spec.spl:85`).
This lane uses the reserved codes with their reserved meanings and adds
**COLL020–022** for the new patterns. It updates the header comment in
`collection_patterns.spl` and the list in `query_lint.spl`.

| Code | Pattern | Message names | Auto-fix |
|---|---|---|---|
| COLL002 (upgrade) | `arr.contains(x)` in a loop, `arr` loop-invariant | `key_set` / inline `Dict<T,bool>` | yes, only if **all** preconditions hold (below) |
| COLL015 accidental_cartesian_product | nested `for a in A: for b in B:` with an `==` between an `a`-expression and a `b`-expression | `semi_join` / `index_by` | no, suggestion only |
| COLL016 missing_index | `.find`/`.filter`/linear scan whose predicate compares to the outer loop variable | `index_by` / `group_by_key` | no |
| COLL020 manual_distinct *(new)* | growing `seen`/result array, `.contains` guard, `.push` | `distinct_by` / `unique` | yes, only if the loop body is exactly guard + push of the same value and the result array is a fresh local `[]` |
| COLL021 manual_group *(new)* | scan a `keys` array for a slot index, then push into a parallel bucket | `group_by_key` | no |
| COLL022 sort_then_take *(new)* | `.sort…()` then `take(k)` / `[0:k]` | `top_k_by` (descending sort only; ascending + take = k-smallest, so negate the score) | no: tie order vs a stable sort is not proven |

**COLL002 fix preconditions.** Otherwise the diagnostic stays hint-only.
`is_contains_call` has no receiver type, and a `text` receiver is a substring
search.

1. `arr` is declared in the same file on a file-unique line, with an explicit
   `[T]` annotation or an array-literal initializer (which gives `T`; never
   `text`).
2. `arr` is not assigned, pushed or removed inside the loop body.
3. The `.contains(` line is file-unique.
4. The enclosing `for`/`while` line is found by an upward text scan with
   decreasing indentation, the same approach COLL001 uses
   (`entry_and_fixes.spl:413-450`).

The fix is two Replacements. Replacements support multiple spans, with
insertion as `start == end` (`easy_fix/types.spl:29-45`). The first inserts
`var <arr>_set: Dict<T, bool> = {}` and `for _v in <arr>: <arr>_set[_v] = true`
before the loop, at loop indentation. The second rewrites the call to
`<arr>_set.contains_key(x)`.

**Confidence policy.** Commit `7ab671e7813` removed `Certain` COLL fixes from
the AST-fallback path because it had no location proof, so COLL findings became
hint-only. This lane re-enables `Certain` **only** for COLL002 and COLL020, and
only when every textual precondition above is verified. The justification is
that each precondition is exactly the location proof whose absence motivated
that removal. Every other rule stays hint-only. The 2 failing examples in
`collection_easy_fix_spec.spl` encode that hint-only policy. Update them to the
new rule-by-rule policy and add a precondition-negative case for each fix
(for example a `text` receiver, or an array mutated in the loop). Such a case
must yield no fix.

Message form: `COLLnnn: <pattern> is O(n*m); switch to <call> (std.common.frame)
— dataframe-able. Inline form: <Dict snippet>`.
