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
