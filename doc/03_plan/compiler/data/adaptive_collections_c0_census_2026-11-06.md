# Adaptive Collections — C0 Source Census

**Date:** 2026-11-06. **Revision audited:** `origin/release/1.0.0` at `4c7769a0619`.
**Plan:** `adaptive_collections_profiling_switching_2026-09-16.md` (this directory),
package C0. **Companion plan:** `data_attributes_layout_containers_xray_2026-11-06.md`
(sections 7, 8, 14).
**Scope:** docs only. Nothing is enabled or changed by this census.

Every row was checked against source at the revision above. File:line points
at the declaration or decision, not at a comment about it. Status words:

| Status | Meaning |
|---|---|
| Implemented | Real code path, reachable, with a spec |
| AnalysisOnly | Code exists and computes a result, but no compiler or runtime path acts on it |
| Unsupported | No code; the plan's assumption is not present |
| Disabled | Code exists but is switched off or admits nothing |
| Blocked | Needs an owner decision or another lane first |

## 1. Headline: what exists versus what the plan assumed

1. **The adaptive runtime is real, and it switches live.** `AdaptiveMap`,
   `AdaptiveSet`, `AdaptiveTextSet` and `AdaptiveTextMap` choose linear, chained
   hash or AVL storage per instance. They promote and demote while in use, and
   take p95 priors from a profile. This is the existing "C7-lite": exclusive
   owner and in-place promotion. It is not a design proposal.
2. **The site identity is not stable across whitespace.** Both parsers hash the
   *raw declaration bytes* with FNV-1a (`parser_stmts.spl:811-813`,
   `attributes.rs:106-112`). Changing a space inside the declaration changes
   the ID. Comments outside the declaration do not. Profile admission is
   stricter still: `sprof_source_module_identity_from_text`
   (`sprof_collection_profile.spl:47-103`) hashes the *whole module's bytes*,
   except the algorithm string, so any edit anywhere in the module drops all
   feedback for that module. Plan §8.1's stable-origin requirement is
   therefore **Unsupported** today. See §5 for the conflict this causes in C1.
3. **`.sprof` collection records already exist.** The plan (§11.1, [R1]) says v1
   rejects collection records and a v2 is future work. In fact
   `sprof_loader.spl:189-190` accepts `sprof-v2`, and
   `sprof_collection_profile.spl:305` writes `header;schema=sprof-v2` with
   collection sample and metric lines. It is a text envelope with no
   record-kind/version/length framing, and it has no insert, erase or replace
   counters. The shared W5 extension, owned by the other lane, must absorb it,
   not run beside it.
4. **The operation registry admits nothing.**
   `config/compiler/collection_operations.sdn` is `operations: []`.
   `HirPerfOperationKind` (`35.semantics/perf_facts/types.spl:18`) has no
   insert, erase, replace or clear operation. The builtin resolver
   (`perf_facts/builtin_collection.spl:6`) admits only Array `map` and
   `filter`. There are no semantic operation IDs for sets or maps.
5. **Typed plan selection is AnalysisOnly.** `collection_plan_select` lives in
   `35.semantics/perf/collection_plan_selection.spl:114`. The `60.mir_opt`
   file is a two-line re-export. Nothing in the pipeline feeds it. This is
   bug `profile_switchable_typed_plan_unwired_2026-10-01.md`, which is still
   OPEN. There is no `20.hir/perf` directory. The plan's "typed-HIR collector"
   is `35.semantics/perf_facts/collector.spl`.
6. **Unknown local attributes are silently dropped.** In the pure-Simple
   parser, `parse_attributed_nested_decl_stmt` (`parser_stmts.spl:833-863`)
   consumes `@name(...)` before a local and throws it away. Only
   `@collection_algorithm` (`:757`) and `@representation_boundary` are kept.
   So `@col(...)` written today is silently ignored. This is exactly the plan's
   R13 risk.
7. **Set literals.** The AST and HIR already have `SetLit`
   (`parser_types_expr.spl:566`, documented as `s{1, 2, 3}`; HIR lowering at
   `expression_core.spl:897`). **No parser builds one.**
   `set_literal_spec.spl:45-115` has every literal case commented out as a
   TODO. In both parsers `{}` is an empty Dict.
8. **No `col<T>` exists.** There is no `trait Collection` or `col` anywhere in
   `src/lib`.

## 2. Inventory

### 2.1 Containers

| Item | Location | Status | Notes |
|---|---|---|---|
| `AdaptiveMap<K,V>` (struct, value) | `src/lib/nogc_sync_mut/src/collections/adaptive_map.spl:18` | Implemented | Holds three backing stores. `put` returns new-key (`:346`); `remove` returns the old value or nil (`:409`). Promotion is `promote_if_useful` (`:550`). Default thresholds: linear up to 8 entries, promote after 32 lookups (`adaptive_text_set.spl:121`) |
| `AdaptiveSet<K>` | `adaptive_set.spl:12` | Implemented | A wrapper over `AdaptiveMap<K, bool>` |
| `AdaptiveTextSet` / `AdaptiveTextMap` (class, reference) | `adaptive_text_set.spl:163`, `adaptive_text_map.spl:16` | Implemented | Text-key variants. They own the shared enums `AdaptiveSetAlgorithm` and `AdaptiveSetAttribute` (`adaptive_text_set.spl:9,14`) and the global feedback context (`:79`) |
| Generic `Map<K,V>` | `src/lib/nogc_sync_mut/src/map.spl:20` | Implemented | Chained buckets with cached hashes. `insert` returns nothing (`:113`); `rehash` (`:284`) is not visible to capture |
| AVL `OrderedMap<K,V>` | `collections/ordered_map.spl:29` | Implemented | Requires `Ord + Eq`. `put` returns new-key (`:175`) |
| Text `HashMap` / `HashSet` | `collections/hashmap.spl:20`, `hashset.spl:14` | Implemented | Text keys only (class). The parser uses them for site ordinals |
| `Set<T>` | `src/lib/nogc_sync_mut/src/set.spl:17` | Implemented | Linear scan over insertion-ordered `items`; no `Hash` bound |
| Builtin `Dict` (interpreter) | `compiler_rust/compiler/src/value.rs:3091` | Implemented | `Arc<HashMap<String, Value>>`, so keys are stringified |
| Builtin `Dict` (native runtime) | `compiler_rust/runtime/src/value/dict.rs:316-342` | Implemented | Open addressing; `keys` iterates slots in order |

### 2.2 Attributes, identity and parsing

| Item | Location | Status | Notes |
|---|---|---|---|
| `@collection_algorithm("auto"/"linear"/"hash"/"ordered")` on locals, pure-Simple | `parser_stmts.spl:757-822` | Implemented | Rewrites the initializer at parse time to `T.attributed_at_site(...)`. No AST attribute node is kept; the attribute survives only as that call |
| Same, on fields | `_ParserDecls/fn_struct_decls.spl:1084-1309` | Implemented | |
| Same, seed | `compiler_rust/parser/src/parser_impl/items.rs:400,606-640`; `attributes.rs:85,135-140` | Implemented | Rust test pins the field site hash (`parser/tests/collection_algorithm_attribute.rs:45`) |
| Site ID `ast://{module}/{owner}/local/{name}#{fnv(decl bytes)}[:ordinal]` | `collection_feedback.spl:46-69`; seed `attributes.rs:106-131` | Implemented | Hashes bytes, not tokens (§1.2). The ordinal is parse order. No spec checks that seed and pure-Simple produce the same ID |
| Feedback catalog install and validation | `collection_feedback.spl:77-111` | Implemented | Rejects bad p95 shapes and duplicate sites |
| HIR family guard for attributed factories | `20.hir/hir_lowering/_Expressions/expression_core.spl:128-173,640` | Implemented | Only checks wrong family or non-adaptive factory |
| Other local `@name(...)` | `parser_stmts.spl:833-863` | Unsupported (dropped) | §1.6 |
| `@layout(...)` | seed known-name list `attributes.rs:47` | Unsupported on locals | Item-level only |
| Brace literal, seed | `compiler_rust/parser/src/expressions/primary/collections.rs:357-367` | Implemented | `{}` gives `Expr::Dict([])`; non-empty entries require `:` |
| Brace literal, pure-Simple | `core/_ParserPrimary/primary_expr.spl:1050-1060` | Implemented | Same meaning |
| `SetLit` | AST `parser_types_expr.spl:566`, HIR `expression_core.spl:897` | Unsupported (no producer) | §1.7 |

### 2.3 Planning, profile and capture

| Item | Location | Status | Notes |
|---|---|---|---|
| `collection_plan_select` | `35.semantics/perf/collection_plan_selection.spl:114` | AnalysisOnly | No pipeline producer. `60.mir_opt/mir_opt/collection_plan_selection.spl` re-exports it |
| CollectionPlan IR, extractor, loop, explain | `35.semantics/perf/collection_plan*.spl` | AnalysisOnly | Unary Array operations only |
| HIR perf collector | `35.semantics/perf_facts/collector.spl:307` | Implemented (diagnostic) | Finds linear lookups (COLL002, `:333`). Its facts authorize no rewrite |
| Operation registry and SDN loader | `perf_facts/types.spl:89`, `registry.spl:11`, `registry_schema.spl:5` | Disabled | Snapshot is empty (§1.4) |
| `optimizer_plugin.spl` descriptors | `60.mir_opt/optimizer_plugin.spl:79` | Implemented (registry) | **No collection descriptor is registered** |
| Capture ABI | `nogc_sync_mut/sffi/collection_capture.spl:7-31`; C `src/runtime/runtime_collection_capture_impl.h` | Implemented | Records size, lookup hit/miss, materialization, hash probe, filter and loop. **No insert, erase, replace or maintenance events.** It uses a spinlock (`:60-69`) and keys records by site text, with at most 14,285 sites (`:13`) |
| `.sprof` v2 collection records | `app/optimize/sprof_collection_profile.spl:294-416`; loader `sprof_loader.spl:189` | Implemented | Text lines, p95 merge (§1.3) |
| Capture run and native build with profile | `app/io/collection_profile_run.spl`, `app/io/_CliCompile/native_collection_profile.spl:39` | Implemented | |
| `simple optimize --explain-collection-plan` | `app/optimize/collection_plan_cli.spl` | AnalysisOnly | Reports `guard.typed_mir=unconnected` |
| `StorageLayoutPlanV1` / `StorageLayoutKind` | `common/structural/storage_layout/storage_layout_contracts.spl:8,53` | Implemented (contract) | Frozen V1 |
| `storage_layout_plan_auto` | `storage_layout/planner.spl:40` | AnalysisOnly | No caller outside its own module. It can return Grouped, which the layout owner lists as incomplete (`feature_expert/storage_layout/skill.md:37`) |

## 3. Semantic contract matrix

"Order" is what iteration exposes to programs. "Eq/hash" is the key contract
the implementation actually calls.

| Family / type | Order | Eq / hash used | Duplicates | Mutation result contract | Iteration guarantee |
|---|---|---|---|---|---|
| Map: `AdaptiveMap` | Sorted by key while every key has native order. Otherwise insertion order, kept in `fallback_order_entries` (`adaptive_map.spl:206-260`) | `Hash + Eq + Ord`; Ord must agree with Eq | No | `put` → new-key bool; `remove` → previous `V?` | The same order whichever backing store is active. Iteration materializes a snapshot |
| Set: `AdaptiveSet`, `AdaptiveTextSet` | Same as `AdaptiveMap` / sorted text | Same / text | No | `insert` and `remove` → bool (changed) | Snapshot |
| Map: `AdaptiveTextMap` | Sorted text | Text | No | `put` → bool; `remove` → `text?` | Snapshot |
| Map: generic `Map` | Bucket order (unspecified) | `Hash + Eq`, cached hash | No | `insert` → unit; `remove` → `Option<V>`; `insert_if_absent` → bool | Unspecified; changes after `rehash` |
| Map: `OrderedMap` | Sorted by key | `Ord + Eq` | No | `put` → new-key bool | Sorted |
| Map: builtin `Dict` | **Depends on backend.** Interpreter `keys()` sorts by stringified key (`value_impl.rs:34-37`, `collections.rs:1518`); native `rt_dict_keys` uses slot order (`dict.rs:316-342`) | Interpreter: string form of the key. Native: runtime hash | No | Index assignment replaces | **No portable guarantee**; this is a parity gap |
| Map: text `HashMap` | Slot order | Text | No | `insert_if_absent` → bool | Unspecified |
| Set: `Set<T>` | Insertion order | `==` only, linear | No | | Insertion order |
| Sequence: `[T]` | Index order | n/a | Yes | | Index order |

Consequences for C1: semantic operation IDs must be attached per *resolved
type*, not per spelling. For example, `put` on `AdaptiveMap`, `insert` on
`Map` and `d[k] = v` on `Dict` are one logical operation, Insert-or-Replace,
but each reports its outcome differently or not at all. Whether a call
replaced a value or added a key is visible directly only from `AdaptiveMap`,
`OrderedMap` and `Map.insert_if_absent`. For `Map.insert` and `Dict` it has to
be derived from a prior membership check, or recorded by the instrumented
container.

## 4. Supported, blocked and missing routes

| Route | Status |
|---|---|
| Source attribute → adaptive constructor with a p95 prior → live promotion | Implemented |
| Capture run → `.sprof-v2` collection lines → feedback on the next build | Implemented (whole-module byte identity) |
| Typed plan → MIR lowering of a selected algorithm | Blocked (bug `profile_switchable_typed_plan_unwired_2026-10-01.md`) |
| SDN collection policy | Unsupported; waits for the shared W1 resolver (other lane, PR-B) |
| Insert, erase, replace and maintenance accounting | Unsupported, in both the capture ABI and `.sprof` |
| Set literals and contextual `{}` | Unsupported; owner language decision |
| Layout auto-plan → typed storage | AnalysisOnly; existing typed-storage gates apply |
| `col<T>` capability | Unsupported; owner naming decision |

## 5. Decisions C1 must take explicitly

- **Site ID formula.** A token-normalized fingerprint makes IDs stable across
  whitespace and comment edits. But changing the existing `ast://…#hash` byte
  formula would invalidate every recorded `.sprof` collection site. It would
  also have to change in the seed and pure-Simple parsers in the same commit.
  The lower-risk route keeps `site_id` as the legacy key. It adds a
  token-normalized origin fingerprint beside it, used for remapping, and
  rejects a remap when more than one candidate matches.
- **Owner of the operation-ID table.** `35.semantics/perf_facts` already owns
  `CollectionOperationSummary` and the registry, so the new contract and origin
  records belong there. They do not belong in a new directory.
- **Capture lock.** `runtime_collection_capture_impl.h:60-69` uses a spinlock.
  Under the lockless rule it needs a documented exception, or a per-thread
  block design, before C4 widens it.

## 6. Execution baseline on the Rust seed

Measured 2026-11-06 with the bootstrap seed (`ed2caded61e`, sha256 prefix
`4e0cc95b1ee42268`; interpreter mode; one spec at a time under
`systemd-run -p MemoryMax=16G`). No self-hosted `bin/simple` was deployed on
this host.

| Spec | Result | Cause |
|---|---|---|
| 8 `adaptive_*` lib specs (`test/01_unit/lib/**/adaptive_*_spec.spl`) | 14 of 67 pass | The seed interpreter has no extern backing for `spl_collection_capture_*` (46 hits) or `spl_ordered_key_cmp` (7 hits). They exist only in `compiler_rust/runtime` and `codegen/runtime_sffi.rs`, so on the seed the adaptive containers fail as soon as any capture-aware path is reached |
| `collection_algorithm_attribute_spec` | 32 of 33 | "keeps local feedback attached after unrelated text is inserted before its declaration": array index out of bounds |
| `perf_facts_spec` | 23 of 25 | Two DCE Skeleton expectations (`expected 1 to equal 0`) |
| `collection_feedback_state_take_install_spec`, `collection_plan_selection_spec`, `hir_perf_facts_spec` | All pass | |

So the adaptive *runtime* claims in §2.1 are source-verified but **not
executed** on this host. Executing them needs either interpreter extern
backing for the capture and ordered-key SFFI, or a deployed self-hosted
binary. C1 specs must exercise contract functions that do not cross those
externs.
