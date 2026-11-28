# Aspect weaving through TLDR: async match and weave queries, trace, invalidation

**Date:** 2026-11-28. **Base:** `origin/release/1.0.0` @ `3d3a74d786c` (census taken at `df04c6a4e7d`).
**Status:** design, nothing here is implemented. Addendum to
`pseudo_immutable_cache_async_build_design.md` (engine, R01-R15) and to
`doc/03_plan/compiler/cache/generic_aop_macro_semantic_cache_plan_2026-10-24.md` §5.
**Sibling (landed, #12309):** `generic_instance_tldr_trace.md` (generic instances on the
same engine); this document uses the same scheduler, slot table, reverse-reference
machinery and coverage gate, and adds none of its own.
**Plan:** `doc/03_plan/compiler/aspect_cache/aspect_tldr_async_trace_plan.md`.
**TLDR:** `aspect_tldr_async_trace_tldr.md`.

Marks: **[OBS]** = read in `src` (file:line given); **[PROP]** = proposed.

## 1. Model in one paragraph

There is no weave pass. Pointcut matching and weaving are queries in the one
engine: each is a single-flight, set-once slot keyed by content, produced by a
task in the same scheduler as `CompileTask(file)`, and consumed by awaiting its
handle. A file's compile task learns which advice applies to it from
TLDR-carried aspect declarations (aggregated up the directory tree) and its own
join-point rows, never from another file's HIR or a process-global registry. It
weaves from an immutable base body and a deterministic ordered plan, as a stage
of its own src -> obj pipeline. Every former whole-program check becomes an
output check of the task that produced the value.

## 2. Census: landed versus planned (verified in code)

### 2.1 Landed and on a production path

| Piece | Where | Note |
|---|---|---|
| Selector AST, directory facts, match shard, apply key, old/new delta (pure) | `00.common/cache_contract/aspect_match_shard_v1.spl:33-102, 321, 362, 372, 427, 435` | 13 spec files reference it |
| Forward (HIR) weave driven by shards | `80.driver/cache/aop_match_cache_driver_v1.spl:268-331`, called at `80.driver/driver_hir_pipeline_support.spl:684` | visits only modules that own a matched id; falls back to every module on any incompleteness |
| Directory source snapshots (facts captured from HIR + frozen sources) | `80.driver/cache/directory_tldr_snapshot_capture_v2.spl:36`, used from `driver_hir_pipeline_lowering.spl:4` | compile-local, not persisted |
| Guard evaluation for facts | `80.driver/cache/aop_guard_eval_v1.spl:28,48` | **0 spec files** |
| Aspect declaration draft / semantic capture (signature and effects digests) | `80.driver/cache/directory_aspect_capture_v2.spl:12`, `directory_aspect_semantic_v2.spl:35,118`; DTOs `cache_contract/directory_aspect_{draft,projection}_v2.spl` | two families: `"mir"` (`on pc{...}` advice, `capture_v2.spl:23`) and `"logical"` (`@advice`, `:30`); "draft facets, not final authority" |
| Inline join-point table in `__init__.tld` | `cache_contract/directory_join_point_table_v3.spl:66,85`, wired at `package_init_tld_v1.spl:145,183`; fields `parent_scope_digest`, `aspect_root_digest` at `:22,:25` | codec only |
| Selector plan cache (bounded 256, FIFO) | `aop_match_cache_driver_v1.spl:59-66, 114` | |
| Query kinds `aop.directory_facts`, `aop.match`, `aop.weave`; family `aop-consumer` | `semantic_query_read_manifest_v1.spl:208`, `reverse_reference_projection_v2.spl:79`, `reverse_reference_key.spl:46`, `reverse_reference_receipt.spl:40,57` | names admitted |
| Call-only weave proof | `test/00_formal_verification/compiler/aop_call_only_weave_contract_spec.spl`, `src/verification/build_cache/src/WeaveCallOnlyV1.lean` | the weave inserts one `Call` to the advice name and never reads the advice body |

### 2.2 Gaps

| # | Gap | Evidence |
|---|---|---|
| G1 | **Weaving is two whole-program passes behind a barrier.** HIR (logical family): after all modules are lowered and validated. MIR (mir family plus ambient log rules from `aspect_params`): `weave_aop` loops over every MIR module with its own matcher (`weave_function`), no shard cache. | `driver_hir_pipeline_support.spl:678-685`; `driver_aot_pipeline.spl:275-280`; `driver_pipeline_aop.spl:47-145` (log rules `:71-91`) |
| G2 | **Nothing is async.** The single-flight use is join, compute, complete, forget in one synchronous call. The directory gate says the same of itself. | `aop_match_cache_driver_v1.spl:198-212`; `directory_tldr_cache_gate_v2.spl:1-5` |
| G3 | **Engine steps this needs are absent** (0 hits in `src/compiler/**.spl` and `src/lib/**.spl`): `parse_async`, `lower_hir_async`, `lower_mir_async`, `emit_object_async`, `read_tldr_async`, `trait CompileInvoker`, key record v2, write-once slot type, `.sphb`/`.spmb`, usage ledger. Present: `FiberSchedV1` (`src/lib/common/task_runner/fiber_scheduler.spl:45-271`), `TldrTableV1.request_async` (`80.driver/cache/reader/tldr_table_v1.spl:88`), `CacheSingleFlightV1` (`cache/daemon/cache_single_flight_v1.spl:27`). | `git grep`; same finding as engine plan §5 |
| G4 | **Advice is discovered from process-global state and a source text scan, not from TLDR.** | `10.frontend/aspect_registry.spl:50-56, 80-85`; `80.driver/driver_worker_surface_closure_v1.spl:390-395`; `driver_advice_scan_v1.spl:30` |
| G5 | **Match state is process-global, in memory only, unbounded.** One module-level `var`; shards are never written to disk; every insert copies the whole `Dict`. The in-process key is a local xxh3 handle, not a persistable identity. | `aop_match_cache_driver_v1.spl:337`; `aspect_match_shard_v1.spl:84-86, 115-124, 362-364, 414-417` |
| G6 | **Old ∪ new invalidation is spec-only.** The planner's only production caller passes an empty pointcut list; `PointcutDirChangeV1` has no constructor call in `src`. | `incremental_rebuild_plan_v1.spl:26-32, 86-108`; `driver_build/native_file_worker_incremental_io_v1.spl:126` |
| G7 | **No production caller:** `advice_apply_key_v1`, `aspect_weave_from_base_v1` / `aspect_weave_base_record_v1`, `aspect_match_forward_reads_v1`, `pointcut_match_universe_v1`, `aop_reverse_index_build`, `85.mdsoc/aop_cache/aop_group_manifest.spl`. | `aspect_match_shard_v1.spl:427, 468, 505`; `35.semantics/aspect_weave.spl:178, 190`; `85.mdsoc/aop_index/reverse_index.spl:104` |
| G8 | **Production weave mutates the module in place** and relies on a scan for an existing call to stay idempotent. | `35.semantics/aspect_weave.spl:70-87, 202-226`; `aop_match_cache_driver_v1.spl:325-328` |
| G9 | **Directory TLDR store, gate and producer are unwired** (0 `src` importers outside themselves). | `80.driver/cache/directory_tldr_{cache_gate,producer,store}_v2.spl`; `directory_tldr_native_qualification_2026-11-14.md` |
| G10 | **No `aop-consumer` rows from a real weave.** `reverse_reference_register_aop_v1` has one caller, the wrapper in `reverse_index.spl:24`, reached only from the uncalled `aop_reverse_index_build`; `incremental.spl:1045-1116` only projects whatever the registry holds. | `reverse_reference_facts.spl:424-427` |
| G11 | **Three selector identities coexist:** `pointcut_selector_parse_v1` (logical shards), `aop_predicate_canonical_text` (mir-family predicates), `aop_selector_digest` (mdsoc index, substring read-set). | `aspect_match_shard_v1.spl:321`; `10.frontend/core/aop_predicate_parser.spl:43`; `85.mdsoc/aop_cache/aop_group_keys.spl:65`; `reverse_index.spl:9-13` |
| G12 | **No trace surface.** `TraceViewProjection` has 0 source files; `TraceRelation` has no advice edge. | `src/lib/common/traceability/model.spl:267-284` |
| G13 | **Conflict detection and weave accounting are global.** | `driver_pipeline_aop.spl:103`; `50.mir/mir_aop_injection.spl:21-31` |
| G14 | Shard matching covers `forward` join points only (`_selector_matches` returns false for any other kind) and only static `before`/`after` is cacheable. Kept (decision D2). | `aspect_match_shard_v1.spl:358-360, 422`; `35.semantics/aspect_weave.spl:8-16` |
| G15 | **Join-point facts are too thin for a weave key.** `JoinPointFactV1` has no signature digest and no guard ids, and production sets `base_body_digest: ""`. | `aspect_match_shard_v1.spl:33-39`; `aop_match_cache_driver_v1.spl:173-176` |

## 3. Facts carried by TLDR

Two sections on a module's TLDR, written by that module's own compile task [PROP]:

| Section | Row | Written at | Existing DTO it reuses |
|---|---|---|---|
| `aspect-decl\|` | family (`logical` / `mir`), `AdviceId`, form, mode, `ActivationMode`, canonical selector text + `PointcutSelectorId`, `PointcutScopeId`, order/priority, `@readonly/@noalloc/@bounded_time` | parse stage | `DirectoryAspectDeclarationV2` |
| `aspect-decl\|` set-once slot | `AdviceSignatureEffect` = signature digest + effects digest | typed-HIR stage | `DirectoryAspectHandlerV2` |
| `aspect-decl\|` facet `advice.body` | `AdviceBodyDigest` | typed-HIR stage | new facet; never read by matching |
| `join-point\|` | `JoinPointFactV2` [PROP, stage AW-2]: the v1 fields plus `signature_digest`, `guard_ids` and a real `base_body_digest` (G15); includes non-exported functions | typed-HIR stage | extends `JoinPointFactV1` |

Handlers are zero-parameter, `Unit`-returning, non-generic, non-async functions
[OBS `directory_aspect_semantic_v2.spl:86-91`], so no argument-type layout input
exists for an advice call until handlers gain parameters.

Aggregation uses the fields `__init__.tld` already has [OBS
`package_init_tld_v1.spl:22-38`]. `aspect_root_digest` is a codec field with no
producer today, and `directory_tldr_roots_v2_2026-11-14.md` records that aspect
catalog roots "are currently broader than a directory and require scoped
aggregation". This design supplies that aggregation [PROP]: the per-module leaf
is the landed `DirectoryAspectSemanticV2.interface_digest` [OBS
`directory_aspect_semantic_v2.spl:100-113`: declaration rows + signature +
effects, **no body**]; a directory's root is the digest over its members' sorted
leaves and its children's roots. An advice body edit does not move any aspect
root. `parent_scope_digest` chains upward; the inline join-point table is the
directory's `DirectoryJoinPointFactsV1`.

**Selector identity.** `PointcutSelectorId` is the digest produced by
`pointcut_selector_parse_v1`. AW-3 retires exactly one identity,
`aop_selector_digest` with its substring read-set. `aop_predicate_canonical_text`
stays as the front parser of mir-family predicates; its text is lowered into
`PointcutSelectorV1` when every atom is expressible, and is otherwise
`supported = false`: evaluated by the file's own task, never cached.

## 4. Queries

All slots live in the engine's one single-flight table; kinds are the admitted
`aop.*` names.

```text
advice_index(scope)                      # kind aop.directory_facts (decl half)
  = merge(own aspect-decl rows, for child in children: await advice_index(child))
  key = aspect_root_digest(scope)         # Merkle; unchanged subtree = one hit

effective_advice(dir)                    # what can apply inside dir
  = filter(await advice_index(domain root), scope admits dir)   # sorted by (order, AdviceId)

weave_plan(file)                         # set-once slot on the file's task
  advice = await effective_advice(dir(file))
  logical family: for each own JoinPointFactV2 row, the ordered advice whose
                  selector matches that row (pure evaluation, no further await)
  mir family + ambient log rules: the ordered rule set that applies to this file
  plan_digest(file) = H(sorted join_point_weave_keys, mir_rule_set_digest, log_config_digest)

match(selector, dir)                     # kind aop.match -> PointcutMatchShardV1
  = selector over join_point_facts(dir)   # for trace, planner and daemon reuse only
  identity = pointcut_match_identity_v1(selector, facts)   # sha256, persisted
```

**Stage order of `CompileTask(file)`** (explicit, so no await can cycle):

```text
1 parse            publishes aspect-decl| draft rows
2 typed HIR        publishes the signature/effects slot and join-point| rows; base HIR is immutable
3 await effective_advice(dir(file))        # first and only aspect await
4 weave_plan(file) pure, over the file's own rows
5 weave_hir(base, plan)
6 MIR
7 weave_mir(mir, plan)                     # mir-family rules and log rules, this file's functions only
8 obj
```

No stage at or before typed HIR awaits any aspect slot. `advice_index` awaits
only stages 1-2 of declaring modules, and stages 1-2 await nothing aspect
related, so the wait graph is acyclic. A file never awaits `match(selector,
dir)` or a sibling's rows: every landed selector atom (`exact`, `prefix`,
`attr`, `within`, `within_tree`, with `!`/`&`/`|`) is a predicate on one fact
[OBS `aspect_match_shard_v1.spl:344-356`], so matching over the file's own rows
is exact. Directory shards serve the reverse direction (which join points does
this selector reach), needed by trace, by the planner and by daemon reuse.

- **Pull, not push.** The first requester of a slot submits the producing task;
  later requesters park. No task iterates "all modules".
- **Domain and cold cost.** The domain root is the root of the build's frozen
  source inventory. On a cold build the first stage 3 therefore waits for stages
  1-2 of every module that declares advice and stage 1 of every other module in
  the inventory. That is a demand on forward declarations which the engine
  produces anyway and which overlaps other files' stages; it is not a barrier on
  weaving. On a warm build it is one root-digest hit. A file with no effective
  advice gets the empty plan as soon as the index slot is set.
- **Failure of `advice_index`.** If a member module fails to parse or to
  resolve a handler, the index slot for that scope and its ancestors is a
  terminal failure naming the module. Every file's stages 1-2 still run and
  report their own diagnostics; stage 3 then fails with one secondary
  diagnostic and **no object is published**. This is intended: the build has
  already failed, and an object woven from an incomplete index must never enter
  the cache. Diagnostics of unrelated files are not lost, because they come
  from stages before the await.
- **Woven unit = one object.** The file's object is keyed by
  `H(hir_key(file), plan_digest(file))` plus the usual MIR/OBJ target inputs. A
  file with an empty plan and no ambient log rule has the constant plan digest,
  so its key equals today's. This matches the sibling's one-object-per-instance.
  The source plan's per-join-point `ComposedBodyId` (§5.3) is the per-join-point
  weave key of §5; the object is per file because a file is the engine's unit
  of object emission (R03).
- **Base body.** The HIR blob under `hir_key` is never mutated. Weaving produces
  a new value from base + plan (`aspect_weave_from_base_v1`, landed, uncalled).
  Unweaving is building from the base with a shorter plan.
- **Determinism.** Plans are sorted by `(order, AdviceId)`; equal order between
  two advice rows on one join point is an error of that task.

### 4.1 Passes removed and the output check that replaces each

| Today | Where | Replaced by (checked by the producing task) |
|---|---|---|
| HIR weave over all modules | `driver_hir_pipeline_support.spl:684` | stage 5; check: advice calls per join point == plan length, in plan order |
| Aspect validation over all modules | `driver_hir_pipeline_support.spl:678` | declaring module validates its handlers at stage 2; the weave stage checks handler-vs-join-point compatibility for its own matches |
| MIR `weave_aop` over all modules (mir family, ambient log rules) | `driver_aot_pipeline.spl:278`, `driver_pipeline_aop.spl:47-145` | stage 7 over the file's own functions with `weave_function` + `apply_weaving_result_checked_v1` (landed); rule set and log config are per-file key inputs (§5) |
| Global conflict detection | `driver_pipeline_aop.spl:103` | per-file check over the rule set that applies to that file |
| Global registry, text scan for advice modules | `aspect_registry.spl:50-56`, `driver_worker_surface_closure_v1.spl:395` | `advice_index` over `aspect-decl\|` |
| Process-global match state | `aop_match_cache_driver_v1.spl:337` | engine slot table + packed shard artifacts |
| Global weave accounting | `mir_aop_injection.spl:21-31` | counters on the task receipt |
| In-place mutation + already-woven scan | `aspect_weave.spl:70-87` | immutable base + plan |

## 5. Keys and artifacts

| Artifact | Key inputs | Target in key | Stored as |
|---|---|---|---|
| `advice_index(scope)` | `aspect_root_digest`, codec version | no | packed blob, set-once slot |
| `join_point_facts(dir)` | member `join-point\|` digests, child roots, guard root | guard root only | inline table in `__init__.tld` |
| match shard | `pointcut_match_identity_v1` (sha256 over selector digest + facts key) [OBS `aspect_match_shard_v1.spl:366-370`: `pointcut_match_identity_v1`] | via facts key | packed blob; ids only |
| woven unit object | `hir_key` + `plan_digest` + MIR/OBJ inputs | yes (MIR/OBJ level) | the file's object, with its plan rows and reverse-reference rows (§6.1) |

The xxh3 `pointcut_match_key_v1` [OBS `:115-124, 362-364`] is an in-memory slot
handle only and is never written; every persisted or cross-trust read verifies
the sha256 identity (engine A-2). Digests are algorithm-tagged and an unknown
algorithm is a miss (`aop_digest_known_v1`, landed).

**Per-join-point weave key [PROP].** The landed `advice_apply_key_v1` [OBS
`aspect_match_shard_v1.spl:427-431`] folds the shard's `match_digest`, which
hashes the selector digest, the directory facts key and the whole id list [OBS
`:378-388`]. With it any sibling edit or selector edit changes every apply key
in the directory. AW-5 defines a key with no shard-wide input:

```text
join_point_weave_key = H(JoinPointId, join point signature digest, base body digest,
                         ordered [AdviceId, mode, activation, signature digest,
                                  effects digest, order])
```

It has no advice body digest (decision D1, §10). `advice_apply_key_v1` stays for
the shard-level delta until AW-5 lands and is then retired.

**Mir family and ambient log rules.** Shards cannot express them (G14), and D2
keeps it so. They are still per-file inputs, not a pass: `mir_rule_set_digest`
is the digest of the ordered mir-family rows in `effective_advice(dir(file))`
(selector, form, priority, handler signature/effects), and `log_config_digest`
is the digest of the log instrumentation config derived from `aspect_params`
[OBS `driver_pipeline_aop.spl:71-91`]. Both fold into `plan_digest(file)`. This
is coarse on purpose: a mir-family rule change in a scope rebuilds every file in
that scope, whether or not a function matched. Narrowing it needs mir join-point
facts, which is outside D2.

Dynamic (`ActivationMode` = registry) advice is never keyed here and stays on
the dynload registry path.

## 6. Invalidation

In a demand-driven engine a changed input changes a key and the slot misses.
Reverse references are needed for three things: choosing which file tasks to
submit at all, the pre-edit impact preview, and trace. Rows go into the existing
`aop-consumer` family, written by the task that performed the read:

| Row (definition -> consumer) | Written by |
|---|---|
| `PointcutSelectorId` -> match shard identity; directory facts key -> match shard identity; shard -> `JoinPointId` | match task |
| advice facet `advice.signature` / `advice.effects` / order -> woven unit key | file task, weave stage |
| mir rule set digest, log config digest -> woven unit key | file task, weave stage |
| advice facet `advice.body` -> advice module object (not the woven unit key; D1) | advice module task |
| `JoinPointId` -> ordered `AdviceId` list | file task (the trace edge) |

### 6.1 Cache hits replay their rows

A task that hits does not run, so it cannot write rows. Each artifact record
therefore stores the rows its producer wrote (the woven unit: its plan rows and
`aop-consumer` rows; the shard: its three row kinds). On a hit the engine
replays the stored rows into the session's reverse-reference registry. A record
without its row block is a miss. This is the same rule the sibling uses for
instance records.

A hit must also prove `plan_digest` without running any match. The unit's
receipt records the inputs the plan was computed from: the domain
`aspect_root_digest`, the digest of the file's own `join-point|` rows, and
`log_config_digest`. The plan is a pure function of exactly those (§4), so when
all three are unchanged the recorded `plan_digest` is reused and no aspect slot
is requested. If any differs, stage 3-4 run (they need no HIR beyond stage 2)
and the new `plan_digest` decides hit or miss.

### 6.2 Matrix

| Change | Match / plan work | Rebuilt | Not rebuilt (negative control) |
|---|---|---|---|
| nothing | none: zero aspect slots requested | nothing; zero links | everything |
| selector text / AST (logical) | plans of files in old ∪ new candidate directories | files owning ids in `old \ new` (unwoven from base) and `new \ old` (woven); intersection only if its weave key changed | files in neither set |
| advice body, same signature and effects | none | advice module object + relink; a woven unit only if the inline-deps input lists that advice as inlined into it (D1) | match sets; every other woven unit |
| advice signature, effects or order | none | every woven unit that has the advice in its plan; compatibility recheck; ABI consumers of the advice symbol | files without the advice |
| join point added / renamed / attribute or signature change | that file's plan; the directory shard for trace | that file | sibling files (their plans read only their own rows) |
| join-point body only | none | that file | others |
| aspect declaration added / removed | `advice_index` of that directory and its ancestors | files whose `plan_digest` changed | files whose plan digest is unchanged |
| mir-family rule or log config change | none | every file in the rule's scope (coarse, §5) | files outside the scope |
| `@when` / target guard flip | facts and plans of that guard root | affected files for that target | other targets |
| reverse-reference shard incomplete or undecodable | recompute for the bounded affected scope | conservative: all members of the affected directories | never a narrower guess |

**Planner input.** The planner is the landed `pointcut_affected_files_v1`, whose
`PointcutDirChangeV1` needs, for the old side, the old facts (`facts_key`,
`complete`, `active_guard_root`, member inventory, id -> owner file), the old
shard and the old apply map [OBS `incremental_rebuild_plan_v1.spl:26-32, 88-99`].
Shards are in memory only until AW-8 (G5), so AW-6 persists a per-directory
**aspect plan receipt** next to the incremental manifest: the facts header
(`scope_id`, `facts_key`, `complete`, `active_guard_root`, sorted member files),
the `JoinPointId -> owner file` map, per effective selector the shard (sorted
ids, `complete`, `match_digest`), and per join point its weave key. The planner
signature does not change; AW-6 builds real `PointcutDirChangeV1` values from
the previous receipt and the current one. The receipt is bounded by the
existing per-directory limits and is replaced by the packed shard records at AW-8.

**No-change proof.** By §6.1 an identical build requests no aspect slot, and the
final-artifact precheck (B-1..B-3) sees matching receipts, so there is no weave
and no link. Note: this design narrows the engine design's "advice bodies ->
woven bodies" invalidation input (`pseudo_immutable_cache_async_build_design.md`
§6) to "advice bodies -> advice object, and woven bodies only via inline deps".

## 7. Trace

Facts are in the sections, shards and replayed rows; nothing extra is stored.

| Query | Answer from |
|---|---|
| which advice applies to this function, in what order | rows `JoinPointId -> AdviceId`, or `weave_plan(file)` |
| which join points does this advice / selector apply to | rows selector -> shard -> ids, across directories |
| why does it (not) match | pure re-evaluation of the selector AST over that one fact, returning each node's truth value and the fact field it read |
| what would an edit to this selector / advice rebuild | `pointcut_affected_files_v1` dry run |
| was the answer exact | shard `complete` -> precision `exact`, `bounded_set` or `unknown`; mir-family answers are `bounded_set` (scope, not matched function) |

One pure function returns these as attributable rows (stage AW-11). They are
facts for the single `TraceViewProjection` of
`doc/04_architecture/extreme_typing_traceability.md`, which CLI, LSP and MCP
render. That projection is not implemented (G12). It is one shared stage, owned
by the extreme-typing lane; generic S3-F8 and aspect AW-11 add fact rows to it.
This design adds one relation (`advises`, advice -> join point, with precision)
to the trace model/schema/codec and no second query authority.

## 8. Bounds, memory, concurrency

- No lock, no lease: slots are set once; shards, facts and plans are immutable
  values; a slot's producer is the single-flight leader; publication is temp +
  rename (R11). State belongs to the scheduler loop and the session.
- Bounded: advice declarations per domain, selector nodes, join points per
  directory, shard count and bytes (through the ledger, S3-5). Over a limit the
  slot fails with a diagnostic naming the limit.
- No GC: shard and plan values belong to the `BuildSession` and are freed with
  it; a module's plan is freed after its object is emitted (R12).
- An abandoned leader is re-driven by the next requester.

## 9. Dependencies on the engine

Detailed per stage in the plan. The fact sections, selector unification, the
pure "why" evaluator, weave key and plan digest, the planner input, rows on the
current synchronous path and the coverage gate do not need the engine and start
now. The index as an async slot needs S1-3 and S1-5 plus the five prerequisites
of `doc/03_plan/compiler/cache/tldr_caller_async_prerequisites_2026-10-30.md`.
Weave as stages of the file task needs S1-1, S1-2 and S2-1. Packed artifacts and
limits need S2-6, S3-1, S3-4 and S3-5. Zero-reweave and the inline guard need
B-1..B-3 and S3-7. The passes are deleted only after S2-3's
standalone-versus-runner differential is green.

## 10. Owner decisions (2026-11-28)

- **D1. Advice body edit rebuilds only the advice module object and relinks.**
  The weave is call-only and formally bound, so the join point's object bytes
  do not depend on the advice body; `join_point_weave_key` has no advice body
  digest. This holds only while advice is never inlined into a join point's
  object. The guard is the engine's inline-deps invalidation input (S3-7): when
  it lists an advice function as inlined into a unit, the advice body digest is
  an input of that unit and the woven object rebuilds. **Interim rule until
  S3-7 lands:** a handler that has an `inline|` TLDR entry (the module TLDR
  already emits `inline|` sections for any function, `module_artifacts_v1.spl:268-270`)
  keeps its body digest in the weave keys of the join points it advises; every
  other handler does not. Positive and negative controls are in AW-5 (interim
  rule) and AW-10 (inline-deps input).
- **D2. Scope of kinds: keep.** Cached matching covers `forward` join points
  and static `before`/`after` only. The mir family and ambient log rules are
  per-file inputs with a coarse key (§5); other kinds stay on their current
  path and are `unknown` in trace.
- **D3. One shared `TraceViewProjection` stage,** owned by the extreme-typing
  lane; generic S3-F8 and aspect AW-11 add fact rows. Neither lane builds a
  projection or a query authority of its own.
- **D4. Coverage is measured as decision and condition coverage** for now. One
  gate script serves both lanes (built in the shared coverage-gate lane), with
  decision coverage, condition coverage, the function-entered check and `\\?\`
  path normalisation; each lane supplies a scope list and a spec list.
- **SSpec as document.** Every acceptance spec is an SSpec written as
  documentation (`doc/07_guide/infra/sspec_documentization_maintenance.md`),
  scored by `sspec-maintain scan` with a minimum score, with its `doc/06_spec`
  mirror; the same shared gate checks it (plan §3).

## 11. Coverage gates

Targets: 95 % per touched unit module from its unit specs; 70 % over the aspect
TLDR / async / trace / invalidation module set from unit + integration + system
specs. Measure: decision and condition coverage (D4).

Measured on this host, seed `C:/dev/keep/seeds/simple-local-20261128f.exe`
(40,430,592 bytes):

```text
SIMPLE_EXECUTION_MODE=interpreter SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT=<file> \
  <seed> run test/01_unit/compiler/aop/aspect_match_shard_v1_spec.spl      # 3 s, 20/20 pass
```

- The report is written and works on Windows.
- `lines |file, line, hit_count|` lists executed lines only: 460 rows, summary
  `total_lines = covered_lines = 459`. There is no line denominator, so a line
  percentage cannot be computed. `functions` has the same shape (74 of 74).
- Decisions and conditions carry every site of every loaded file. For
  `aspect_match_shard_v1.spl` from its own unit spec: 51 of 75 decisions (68 %),
  46 of 78 conditions (59 %), 181 hit lines out of 355 non-blank, non-comment,
  non-declaration lines. A source-derived line denominator over-counts, because
  continuation lines of a multi-line expression are never reported as hit.
- File names in the report are `\\?\C:\...` backslash paths. The existing gate
  (`scripts/check/check-hash-algos-coverage.shs:321`) compares exact absolute
  paths and would find no rows on this host.
- `bin/simple test --coverage` needs the self-hosted child receipt and cannot be
  used under the seed (`doc/07_guide/infra/testing/coverage.md`).

Gate [PROP], the one script shared with the generic lane, modelled on
`check-hash-algos-coverage.shs` (per-lane scope and spec lists; fail-closed
verdict line; `--selftest`; manifest row plus dispatch case):

1. Per scope file, `decision % = covered / total` and `condition % = covered /
   total` (both-outcomes rule), merged over the listed specs. Unit gate: each
   touched module >= 95 % on both, from unit specs only. Set gate: totals over
   the module set >= 70 % from unit + integration + system specs.
2. **Function-entered check**, because a function with no branch has no decision
   site: every `fn` in a scope file must have at least one hit line inside its
   range. The unit gate requires all of them; the set gate counts them.
3. A scope file with no rows at all is 0 %, not skipped. A red spec, an empty
   denominator or a missing binary is ERROR, never a pass.
4. Paths are normalised (strip `\\?\`, backslash to slash, make repo-relative).
5. Justified exclusions are listed by `<file>:<line>:D|C<n>` with a reason.

Module set (existing files this work touches, plus the new ones the plan
names): `cache_contract/aspect_match_shard_v1`, `directory_aspect_{draft,projection}_v2`,
`directory_join_point_table_v3`, `80.driver/cache/aop_match_cache_driver_v1`,
`aop_guard_eval_v1`, `directory_aspect_{capture,semantic}_v2`,
`incremental_rebuild_plan_v1`, `35.semantics/aspect_weave`, `50.mir/mir_aop_injection`,
`85.mdsoc/aop_index/reverse_index`, and the new section codec, query, plan,
explain and trace-row modules.
