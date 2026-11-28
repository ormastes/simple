# Aspect weaving through TLDR: async match and weave queries, trace, invalidation

**Date:** 2026-11-28. **Base:** `origin/release/1.0.0` @ `df04c6a4e7d`.
**Status:** design, nothing here is implemented. Addendum to
`pseudo_immutable_cache_async_build_design.md` (engine, R01-R15) and to
`doc/03_plan/compiler/cache/generic_aop_macro_semantic_cache_plan_2026-10-24.md` §5.
**Sibling:** `generic_instance_tldr_trace.md` (generic instances on the same engine);
this document uses the same scheduler, slot table, reverse-reference machinery and
coverage gate, and adds none of its own.
**Plan:** `doc/03_plan/compiler/aspect_cache/aspect_tldr_async_trace_plan.md` (stages AW-0..AW-12).
**TLDR:** `aspect_tldr_async_trace_tldr.md`.

Marks: **[OBS]** = read in `src` at the base commit (file:line given); **[PROP]** = proposed.

## 1. Model in one paragraph

There is no weave pass. Pointcut matching and weaving are queries in the one
engine: each is a single-flight, set-once slot keyed by content, produced by a
task in the same scheduler as `CompileTask(file)`, and consumed by awaiting its
handle. A file's compile task learns which advice applies to it from
TLDR-carried facts only (aspect declarations aggregated up the directory tree,
join-point facts per directory), never from another file's HIR or a
process-global registry. It weaves from an immutable base body and a
deterministic ordered plan, as a stage of its own src -> obj pipeline. Every
former whole-program check becomes an output check of the task that produced
the value.

## 2. Census: landed versus planned (verified in code)

### 2.1 Landed and on a production path

| Piece | Where | Note |
|---|---|---|
| Selector AST, directory facts, match shard, apply key, old/new delta (pure) | `00.common/cache_contract/aspect_match_shard_v1.spl:33-102, 321, 362, 372, 427, 435` | 13 spec files reference it |
| Forward (HIR) weave driven by shards | `80.driver/cache/aop_match_cache_driver_v1.spl:268-331`, called at `80.driver/driver_hir_pipeline_support.spl:684` | visits only modules that own a matched id; falls back to every module on any incompleteness |
| Directory source snapshots (facts captured from HIR + frozen sources) | `80.driver/cache/directory_tldr_snapshot_capture_v2.spl:36`, used from `driver_hir_pipeline_lowering.spl:4` | compile-local, not persisted |
| Guard evaluation for facts | `80.driver/cache/aop_guard_eval_v1.spl:28,48` | **0 spec files** |
| Aspect declaration draft / semantic capture (signature and effects digests) | `80.driver/cache/directory_aspect_capture_v2.spl:12`, `directory_aspect_semantic_v2.spl:35,118`; DTOs `cache_contract/directory_aspect_{draft,projection}_v2.spl` | "draft facets, not final authority" (`directory_aspect_draft_v2.spl:1-3`) |
| Inline join-point table in `__init__.tld` | `cache_contract/directory_join_point_table_v3.spl:66,85`, wired at `package_init_tld_v1.spl:145,183`; fields `parent_scope_digest`, `aspect_root_digest` at `:22,:25` | codec only; "no source freshness or guard execution is proved" (`:1-2`) |
| Selector plan cache (bounded 256, FIFO) | `aop_match_cache_driver_v1.spl:59-66, 114` | |
| Query kinds `aop.directory_facts`, `aop.match`, `aop.weave`; family `aop-consumer` | `semantic_query_read_manifest_v1.spl:208`, `reverse_reference_projection_v2.spl:79`, `reverse_reference_key.spl:46`, `reverse_reference_receipt.spl:40,57` | names admitted |
| Call-only weave proof | `test/00_formal_verification/compiler/aop_call_only_weave_contract_spec.spl`, `src/verification/build_cache/src/WeaveCallOnlyV1.lean` | the weave inserts one `Call` to the advice name and never reads the advice body |

### 2.2 Gaps

| # | Gap | Evidence |
|---|---|---|
| G1 | **Weaving is two whole-program passes behind a barrier.** HIR: after all modules are lowered and validated. MIR: `weave_aop` loops over every MIR module with its own matcher (`weave_function`), no shard cache. | `driver_hir_pipeline_support.spl:678-685`; `driver_aot_pipeline.spl:275-280`; `driver_pipeline_aop.spl:47-145` |
| G2 | **Nothing is async.** The single-flight use is join, compute, complete, forget in one synchronous call; no waiter can exist. The directory gate says the same of itself. | `aop_match_cache_driver_v1.spl:198-212`; `directory_tldr_cache_gate_v2.spl:1-5` ("NOT asynchronous waiter coalescing") |
| G3 | **Engine steps this needs are absent:** `parse_async`, `lower_hir_async`, `lower_mir_async`, `emit_object_async`, `read_tldr_async`, `trait CompileInvoker`, key record v2, write-once slot type, `.sphb`/`.spmb`, usage ledger (0 hits each). Present: `FiberSchedV1` (`src/lib/common/task_runner/fiber_scheduler.spl:45-271`), `TldrTableV1.request_async` (`80.driver/cache/reader/tldr_table_v1.spl:88`), `CacheSingleFlightV1` (`cache/daemon/cache_single_flight_v1.spl:27`). | `git grep` at base; same finding as the sibling plan §5 |
| G4 | **Advice is discovered from process-global state and a source text scan, not from TLDR.** Registry is module-level `var`s filled during parse; file workers load any module whose text may declare advice. | `10.frontend/aspect_registry.spl:50-56, 80-85`; `80.driver/driver_worker_surface_closure_v1.spl:390-395`; `driver_advice_scan_v1.spl:30` |
| G5 | **Match state is process-global, in memory only, unbounded.** One module-level `var`; shards are never written to disk; every insert copies the whole `Dict`. | `aop_match_cache_driver_v1.spl:337`; `aspect_match_shard_v1.spl:84-86, 414-417` |
| G6 | **Old ∪ new invalidation is spec-only.** The planner exists, but its only production caller passes an empty pointcut list and `PointcutDirChangeV1` has no constructor call anywhere in `src`. | `incremental_rebuild_plan_v1.spl:86-108`; `driver_build/native_file_worker_incremental_io_v1.spl:126` |
| G7 | **No production caller:** `advice_apply_key_v1`, `aspect_weave_from_base_v1` / `aspect_weave_base_record_v1` (weave from an immutable base), `aspect_match_forward_reads_v1`, `pointcut_match_universe_v1`, `aop_reverse_index_build`, `85.mdsoc/aop_cache/aop_group_manifest.spl` (0 importers). | `aspect_match_shard_v1.spl:427, 468, 505`; `35.semantics/aspect_weave.spl:178, 190`; `85.mdsoc/aop_index/reverse_index.spl:104` |
| G8 | **Production weave mutates the module in place** and relies on a scan for an existing call to stay idempotent. | `35.semantics/aspect_weave.spl:70-87, 202-226`; `aop_match_cache_driver_v1.spl:325-328` |
| G9 | **Directory TLDR store, gate and producer are unwired** (0 `src` importers outside themselves; one system spec). | `80.driver/cache/directory_tldr_{cache_gate,producer,store}_v2.spl`; plan `directory_tldr_native_qualification_2026-11-14.md` ("Full production routes remain UNRUN") |
| G10 | **No `aop-consumer` rows from a real weave.** `reverse_reference_register_aop_v1` has one caller, the wrapper in `reverse_index.spl:24`, reached only from the uncalled `aop_reverse_index_build`; `incremental.spl:1045-1116` only projects whatever the registry holds, so the family is published empty or unknown. | `reverse_index.spl:20-24, 104-146`; `reverse_reference_facts.spl:424-427` |
| G11 | **Three selector identities coexist:** `pointcut_selector_parse_v1` (shards), `aop_predicate_canonical_text` (MIR pass), `aop_selector_digest` (mdsoc index, substring read-set). | `aspect_match_shard_v1.spl:321`; `10.frontend/core/aop_predicate_parser.spl:43`; `85.mdsoc/aop_cache/aop_group_keys.spl:65`; `reverse_index.spl:9-13` |
| G12 | **No trace surface.** `TraceViewProjection` has 0 source files; `TraceRelation` has no advice edge; no CLI, LSP or MCP entry answers "which advice applies here and why". | `src/lib/common/traceability/model.spl:267-284`; `git grep TraceViewProjection -- src` = 0 |
| G13 | **Conflict detection and weave accounting are global.** | `driver_pipeline_aop.spl:103`; `50.mir/mir_aop_injection.spl:21-31` |
| G14 | Only `forward` join points and static `before`/`after` are cacheable; the other six kinds are unmeasured. This is a stated restriction, kept. | `35.semantics/aspect_weave.spl:8-16`; `aspect_match_shard_v1.spl:422` |

## 3. Facts carried by TLDR

Two sections on a module's TLDR, both forward declarations (no body is needed to
read them) and both written by that module's own compile task [PROP]:

| Section | Row | Written at | Existing DTO it reuses |
|---|---|---|---|
| `aspect-decl\|` | `AdviceId`, form, mode, `ActivationMode`, canonical selector text + `PointcutSelectorId`, `PointcutScopeId`, order/priority, `@readonly/@noalloc/@bounded_time` | parse stage | `DirectoryAspectDeclarationV2` |
| `aspect-decl\|` set-once slot | `AdviceSignatureEffect` = signature digest + effects digest | typed-HIR stage | `DirectoryAspectHandlerV2` |
| `aspect-decl\|` facet `advice.body` | `AdviceBodyDigest` | typed-HIR stage | new facet; never read by matching |
| `join-point\|` | `JoinPointId`, kind, name, owner file, signature digest, attributes, guard ids; includes non-exported functions | typed-HIR stage | `JoinPointFactV1` |

Aggregation uses the fields `__init__.tld` already has [OBS
`package_init_tld_v1.spl:22-38`]. `aspect_root_digest` is a codec field with no
producer today (it is only encoded, decoded and validated there), and
`directory_tldr_roots_v2_2026-11-14.md` records that aspect catalog roots "are
currently broader than a directory and require scoped aggregation". This design
supplies that aggregation [PROP]: the per-module leaf is the landed
`DirectoryAspectSemanticV2.interface_digest` [OBS
`directory_aspect_semantic_v2.spl:100-113`: declaration rows + signature +
effects, **no body**]; a directory's root is the digest over its members'
sorted leaves and its children's roots. So an advice body edit does not move
any aspect root. `parent_scope_digest` chains upward; the inline join-point
table is the directory's `DirectoryJoinPointFactsV1`.

`PointcutSelectorId` is the digest produced by `pointcut_selector_parse_v1`
(the only parser with a typed AST and a `supported` flag). The other two
identities (G11) are retired by AW-3; a selector that parser cannot evaluate
completely is `supported = false` and is never cached.

## 4. Queries

All slots live in the engine's one single-flight table; kinds are the admitted
`aop.*` names.

```text
advice_index(scope)                      # kind aop.directory_facts (decl half)
  = merge(own aspect-decl rows, for child in children: await advice_index(child))
  key = aspect_root_digest(scope)         # Merkle; unchanged subtree = one hit

effective_advice(dir)                    # what can apply inside dir
  = filter(await advice_index(domain root), scope admits dir)   # sorted by (order, AdviceId)

join_point_facts(dir)                    # kind aop.directory_facts (fact half)
  = merge(join-point| sections of dir's member TLDRs)           # DirectoryJoinPointFactsV1

match(selector, dir)                     # kind aop.match -> PointcutMatchShardV1
  key = pointcut_match_key_v1(selector, facts)                   # unchanged from today

weave_plan(file)                         # set-once slot on the file's task
  for advice in await effective_advice(dir(file)):
      shard = await match(advice.selector, dir(file))
      take shard ids owned by file
  per join point: ordered advice list -> advice_apply_key
  plan_digest(file) = H(sorted (JoinPointId, apply keys))        # empty plan = fixed constant

CompileTask(file):  parse -> HIR(base, immutable) -> weave_hir(base, plan)
                    -> MIR -> weave_mir(mir, plan) -> obj
```

- **Pull, not push.** A file's task awaits `effective_advice` and `match`; the
  first requester of a slot submits the producing task, later requesters park.
  No task iterates "all modules". `advice_index` reads `aspect-decl|` sections,
  which exist after the parse stage of the declaring module (or from its cached
  TLDR with no parse at all), so it never waits on any HIR.
- **Domain and cold cost.** The domain root is the root of the build's frozen
  source inventory (the same inventory the directory snapshot capture pins).
  On a cold build the first weave stage therefore waits for the parse-surface
  TLDR of every module in the inventory. That is a demand on forward
  declarations, which the engine produces anyway and overlaps with other files'
  HIR/MIR/obj stages; it is not a barrier on HIR or on weaving. On a warm build
  it is one root-digest hit. A file in a directory with no effective advice gets
  the empty plan as soon as the index slot is set.
- **Completeness.** A selector that needs the universe (negation, recursive
  `within`) awaits the facts of every directory its scope names
  (`pointcut_match_universe_v1`). A missing or incomplete facts slot makes the
  shard `complete = false`: the file's task then evaluates the selector over its
  own join points directly, uncached. That is still a per-task query; the
  "visit every module" fallback (`aop_match_cache_driver_v1.spl:300-324`) is removed.
- **Woven unit = one object.** The file's object is keyed by
  `H(hir_key(file), plan_digest(file))` plus the usual MIR/OBJ target inputs.
  A file with an empty plan has the constant plan digest, so its key equals
  today's and aspects cost it nothing. This matches the sibling's
  one-object-per-instance: one task, one object, named by its key. The source
  plan's per-join-point `ComposedBodyId` (§5.3) is the per-join-point weave key
  of §5; the object is per file because a file is the engine's unit of object
  emission (R03), and `plan_digest` is the digest of its join points' weave keys.
- **Base body.** The HIR blob under `hir_key` is never mutated. Weaving produces
  a new value from base + plan (`aspect_weave_from_base_v1`, landed, uncalled).
  Unweaving is building from the base with a shorter plan.
- **No await cycle.** A file task awaits declarations and facts (TLDR level),
  never another file's object or woven body. An advice function whose own module
  is advised is an ordinary join point of that module.
- **Determinism.** Plans are sorted by `(order, AdviceId)`; equal order between
  two advice rows on one join point is an error of that task. Artifacts never
  record which requester arrived first.

### 4.1 Passes removed and the output check that replaces each

| Today | Where | Replaced by (checked by the producing task) |
|---|---|---|
| HIR weave over all modules | `driver_hir_pipeline_support.spl:684` | `weave_hir` stage; check: advice calls per join point == plan length, in plan order |
| Aspect validation over all modules | `driver_hir_pipeline_support.spl:678` | declaring module's task validates its handlers when it fills the signature/effect slot; the weave stage checks handler-vs-join-point compatibility for its own matches |
| MIR `weave_aop` over all modules | `driver_aot_pipeline.spl:278`, `driver_pipeline_aop.spl:47-145` | `weave_mir` stage with `apply_weaving_result_checked_v1` (landed) |
| Global conflict detection | `driver_pipeline_aop.spl:103` | per-join-point order check while building `weave_plan(file)` |
| Global registry, text scan for advice modules | `aspect_registry.spl:50-56`, `driver_worker_surface_closure_v1.spl:395` | `advice_index` over `aspect-decl\|` |
| Process-global match state | `aop_match_cache_driver_v1.spl:337` | engine slot table + packed shard artifacts |
| Global weave accounting | `mir_aop_injection.spl:21-31` | counters on the task receipt |
| In-place mutation + already-woven scan | `aspect_weave.spl:70-87` | immutable base + plan |

## 5. Keys and artifacts

| Artifact | Key inputs | Target in key | Stored as |
|---|---|---|---|
| `advice_index(scope)` | `aspect_root_digest`, codec version | no | packed blob, set-once slot |
| `join_point_facts(dir)` | member `join-point\|` digests, child roots, guard root | guard root only | inline table in `__init__.tld` |
| match shard | selector digest + facts key (`pointcut_match_key_v1`) | via facts key | packed blob; ids only |
| woven unit object | `hir_key` + `plan_digest` + MIR/OBJ inputs | yes (MIR/OBJ level) | the file's object |

**Per-join-point weave key [PROP].** The landed `advice_apply_key_v1` [OBS
`aspect_match_shard_v1.spl:427-431`] folds the shard's `match_digest`, and that
digest hashes the selector digest, the directory facts key and the whole id
list [OBS `:378-388`]. With it, any sibling join-point edit or any selector edit
changes every apply key in the directory, so neither "intersection reused" nor
"sibling file not rebuilt" can hold. AW-5 therefore defines a second key that
has no shard-wide input:

```text
join_point_weave_key = H(JoinPointId, base body digest,
                         ordered [AdviceId, mode, activation, signature digest,
                                  effects digest, order] (+ body digest under D1 = literal))
```

`plan_digest(file)` is built from these keys only. `advice_apply_key_v1` stays
for the shard-level delta until AW-5 lands and is then retired. Because the
weave is call-only (§2.1), the join point's object bytes do not depend on the
advice body, so two behaviours are possible; see owner decision D1 in §10. Digests are algorithm-tagged; an unknown algorithm is a miss
(`aop_digest_known_v1`, landed). Dynamic (`ActivationMode` = registry) advice is
never keyed here and stays on the dynload registry path.

## 6. Invalidation

In a demand-driven engine a changed input changes a key and the slot misses.
Reverse references are needed for three things: choosing which file tasks to
submit at all, the pre-edit impact preview, and trace. Rows go into the existing
`aop-consumer` family, written by the task that performed the read:

| Row (definition -> consumer) | Written by |
|---|---|
| `PointcutSelectorId` -> match shard key | match task |
| directory facts key -> match shard key | match task |
| match shard key -> `JoinPointId` | match task |
| advice facet `advice.signature` / `advice.effects` / order -> woven unit key | file task, weave stage |
| advice facet `advice.body` -> advice module object (and woven unit key under D1 = literal) | advice module task |
| `JoinPointId` -> ordered `AdviceId` list | file task (the trace edge) |

| Change | Match work | Rebuilt | Not rebuilt (negative control) |
|---|---|---|---|
| nothing | none: zero match tasks, zero weave stages | nothing; zero links | everything |
| selector text / AST | shards of old ∪ new candidate directories | files owning ids in `old \ new` (unwoven from base), `new \ old` (woven); intersection only if its apply key changed | files in neither set; every shard of other selectors |
| advice body, same signature and effects | none; every shard reused | advice module object + relink; woven units too only under D1 = literal | match sets; unrelated files |
| advice signature, effects or order | none | every woven unit that has the advice in its plan; compatibility recheck; ABI consumers of the advice symbol | match sets; files without the advice |
| join point added / renamed / attribute or signature change | owning directory's facts and its shards; ancestors only where a scope names them | files whose `plan_digest` changed | sibling files with unchanged plan digest (early cutoff at `plan_digest`) |
| join-point body only | none | that file | others |
| aspect declaration added / removed | `advice_index` of that directory and its ancestors | files that gain or lose a plan entry | files whose plan digest is unchanged |
| `@when` / target guard flip | facts and shards of that guard root | affected files for that target | other targets |
| RR shard incomplete or undecodable | recompute for the bounded affected scope | conservative: all members of the affected directories | never a narrower guess |

The planner is the landed `pointcut_affected_files_v1`; it receives real
`PointcutDirChangeV1` values (G6). The "old" side cannot come from shards, which
are in memory only until AW-8 (G5): AW-6 extends the per-file incremental
manifest row (`native_file_worker_incremental_v1`) with the file's plan rows
`(JoinPointId, ordered AdviceId list, weave key)`. The old match set of a
selector is the set of join points whose old plan names its advice; the old
apply map is the old weave keys. No-change proof: the domain root `aspect_root_digest` and every
file's `plan_digest` are in the object receipts checked by the final-artifact
precheck (B-1..B-3), so an identical build submits no match task and no weave.

## 7. Trace

Facts are already in the sections, shards and RR rows; nothing extra is stored.

| Query | Answer from |
|---|---|
| which advice applies to this function, in what order | RR `JoinPointId -> AdviceId` rows, or `weave_plan(file)` |
| which join points does this advice / selector apply to | RR selector -> shard -> ids, across directories |
| why does it (not) match | pure re-evaluation of the selector AST over that one `JoinPointFactV1`, returning each node's truth value and the fact field it read; no persisted explanation |
| what would an edit to this selector / advice rebuild | `pointcut_affected_files_v1` dry run |
| was the answer exact | shard `complete` flag -> precision `exact`, `bounded_set` or `unknown` |

One pure function returns these as attributable rows. They feed the single
`TraceViewProjection` of `doc/04_architecture/extreme_typing_traceability.md`,
which CLI, LSP and MCP render. That projection does not exist yet (G12) and the
model has no advice relation; this design adds one relation (`advises`, advice
-> join point, with precision) through the model/schema/codec in one change and
adds no second query authority. See decision D3.

## 8. Bounds, memory, concurrency

- No lock, no lease: slots are set once; shards, facts and plans are immutable
  values; a slot's producer is the single-flight leader; publication is temp +
  rename (R11). State belongs to the scheduler loop and the session, not to
  module-level variables.
- Bounded: advice declarations per domain, selector nodes, join points per
  directory, shard count and bytes (through the ledger, S3-5). Over a limit the
  slot fails with a diagnostic naming the limit; it does not widen silently.
- No GC: shard and plan values belong to the `BuildSession` and are freed with
  it; a module's plan is freed after its object is emitted (R12).
- Failure: a failed slot is terminal for all waiters. An abandoned leader is
  re-driven by the next requester.

## 9. Dependencies on the engine

Detailed per stage in the plan. Summary: the fact sections, selector
unification, the pure "why" evaluator, apply-key and plan digest, the real
planner input, RR rows on the current synchronous path and the coverage gate do
not need the engine and start now. Match and index as async slots need S1-3 and
S1-5 plus the five prerequisites of
`doc/03_plan/compiler/cache/tldr_caller_async_prerequisites_2026-10-30.md`.
Weave as a stage of the file task needs S1-1, S1-2 and S2-1. Packed artifacts
and limits need S2-6, S3-1, S3-4 and S3-5. Zero-reweave needs B-1..B-3. The two
passes are deleted only after S2-3's standalone-versus-runner differential is green.

## 10. Owner decisions

- **D1. Advice body edit.** The directive says an advice body change dirties
  woven objects. The weave is call-only and formally bound, so a rebuilt join
  point object would be byte-identical. Option (a) literal: keep the body digest
  in `advice_apply_key`; every woven unit recompiles and early cutoff stops at
  the unchanged object digest. Option (b): drop the body digest from the key
  while the weave is call-only; only the advice module object and the link are
  rebuilt. (b) is sound only while no advice body is inlined into a join
  point's object: the weavers have no inline path today, and when an advice
  function is inlined by the backend its body must reach the unit through the
  engine's existing "inline deps" invalidation input (S3-7), not through this
  key. Recommended: (b), conditional on that input. The plan implements the key so the choice is one function.
- **D2. Scope of kinds.** Keep the restriction to `forward` join points and
  static `before`/`after` (G14) for this work, with every other kind on its
  current path and reported `unknown` in trace. Recommended: yes.
- **D3. `TraceViewProjection` owner.** Both lanes need it and neither owns it.
  Either the extreme-typing lane builds the minimal projection first, or this
  lane and the generic lane share one stage that adds it with CLI, LSP and MCP
  adapters. Recommended: one shared stage, guided by Fable, after both lanes'
  fact functions exist.
- **D4. Line coverage.** Settled by the owner: decision/condition proxy now.
  Remaining choice: whether to add zero-count line sites to the seed
  (`interpreter/coverage_sites.rs`) so the gate can later be stated in lines.

## 11. Coverage gates

Targets: 95 % per touched unit module from its unit specs; 70 % over the aspect
TLDR / async / trace / invalidation module set from unit + integration + system
specs. Measure: decision and condition coverage (owner decision).

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

Gate [PROP], one script shared with the generic lane, modelled on
`check-hash-algos-coverage.shs` (per-lane scope and spec lists; fail-closed
verdict line; `--selftest`; manifest row plus dispatch case):

1. Per scope file, `decision % = covered / total` and `condition % = covered /
   total` (both-outcomes rule), merged over the listed specs. Unit gate: each
   touched module >= 95 % on both, from unit specs only. Set gate: totals over
   the module set >= 70 % from unit + integration + system specs.
2. **Function-entered check**, because a function with no branch has no decision
   site and would be invisible: every `fn` in a scope file must have at least one
   hit line inside its range. The unit gate requires all of them; the set gate
   counts them into the 70 %.
3. A scope file with no rows at all is 0 %, not skipped. A red spec, an empty
   denominator or a missing binary is ERROR, never a pass.
4. Paths are normalised (strip `\\?\`, backslash to slash, make repo-relative)
   before matching.
5. Justified exclusions are listed by `<file>:<line>:D|C<n>` with a reason, as in
   the hash gate.

Module set (existing files that this work touches, plus the new ones the plan
names): `cache_contract/aspect_match_shard_v1`, `directory_aspect_{draft,projection}_v2`,
`directory_join_point_table_v3`, `80.driver/cache/aop_match_cache_driver_v1`,
`aop_guard_eval_v1`, `directory_aspect_{capture,semantic}_v2`,
`incremental_rebuild_plan_v1`, `35.semantics/aspect_weave`, `50.mir/mir_aop_injection`,
`85.mdsoc/aop_index/reverse_index`, and the new section codec, query, plan,
explain and trace-row modules.
