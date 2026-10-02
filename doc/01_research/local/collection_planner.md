<!-- codex-research -->
# Typed DataFrame-able collections and collection planner: local research

Status: current-tree inventory, 2026-09-27. The detailed prior analysis is
[collection_plan_ir_2026-07-31.md](../compiler/collection_planner/collection_plan_ir_2026-07-31.md);
its July readiness table is historical. This note records current code and
does not replace that research.

## Existing foundations

- `src/lib/nogc_sync_mut/df/` and `nogc_async_mut/df/` expose numeric Series and
  DataFrame operations. Numeric joins, group-by, unique, counts and pivot use
  `NumericJoinIndex`, including duplicate chains and explicit NaN/zero policy.
  Columns remain runtime `DType`/`DfValue` based rather than `Series<T>`.
- `src/compiler/35.semantics/perf_facts/` contains a typed HIR operation
  registry and collector keyed by resolved symbol ID. It is not populated and
  invoked as one production registry across lint and optimization.
- `src/compiler/35.semantics/perf/collection_plan.spl` defines logical nodes,
  facts and a validator. Its extractor recognizes resolved unary call chains.
  `src/compiler/60.mir_opt/mir_opt/collection_plan_selection.spl` is a separate
  fail-closed physical choice gate. No end-to-end HIR-to-MIR plan lowering or
  invocation is established.
- Existing `collection_opt*.spl` MIR passes and `COLL001`–`COLL019` lint rules
  cover selected patterns. Functional-form complexity coverage, loop extraction,
  symbolic cost summaries and planned typed lint rules remain incomplete.
- `std.nogc_sync_mut.src.map.Map<K,V>` supplies generic `Hash + Eq` keys.
  `Set<T>` retains linear membership; generic primitive-key hash behavior and
  cross-engine parity have no admitted evidence. Older HashMap/HashSet modules
  are text-specialized. The pure `unique` and `group_by` paths still need the
  P1 asymptotic audit and replacement.

## Required work and gates

P0 requires cross-engine closure, map/filter/any/all and native Dict evidence.
P1 removes quadratic standard-library collection implementations. P2 certifies
generic hash-backed keys and sets. P3 adds typed, functional-form cost lint.
P4 connects loop and chain extraction to legal fusion and MIR lowering. P5
selects equality-key index/join plans with duplicate, order and effect proofs.
P6 adds profile records and guarded adaptive choice. Numeric DataFrame indexing
is useful library work but does not establish P4/P5 compiler planning.

The self-hosted Linux Stage2 candidate clears frontend and receiver admission,
but the phase verification matrix rejects its full CLI build on 30 HIR field
inference errors. Until a full pure-Simple test runner is admitted, focused
DataFrame and plan specs lack current executable evidence. See
`doc/08_tracking/bug/linux_stage2_full_cli_hir_field_inference_2026-09-27.md`.

## Knowledge routing

The common SPipe compatibility route is `.spipe/spipe`; current registry has
no exact `collection_planner` feature route. Longest-prefix routes select the
compiler-pipeline and runtime-memory-I/O layer bases. Selection is recorded in
`.spipe/collection_planner/knowledge_selection.sdn`; the missing feature route
is a research/configuration gap.

## 2026-10-03 release-lane re-audit (Codex)

Baseline: `origin/release/1.0`, commit
`e9cd3153c881c55f59eaaa2573b4b8a5e803023a`. This supplement preserves the
September inventory as history; it does not claim executable verification.

| Evidence at baseline | Consequence for the next TDD slice |
|---|---|
| Both `nogc_sync_mut/df/typed_series.spl` and `nogc_async_mut/df/typed_series.spl` define `TypedSeries<T>`, numeric adapters, missing-mask validation, map/filter and short-circuit methods. | The older statement that columns have no typed facade is stale. Assert facade semantics and adapter failures before extending it; generic typed DataFrame schema and richer errors still need evidence. |
| `35.semantics/perf_facts/builtin_collection.spl` admits unary array lambda map and capture-free filter by typed builtin identity. | This is dispatch admission, not callback purity, arbitrary collection coverage, or five-engine parity. Named callbacks, any/all/flat-map and captures need separate fixtures. |
| `CollectionOperationRegistry` stores summaries by resolved symbol and tracks ambiguous symbols; the planned `config/compiler/collection_operations.sdn` is absent. | In-memory metadata types do not meet REQ-003's production, versioned registry contract. Test duplicate IDs, wrong receiver/signature, backend symbol absence and cache invalidation. |
| `extract_unary_collection_plan` rejects chains longer than 128 and unknown metadata; callback/alias/escape/profitability facts start unproven. | Preserve this bound and fail-closed behavior. Add loop extraction only with typed equivalence evidence; method spelling cannot authorize rewrites. |
| `collection_plan_selection.spl` explicitly calls itself advisory; its algorithms are Original/Linear/Hash/Ordered. | These collection-storage choices are not yet the architecture's fusion/nested/hash/merge/direct-index execution operators. Keep those meanings distinct. |
| `collection_plan_explain.spl` prints `extra_memory_bytes=unproven` for selected alternatives and `memory_budget=not-modeled`. | Add numeric peak-memory and output-work admission before claiming REQ-009/NFR-004. Explain text alone cannot prove a selected plan executed. |
| Compiler reference search finds selector/renderer definitions and exports, but no invocation from driver or MIR lowering. | Production pipeline wiring, generated MIR and observed execution are separate mandatory gates, not satisfied by selector unit tests. |

Research result: retain selected REQ-001–011 without adding unselected scope.
The concrete acceptance matrix is appended to the detail design. The first
integration failure should distinguish unavailable runner, unsupported engine,
unwired planner and semantic mismatch; none may be counted as a passing case.
The September Linux runner blocker is historical until rechecked on the current
host. No runtime pass or current host failure is inferred from that report.

Parallel planner-lane inspection additionally identified distinct logical and
physical `CollectionPlanFacts` types with no established bridge, absent
explicit-loop extraction, and operation summaries without the full
worst-cost/backend/key contract. These are integration tasks, not safe field
renames. The lane also flagged bare-method-name pure-query caching and coarse
Array/Tuple/Struct constant keys in `collection_opt_core.spl` for a targeted
collision reproducer; this is a reported risk pending reproduction, not a
verified regression or authorization to expand the present rewrite scope.

Host admission update from the integration lane: the available stage2 binary
supports diagnostic compilation but has no test/run CLI. A full self-hosted
runner has not been admitted for this work. Consequently, this dated audit and
its focused guard implementation cannot report runtime PASS; five-engine
parity, generated manuals and retained NFR measurement remain open gates.
