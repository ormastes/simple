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
