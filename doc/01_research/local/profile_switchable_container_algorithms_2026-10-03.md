# Item 7 completion research: current source boundary

Research owner: `research_design`, isolated branch `work/item7-research-20261003`, target `release/1.0`. This supplement preserves earlier research and the user's selected full item 7 scope. It records source inspection, not executable acceptance.

## What exists

`src/compiler/35.semantics/perf/collection_plan.spl` defines a typed logical DAG with explicit input order, source expressions, key/result types, effect facts, order and uniqueness. Its operation enum includes joins and materialization, but enum membership alone does not implement those operations. `collection_plan_extractor.spl` extracts resolved unary Map, Filter, FlatMap, DistinctBy and CollectArray calls using the registered symbol summary. `collection_plan_analysis.spl` invokes that extractor. Unknown equality, alias, callback, escape and profitability proofs remain false.

`src/compiler/60.mir_opt/mir_opt/collection_plan_selection.spl` defines a separate physical `CollectionPlanFacts`, `CollectionPlanAlgorithm` and `CollectionPlanDecision`. It selects Original/Linear/Hash/Ordered from explicit semantic guards, target capabilities, policy, cost and memory facts. Its header correctly describes its advisory status. These two identically named facts records are different contracts: no field-copy shortcut or wildcard-import bridge can establish the missing proofs.

Existing runtime/profile work is described in the [detail design](../../05_design/compiler/profile_switchable_container_algorithms.md). Text and generic adaptive containers, parser embedding and prepared profiles are real implementation slices. They do not establish typed aggregate ordering, closure dependency identity, join lowering, all P6 instrumentation, or admitted cross-backend behavior.

## Remaining evidence obligations

1. Retain attributed declaration identity through typed HIR, including nested lexical owners and factory-result validation.
2. Adapt logical facts to physical facts with analysis-owned proof receipts. Preserve unknowns; p95 cannot become a hard size bound.
3. Connect legal physical decisions to executable MIR and preserve original evaluation, callback count, duplicates, observable order and mutation epochs.
4. Extend extraction/lowering to the selected set/map and join surface only after the research P0 gates execute successfully.
5. Admit profile data against an immutable source/dependency snapshot and target/workload identity. Profile-only cache invalidation is insufficient for imported code changes.
6. Instrument the applicable eleven P6 metrics, separating unknown from measured zero. Document applicability per operation.
7. Execute the shared PSC-AC-001 through PSC-AC-008 matrix on admitted self-hosted runners. Source searches and C channel selfchecks cannot substitute for interpreter/native integration.

No requirement is dropped because a runner or a backend is unavailable. Those results remain unverified and release-blocking. Concrete acceptance cases and lowering contracts are appended to the architecture and detail design.
