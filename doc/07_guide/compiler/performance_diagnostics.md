# Compiler Performance Diagnostics

## Operator contract

Simple separates four evidence tiers:

1. `simple check`: high-confidence typed source diagnostics.
2. optimized builds with performance remarks: safe transforms and exact missed reasons.
3. `simple perf --deep`: bounded interprocedural cost and memory summaries.
4. `.sprof` evidence: ranking by observed hotness, cardinality, allocation, and copy bytes.

Source warnings describe likely application defects. Optimizer remarks describe compiler
decisions. Runtime profiles rank candidates but never authorize a semantics-changing
transformation.

## Optimizer truth

The requested pipeline is an inventory. The effective pipeline contains only descriptors
whose `PassStatus` is `Active`. `AnalysisOnly`, `RemarkOnly`, `Skeleton`, and
`Disabled(reason)` entries remain visible but cannot enter transformation dispatch.

Every active transform must have a positive sentinel, negative legality fixture,
idempotence check, IR verification, and semantic differential evidence. Missing facts,
timeouts, or unavailable backends fail closed.

The registry now gives each admitted transform a stable positive and negative witness ID.
The first contracts are `pattern.supported_aes_call`,
`predicate.mask_cmp_masked_add`, `fs.two_stores_same_base`, and
`fs.two_calls_same_callee`, paired with explicit non-candidate witnesses. An `Active`
descriptor without a complete witness contract is a compiler-integrity error.

`optimizationpipeline_report_json` emits deterministic planning evidence under schema
`simple.opt-pipeline-report/v1`. Each requested ordinal records pass status,
expectation, backend outcome and reason. Planning is not execution: its run outcome is
`not-run` and execution counters are `null`. Consumers must not infer that a pass ran or
changed MIR from selection alone. Populated `PassRunRecord` counters will be admitted
only after dispatch owns verified change receipts.

## Diagnostic policy

`COLL*` findings belong to the `collection_performance` lint family. Moderate and strict
profiles warn; robust and critical profiles may deny typed high-confidence findings.
The AST compatibility analyzer caps itself at warning, marks findings uncertain, and
never attaches a machine-applicable fix. Typed HIR or
CollectionPlan analysis may offer a fix only after receiver semantics, effects, aliasing,
mutation version, ordering, and lifetime are proven.

Human and JSON records preserve stable code, location, evidence, uncertainty, hint, and
optional proof-gated fix. Unknown rule codes remain visible rather than silently
suppressed.

## Shared facts

`PerfFacts` is the function-local owner for reusable MIR analysis. Its first deployed
slice owns CFG successors, predecessors, block indexes, and block count; loop detection
consumes this shared view. Dominance, loop forest, def-use, range/induction, region alias,
effects, and MemorySSA-lite extend the same revision-local owner with explicit
invalidation.

## Current safety containment

- Unknown escape state remains escaping after finalization.
- Auto-vectorization is analysis-only; candidate recognition requires an exact integer
  unit step found in the actual loop header/direct body region.
- Canonical `collection_opt` dispatch is disabled. Retained patterns do not yet prove
  ownership/COW equivalence, alias and memory versions, call effects,
  trapping/allocation behavior, or destruction order.
- Collection hoisting remains inert until it can target a true preheader with complete
  dominance, effects, alias, zero-trip, and speculatability proofs.
- Loop trip counts remain unknown until SCEV-lite proves the complete recurrence.
- Dormant identity and proof-incomplete transforms are absent from effective pipelines.
- Inline facades and target narrowing are classified `Skeleton`; read-ahead hoisting is
  `AnalysisOnly`. Their presence in a requested pipeline is never transformation proof.
- General fusion, stack promotion, general LICM, BCE, GVN, string-builder rewriting, and
  TCO remain unavailable until their proof contracts pass.

See [the architecture](../../04_architecture/simple_compiler_performance_memory_efficiency.md)
and [system-test plan](../../03_plan/sys_test/simple_compiler_performance_memory_efficiency.md).
