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
- General fusion, stack promotion, general LICM, BCE, GVN, string-builder rewriting, and
  TCO remain unavailable until their proof contracts pass.

See [the architecture](../../04_architecture/simple_compiler_performance_memory_efficiency.md)
and [system-test plan](../../03_plan/sys_test/simple_compiler_performance_memory_efficiency.md).
