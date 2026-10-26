# Typed DataFrame-able collections and collection planner

Status: selected full scope by the user's “fully impl” objective. Source:
`doc/01_research/compiler/collection_planner/collection_plan_ir_2026-07-31.md`
and the 2026-09-27 local/domain research. P7 research topics are outside this
implementation requirement unless separately selected.

## Functional requirements

- **REQ-001 Typed collections and DataFrame columns.** Expose typed column and
  collection operations with static element/key types while retaining explicit
  missing-value behavior and the existing numeric DataFrame API. Numeric keys
  must preserve stable duplicate order, NaN non-match, signed-zero equality,
  and first/last/unique policies where applicable.
- **REQ-002 Cross-engine semantic substrate.** Map/filter/flat-map/any/all,
  closure construction and invocation, and built-in Dict insertion/lookup must
  agree across interpreter, JIT, LLVM AOT, self-hosted native and bootstrap
  routes before source lambda fixes or synthesized Dict indexes are enabled.
  Every referenced runtime symbol must have a matching implementation.
- **REQ-003 Collection operation registry.** One versioned, machine-readable
  registry must bind resolved operations to receiver/key types, effects,
  cardinality, expected and worst cost, allocation, order, and backend support.
  Lint, planner and backend symbol checks consume this source of truth.
- **REQ-004 Standard-library complexity.** Replace quadratic `unique` and
  `group_by` implementations with proven indexed algorithms when keys permit,
  preserving first-seen order and duplicate behavior. Audit related array
  operations and retain explicit fallbacks where hash/equality is unavailable.
- **REQ-005 Generic index substrate.** Provide and certify generic `HashMap`
  and `HashSet` behavior for text, integers, enums, tuples and interned symbols,
  with explicit hash/equality contracts and collision tests across engines.
- **REQ-006 Typed complexity diagnostics.** Extend the existing `COLL`
  namespace with typed cost, join/index candidate and regression diagnostics.
  Functional chains and explicit loops must receive equivalent complexity
  analysis; diagnostics explain assumptions and intentional bounded cases.
- **REQ-007 Logical CollectionPlan.** Extract typed loops and functional
  chains into one validated semantic DAG carrying effects, cost, cardinality,
  order, uniqueness, memory, source span and proof receipts. Unknown facts are
  represented explicitly and do not authorize a rewrite.
- **REQ-008 Fusion and lowering.** Legally fuse eligible pipelines into one
  MIR loop without intermediate collections or closure allocation. Preserve
  callback count/order, exceptions, mutation, aliasing, short-circuit,
  suspension, allocation behavior and observable output on every backend.
- **REQ-009 Equality-key planning.** Generate nested, hash, merge and direct
  index candidates for proven semi/anti joins, first/all matches, frequency,
  distinct and intersections. Select by estimated total work and memory,
  including output cardinality. Preserve ordering and duplicates or reject a
  candidate with an explainable reason.
- **REQ-010 Profile-guided adaptation.** Extend `.sprof` with collection
  cardinality/selectivity observations and choose guarded physical plans using
  backend/key/target-specific evidence. Missing or invalid profiles retain the
  correct original plan.
- **REQ-011 Plan explanation and verification.** Expose original and selected
  complexity, alternatives, proof blockers, memory and profile evidence.
  Differential execution, exact semantic edge cases and scaling tests cover
  every algorithm-changing rewrite; generated SPipe manuals trace each REQ.

## Ordering and acceptance

REQ-002 precedes lambda-facing source fixes and Dict index synthesis.
REQ-005 precedes hash-backed REQ-009. REQ-003/007/008 require production
pipeline invocation, not stand-alone type definitions. The feature is complete
only when REQ-001–011 have implementation and executable evidence, required
architecture/design/spec artifacts are current, and `/verify` reports PASS.
