<!-- codex-design -->
# Collection planner detail design

Status: draft with balanced NFR targets selected; executable system scenarios
remain pending.
Architecture: `doc/04_architecture/collection_planner.md`.
NFR: `doc/02_requirements/nfr/collection_planner.md`.

## Interfaces and storage

- Keep `CollectionPlan`, `CollectionPlanNode` and the current validator in
  `35.semantics/perf/collection_plan.spl`. Node IDs remain dense topological
  indices; append-only extraction rejects forward inputs and cycles.
- Add `CollectionRegistrySnapshotV1` loaded once from
  `config/compiler/collection_operations.sdn`. Each row binds resolved symbol,
  receiver shape, operation, effect, expected/worst cost, cardinality,
  allocation, order, backend availability and an evidence receipt. A
  nonmatching or duplicate row is a startup/config error, never a guessed op.
- Add `CollectionProofV1` with individual `effects`, `alias`, `escape`,
  `equality`, `order`, `duplicate`, `memory` and `target` witnesses. A witness
  includes a reason and producer version, so a later pass can reject stale
  facts. Unknown facts remain explicit.
- Add `CollectionPhysicalPlanV1` as a tree of `Original`, `FusedLoop`,
  `NestedLookup`, `HashLookup`, `MergeLookup` and `DirectIndex` operations.
  Estimated build/probe/output work and peak memory are fields, not comments.
  The plan carries a fallback edge and source span for diagnostics.
- `TypedSeries<T>` holds typed values and an explicit missing mask. Its
  f64/i64 adapters convert to the existing dynamic `Series` and check runtime
  DType and mask length on conversion back. The numeric join index remains
  the specialized f64/i64 path; generic key indexes use `Hash + Eq` only after
  the parity gate. `map_values`, `filter_present`, `any_present` and
  `all_present` skip callbacks on missing rows; `any_present` and `all_present`
  short circuit. Richer column error details remain required before REQ-001
  is complete.

## Pipeline

1. Resolve method symbols and collect typed HIR facts once per function. Reuse
   the admitted registry snapshot, never method-name text alone.
2. Extract a logical plan from a chain or recognized loop. Record the original
   HIR region as an exact fallback. Structural validation happens before
   proofs or cost estimation. For `DistinctBy`, use the resolved callback
   function return as the key type; an untyped callback leaves an explicit
   `key type` blocker in the logical plan.
3. Derive effect/alias/equality/order/duplicate/cardinality witnesses. A failed
   witness records a blocker and keeps the original region.
4. Enumerate legal physical candidates. Estimate `build + probe + output` work,
   peak memory and worst-case bounds. Use target/key-specific thresholds from
   measurements; a profile may refine estimates but cannot legalize a plan.
   Reject plans above the memory cap, and compare surviving candidates against
   the balanced NFR gates: 10% wall-time, 20% peak-RSS and 5% warm compiler
   startup/request regression limits.
5. Lower the selected candidate in `50.mir` to ordinary MIR. Single-input
   map/filter chains become one counted loop with one output builder.
   Semi/anti joins construct and probe an index only after legal duplicate and
   ordering proofs. Preserve short-circuit and exception edges.
6. Verify generated MIR plus receipt in `60.mir_opt`. On verification failure,
   discard the candidate, emit a diagnostic, and lower the original region.
   Backend emission sees normal MIR, never an unverified planner node.
7. Record plan selection, blockers, timings and allocations for explain output
   and `.sprof` collection counters. The profile format is versioned; stale
   records are ignored with an explicit reason.

## Failure behavior and cache

Malformed registry or missing runtime symbol fails the build early with a
source-located configuration error. Unsupported source shape, unknown effect,
unproven equality/order, memory cap, stale profile or backend limitation
selects `Original` and may emit a typed `COLL` diagnostic. No optimizer path
silently changes a duplicate policy or callback execution count.

Plan cache key: typed function hash, callee-summary hashes, registry version,
target/backend capability hash, planner policy version and profile epoch.
Invalidate only affected functions on a key change. Register lookup is O(1)
by resolved symbol; extraction is O(HIR nodes) and candidate enumeration is
bounded per plan node. Hot compilation makes no filesystem or process calls.

## Shared scenario helpers

System spec path: `test/03_system/app/compiler/feature/collection_planner_spec.spl`.
Use `step("prepare typed collection fixtures")`,
`step("compile the same program in each engine")`,
`step("inspect the selected collection plan")`, and
`step("compare results and operation counts")` as visible flow names.
Helper names: `collection_fixture_path`, `run_collection_program`,
`collection_plan_receipt`, `assert_engine_parity`, and
`measure_collection_scaling`. Any not-yet-implemented helper must fail fast
with `assert(false)` until replaced by executable behavior. Built-in matchers
only. The generated manual should show these user-visible flows and fold the
engine/edge matrix details.

## 2026-10-03 concrete TDD and evidence contract (Codex)

The canonical scenario IDs and executable acceptance list belong to
`doc/03_plan/sys_test/collection_planner.md`. IDs CP-001-A/B/C through
CP-011-A/B/C map to the corresponding requirement's normal, edge and rejection
cases; CP-GUARD-01–06 are focused selector/explain checks and do not establish
production completion. Preserve the existing helper
names above across isolated worktrees. Every helper calls production behavior
or explicitly fails; fixture strings, expected arrays and hand-authored
receipts cannot substitute for compilation and execution.

### Concrete fixtures and assertions

| Requirement | Fixture and exact observation required |
|---|---|
| REQ-001 | Values [10,20,30], missing [false,true,false]: map +1 yields present values 11 and 31 with the same missing row; callback count is 2. Mask/value length mismatch and wrong dynamic dtype return errors. All-missing any is false and all is true with zero callbacks. Exercise sync and async families, integer and floating adapters. |
| REQ-002 | Map/filter/flat-map, any/all early exit, captured and noncaptured callbacks, Dict overwrite and absent lookup execute in interpreter, JIT, LLVM AOT, self-hosted native and bootstrap routes. Compare ordered output and callback/error trace; record unsupported engine as failure, not parity. Bootstrap route evidence does not authorize using the Rust seed as ordinary tooling. |
| REQ-003 | Register duplicate symbol IDs and mismatched receiver/signature/version/backend symbols; assert rejection and source-located diagnostics. Compile twice with an unchanged registry to observe one load; change its version to require invalidation. |
| REQ-004 | Input [3,1,3,2,1] gives unique [3,1,2] and groups in first-seen key order with original member order. Count key/hash work at the four selected sizes; explicit unsupported-hash fallback must preserve results. |
| REQ-005 | Text, integer, enum, tuple and interned-symbol keys: deliberately colliding unequal keys remain separately retrievable, equal keys overwrite according to contract, absent keys stay absent, and resize retains entries. Run the same fixtures across engines. |
| REQ-006 | Equivalent nested-loop and functional membership programs report the same cost class, each with its own correct source span. Bounded intentional loops state their bound; unresolved receiver/effect evidence reports unknown instead of an indexed claim. |
| REQ-007 | Equivalent typed loop and unary chain normalize to equivalent operation/fact DAGs. Invalid source IDs, forward edges, disconnected output, unknown key type and chain bound overflow are rejected with reasons. Same-spelled user methods are not builtin operations. |
| REQ-008 | Eligible pure map/filter pipeline produces the baseline result with one generated MIR loop, no intermediate collection and no closure allocation. Mutating/throwing/suspending/aliasing callbacks preserve the original callback/error trace through fallback; eager map/filter interleaving must not change. |
| REQ-009 | Left keys [2,1,2], right keys [2,2,3]: semi yields both original left rows with key 2; anti yields key 1; all-match join yields four pairs in declared original order. Distinct/frequency/intersection and first/last policies get independent oracles. NaN never matches and signed zeros match. Test nested/hash/merge/direct-index eligibility and each rejected alternative. |
| REQ-010 | Admit matching collection observations, then alter function hash, target/backend, registry version and profile epoch independently. Each stale profile leaves correct original/static execution with an explicit reason. Negative, overflowing and malformed counters fail admission. |
| REQ-011 | Explain binds source, registry, target, proof and profile identities to selected/rejected alternatives, costs and memory. Compilation produces the matching MIR receipt, and execution counters prove that artifact ran. Corrupt/stale receipt cannot be used as optimization evidence. |

### Implementation dependency order

1. Capture a real failing focused fixture before changing production code.
   First admit runner and REQ-002 semantics, then typed library and generic
   index behavior. Commit failure command/exit evidence alongside the
   subsequent successful focused run, with source revision identities.
2. Load the versioned registry into the production typed pipeline and certify
   backend symbols. Feed both diagnostics and extraction from that snapshot.
3. Extend extraction to typed loops, then add operation-specific proof and
   cost/memory admission. Test unknown, invalid and overflowing facts first.
4. Wire lowering only for admitted candidates; retain exact original regions
   for rejection. Validate emitted MIR and prove execution before enabling a
   rewrite for users. Library index speedups do not complete compiler lowering.
5. Add guarded profile records and cache invalidation, then full differential,
   scaling and responsiveness evidence. Keep unsupported REQ entries open.

The NFR fixtures use 1,000/2,000/4,000/8,000 rows and retain equality/hash/
comparison/build/probe/emission counts. Bound output multiplicity for the
<=1.15 exponent gate; separately assert n*m output on all-equal all-match
joins. Wall-time and peak-RSS gates require at least five measured warm runs
against the same-revision unoptimized baseline, with raw samples and medians.
A single elapsed time, constant counter or receipt snapshot is insufficient.

For every TDD slice, record the real red result, minimal production change,
focused green result and affected requirement IDs. Missing executables,
unsupported syntax and unavailable engines are infrastructure failures until
diagnosed; they do not establish the intended semantic red. Reuse passing
checks and stop after the session's bounded repair cycles.
