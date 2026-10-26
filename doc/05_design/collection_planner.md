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
