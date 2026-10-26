<!-- codex-design -->
# Collection planner architecture

Status: design in progress, 2026-09-27. Functional scope is REQ-001–011 in
`doc/02_requirements/feature/collection_planner.md`; balanced performance
targets are selected in `doc/02_requirements/nfr/collection_planner.md`. The
executable SPipe and generated manual remain required before this design can
be marked complete.

## Decision and alternatives

Use a typed logical `CollectionPlan` between HIR and MIR, then lower a selected
physical candidate into ordinary MIR. A direct MIR-pattern-only design cannot
recover callback effect, source ordering or key equality reliably after HIR
erasure. A runtime-only DataFrame query engine cannot optimize explicit Simple
loops or preserve compile-time diagnostics. A typed HIR plan allows both source
forms to share proofs while existing MIR/backends remain the execution target.

The planner is fail-closed: missing facts select the original execution. A
physical rewrite is enabled only by a proof receipt containing operation
identity, effect/alias/order/equality/escape facts, target capabilities and the
registry version. No source lambda fix or Dict synthesis runs before REQ-002's
cross-engine gate.

## Layer ownership and data flow

1. `src/compiler/35.semantics/perf_facts/` owns resolved operation summaries,
   registry load/validation and typed HIR collection/cost facts. Its registry
   comes from `config/compiler/collection_operations.sdn`, versioned and checked
   against runtime/backend symbols.
2. `src/compiler/35.semantics/perf/` owns `CollectionPlan`, loop and unary-chain
   extraction, symbolic cost algebra, legality and candidate enumeration. The
   extractor never chooses a hash merely because a call is pure.
3. `src/compiler/50.mir/` consumes a validated plan through a narrow
   plan-lowering entrypoint. It emits ordinary MIR loops, short-circuit edges,
   builders and index operations, plus a plan receipt. The unchanged HIR route
   remains available as a guarded fallback.
4. `src/compiler/60.mir_opt/` verifies the receipt against MIR and performs
   local fusion/cleanup; it consumes MIR-level metadata and does not rederive
   HIR ownership from strings. Backends receive normal MIR and do not invent
   planner semantics.
5. `src/lib/nogc_sync_mut/` owns generic map/set and typed DataFrame facades;
   the async family mirrors APIs without sharing mutable state. Runtime/FFI
   owns hash and equality ABI behavior. Numeric DataFrame index policy remains
   explicit and separate from generic hash assumptions.
6. `.sprof` collection records feed a later optional physical choice. Invalid,
   stale, or absent profiles leave static legal choices or original execution.

The driver wires one registry snapshot and one planner instance per compilation
request. Registry validation occurs once at startup or cache load, not on each
function. Plans are cached by typed function/HIR hash, callee summary hashes,
registry version, target capability and planner policy version. Changing any
component invalidates the affected plan and its receipt. No hot path performs a
full-tree scan, repeated source read, subprocess call or retry sleep.

## Plan and proof contracts

`CollectionPlanNode` retains typed source binding, resolved symbol ID, input
node IDs, key/output types, effects, expected/worst cost, cardinality, order,
uniqueness, allocation, alias/escape facts and source span. The DAG validator
checks shape, acyclicity, typed source/operation bindings and a connected path
to the final output. Missing key types remain explicit proof blockers. New
legality checks must prove operation
specific conditions: callback count/order, throwing behavior, suspension,
mutation, equality and hash consistency, duplicate multiplicity, first-seen
order and output size. Unknown facts are explicit blockers.

Physical candidates are `Original`, `FusedLoop`, `NestedLookup`, `HashLookup`,
`MergeLookup` and `DirectIndex`. Cost comparison includes build + probe +
output emission + memory; expected and worst bounds stay distinct. Small or
poorly estimated inputs can retain nested lookup. A candidate requiring more
memory than the selected NFR budget is rejected before MIR lowering. Explain
output shows each rejection reason and evidence source.

Numeric DataFrame columns use typed wrappers with explicit missing masks and
conversion into the existing dynamic DataFrame. The numeric join index keeps
stable duplicate chains; floating NaN is nonmatching and signed zeros compare
equal. Generic HashMap/HashSet keys use declared `Hash + Eq`; no key is indexed
without cross-engine hash/equality parity evidence.

## MDSOC and module boundaries

The planner is a compiler feature capsule: public interfaces are the registry
snapshot, logical plan, proof receipt and MIR lowering request. HIR storage and
MIR builder internals stay private to their owning layers. A feature transform
at the driver pipeline composes registry loading, diagnostics and optional plan
lowering without altering unrelated backends. The DataFrame compatibility
adapter bridges typed columns to the existing dynamic API; it does not make
backend state global. Runtime index data is owned by the executing collection
and may not cross task/actor boundaries without the repository's ownership
transfer rules.

## Verification and observability

Every REQ maps to a real executable SPipe scenario. Differential fixtures run
the same program through all required engines, including empty, duplicate,
missing, NaN, signed-zero, collision, mutation and throwing callbacks. Scaling
tests count equality/hash operations and measure wall time/RSS; operation
counts distinguish algorithmic change from noisy timing. Planner telemetry
records extraction time, selected/rejected candidates, cache hits, invalidation
reason, generated loop count and intermediate allocations. Cold startup, warm
startup, request latency and max RSS are measured on realistic fixtures using
the selected balanced NFR profile. `/verify` must reject placeholder tests and
unsupported REQ claims before release.
