# Remaining collection capture observations

Scope: bounded source audit after CLI capture/argv integration. This is a wiring
inventory, not runtime evidence or a completion claim. All five metrics below
remain unmeasured. No event implementation or executable unit case was added:
none has both an admitted site identity and a shared observation transport.

## Existing owner boundary

`src/lib/nogc_sync_mut/sffi/collection_capture.spl` exposes begin, size, lookup,
materialization, hash-probe, finish and abort. The process owner in
`src/runtime/runtime_collection_capture_impl.h` uses a lock, active state,
bounded site slots and a fixed six-name metric serialization loop. Preserve
these exports and synchronization. The six names are collection_size,
distinct_key_count, lookup_count, materialization_count, hash_probe_count and
hash_collision_count; unobserved probe pairs are omitted.

`src/compiler/70.backend/backend/interpreter_run_abi.spl` dispatches the four
canonical observation externs into that compiled owner. This bridges interpreter
contexts; it does not provide an arbitrary metric channel. Ordinary interpreted
module globals would create a separate owner and cannot extend this stream.

`src/app/optimize/sprof_collection_profile.spl` admits eleven metric names and
limits filter_selectivity to 0..1000000. Admission is not measurement. It cannot
recover the five missing observations from the existing six values.

## Exact missing wiring

| Metric | Actual event owner and required delta | Blocked contract |
|---|---|---|
| loop_trip_count | Compiler control-flow lowering must attach the collection plan's stable AST site to the loop body entry and completed invocation. Count body entries, including entries ending in continue or break, rather than container size or lookup count. Interpreter and emitted native control flow must call the same observation owner. | No site-bearing loop observation API. `perf/collection_plan_extractor.spl` describes a plan, not an executed iteration; typed backend `InterpreterBackendImpl.exec_stmt`/`eval_expr` is not a native execution counter. |
| join_output_count | The collection join operator's output-commit point must count each produced row, including duplicate multiplicity. A successful membership probe cannot identify output count for arbitrary joins. | No admitted join output event or output operator identity flows into the shared channel. |
| filter_selectivity | `HashMap.filter` in `src/lib/nogc_sync_mut/src/collections/hashmap.spl` and `HashSet.filter` in sibling `hashset.spl` have real predicate invocations and accepted results. Instrument once per invocation with evaluated and accepted counts, after successful completion. | These owners lack AST site/target parameters, and the shared ABI lacks the count-pair event. Define empty-input omission and aggregate counts before deriving fixed-point selectivity; do not average invocation percentages or substitute result size for accepted count. |
| allocation_bytes | Allocation owner must report actual successful backing-storage allocation/reallocation bytes attributed to a collection site, including growth and temporary storage according to a documented accounting rule. `src/runtime/simple_core/core_memory.spl` has allocator/bookkeeping boundaries, but no collection-site attribution. | Existing adaptive array growth does not expose requested/committed bytes with site identity. Global heap deltas include unrelated work; size times element width misses capacity, alignment and metadata. A numeric estimate is not an observation. |
| early_exit_position | The short-circuit operation/control-flow owner must emit its actual examined-element count and an explicit terminated-early indicator on successful completion. Keep exhaustion distinct from a break or successful find. | Existing lookup event carries only found, not examined position or source traversal order. Probe count is a physical hash operation count, not a semantic source position. Need a stated zero/one-based convention and absence on exhaustion. |

## Bounded next implementation contract

Filter observation is the smallest plausible next slice because its pure-Simple
library loops already own both counts. Before editing these loops, establish a
site-aware compiler/library call boundary and an additive shared-owner event
interface carrying both counts, site and target. Keep existing C exports intact.
A pure-Simple compiled owner is viable only after native export/link retention,
one-process ownership and locking are demonstrated; a second mutable singleton
or a same-name replacement export is not an acceptable shortcut.

The new owner must share begin/finish/abort lifetime with existing events, reject
target mismatch and overflow, serialize deterministic site order, and prevent
finish racing with a note from publishing a partial invocation. Define nested
capture behavior before implementing it. Interpreter adapters must enforce
canonical extern ownership, exact value/arity conversion and existing AOP hooks.

Write executable cases before implementation: empty input (selectivity absent),
all reject (0), all accept (1000000), 1 of 3 (specified rounding), differently
sized repeated filters (ratio of totals), predicate failure (no completed
sample), wrong target, counter overflow, abort then new session, and concurrent
note/finish admission. Run identical source through admitted interpreter and
native execution and compare event streams, not merely parsed metric names.
For the other metrics add zero-trip/continue/break loops, duplicate join outputs,
first/last/no-match short circuits, and allocation growth/failure/attribution
cases only after the corresponding owner contracts exist.

No bootstrap or runtime execution was attempted in this audit. P6 remains open;
performance being best effort does not waive observation correctness.
