# SimpleRing Async Base: Concurrency and Resource Linearization Evidence

Date: 2026-08-26  
Scope: AC-12 / SimpleRing V1 hosted reference implementation  
Evidence status: **bounded model evidence; not a universal formal proof**

## Claim boundary

This report supports the safety design for one mutable owner, bounded queues,
exactly one terminal publication, cancellation ordering, and stale-generation
rejection. It combines source inspection, executable implementation tests, and
a finite abstract-state enumeration. It does **not** prove arbitrary capacity,
true simultaneous OS threads, weak-memory behavior, counter/generation
exhaustion, native providers, compiler-generated task frames, or mission
link-time-static storage. Those claims remain release blockers until their own
proof or measured evidence exists.

## Canonical owners and boundary values

| Mutable state | Sole authority | Boundary classification |
|---|---|---|
| Slot lifecycle, generation, SQ/CQ indices, telemetry | `SimpleRing` instance identified by `ring_id` and `owner_id` | Owner-mutated; foreign owner calls fail closed |
| Operation payload | Caller or registered-resource owner | `RingPayloadLease`: explicit lease/handle/generation; no raw pointer crosses the ring contract |
| Submitted operation | Provider after `provider_take[_at]` | Value plus token/lease/metadata; provider receives no queue mutation authority |
| Terminal completion | Ring until owner consumes it | Value copied into bounded CQ; exact `task_key` is the wake handle |
| Mission capacities | Mission adapter during configuration, then sealed at Ready | Hosted preallocation receipt only; `link_time_static_proven=false` and `allocation_free_proven=false` remain honest |
| Trace events | One `AsyncTraceRing` owner | Fixed-capacity event records with explicit RejectNewest/DropOldest policy |

Cross-domain values are copies, opaque handles, or generation-bound leases.
There is no claimed owned-move implementation in V1. Unknown transfer and raw
host-address transport are outside the admitted contract.

## Linearization map

| Operation | Linearization point | Postcondition / rejection |
|---|---|---|
| Reserve | `_free_pop`, followed by `Empty -> Reserved` under the recorded owner | Full rejects before mutation; occupancy is finite |
| Commit | `Reserved -> Committed` plus one SQ index publication | This is the first point at which a provider may observe work |
| Provider take | SQ head removal and `Committed -> InFlight` | Empty returns `nil`; a slot cannot be taken twice |
| Precommit cancel | `Reserved -> Empty` through `_release_slot` | Generation advances; the old reservation becomes stale |
| In-flight cancel request | First `cancel_requested=false -> true` | Later ordinary completion is rejected with `CancellationRequired`; repeated request is rejected |
| Terminal publication | `_complete` changes `InFlight -> Terminal` and appends one CQ index | Duplicate/conflicting terminal attempts reject with `TerminalAlreadyPublished` |
| Completion consumption | CQ head removal followed by `_release_slot` | Slot returns to free queue and generation advances exactly once |
| Reset | Precheck all generations, then invalidate every slot and rebuild bounded queue indices | Old tokens/submissions fail generation validation; no partial reset on exhaustion |

The implementation is deliberately single-mutator. These points define a
serial specification for adapters that later introduce synchronized remote
ingress; they are not a claim that the current class itself is thread-safe.

## Resource accounting

For configured capacity `C`, construction creates exactly `C` entries in each
slot-parallel array and exactly `C` indices in each free/SQ/CQ array. Runtime
queue counters are bounded by `C`; reserve fails when `free_count == 0`, and a
terminal slot remains occupied until the owner consumes its CQ entry. Batch
commit prevalidates count and capacity before the first mutation. Ring counter
telemetry saturates rather than wrapping. Generation exhaustion fails closed
before release/reset mutation.

This proves an explicit storage *shape* in the source, not zero runtime heap
allocation: the hosted implementation allocates arrays during `create`.
Mission Ready/static-storage proof is therefore intentionally absent.

## Executable evidence

| Evidence | Covered behaviors |
|---|---|
| `test/01_unit/lib/nogc_async_mut/async_ring/simple_ring_spec.spl` | owner rejection, full/empty, generation reuse, batch admission, cancellation, payload lease, reset, stale and duplicate rejection |
| `test/02_integration/lib/async/simple_ring_async_base_concurrency_spec.spl` | independent progress, exact wake identity, bounded saturation, reset/delayed completion, cancellation/terminal interleavings |
| `test/00_formal_verification/runtime/simple_ring_async_base_bounded_model_spec.spl` | all 117,649 length-six traces over seven abstract actions for a capacity-one slot |

The bounded model enumerates reserve, commit, provider take, cancellation,
ordinary terminal, cancelled terminal, and completion consumption. After every
prefix it checks capacity-one occupancy, `consumed <= terminals <= admitted`,
exactly one outstanding terminal iff the phase is Terminal, and one generation
advance per release. This is useful exhaustive finite-state evidence. It is not
a refinement proof connecting every concrete source line to the abstract model,
nor an induction over arbitrary trace length/capacity.

## Remaining proof obligations

1. Mechanized refinement from concrete ring arrays/cursors to the abstract
   state machine, including arbitrary positive `C` and generation exhaustion.
2. A synchronized remote-ingress implementation plus real threaded race and
   memory-order evidence; until then the API remains single-owner only.
3. Native provider parity, delayed completion/reset fault injection, and
   cancellation/durability boundaries for device rings.
4. Allocation/RSS receipts after admission and true static pool/link-time
   topology evidence for `mission_pool`.
5. Fairness, deadlines, overload scheduling, and liveness proofs. The present
   evidence establishes bounded safety properties, not starvation freedom.

