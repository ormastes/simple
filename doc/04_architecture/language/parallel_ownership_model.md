<!-- codex-design -->
# Parallel Ownership and Parent-Commit Architecture

## Current state

`src/lib/common/structural/mutation/` already owns MutationPlan/receipt conflict vocabulary. `src/lib/common/structural/placement/` owns wire placement and lease vocabulary, while `src/lib/common/compute/placement_contracts/` owns host semantic placement carriers. These must be consumed, never redeclared. Current application transport and borrow paths require the Wave 1 safety gates before they can support optimization claims.

## Target layers

1. `src/lib/common/structural/transfer/` owns frozen transfer records, wire validation, ownership-token semantics, and codecs.
2. `src/lib/common/structural/storage_layout/` owns frozen storage-plan records and mapping/validation vocabulary.
3. `src/lib/common/structural/parallel_commit/` owns result envelopes, ordering/conflict vocabulary, and receipts; it consumes mutation contracts rather than replacing them.
4. Compiler HIR/MIR/borrow layers derive facts and emit semantic operations; they do not own wire enums.
5. Runtime `parallel_app/` implements bounded transport, structured task lifecycle, and receipt capture behind the common contracts.
6. `src/compiler/85.mdsoc/` adapts the common contracts to stage routing; it may not define competing task/transfer/layout types.

## Ownership flow

```text
Owner Snapshot N --FrozenShare/ObjectRef/Copy--> Child task/process
ChildFresh task arena --IsolatedMove/MutationPlan--> bounded result transport
bounded transport --> owner validation/order/conflict/apply --> Snapshot N+1
```

`Local(owner, generation)` may freeze, begin move, begin scoped loan, or free. A move enters `InTransit`; receipt creates `Local(destination, generation + 1)`. A loan returns only at structured scope join. Source access after move is invalid. Device and process boundaries carry a lease/codec/handle, never an ordinary host address.

### Actor admission authority

The scalar-text `std.actor` compatibility path has one scheduler authority per
actor. `ActorRef` contains only the actor identifier and that admitting
`ActorScheduler`; it does not retain a separately callable mailbox handle.
Public send, ask, pending-work queries, and terminal stop therefore resolve
through the same scheduler registry. The scheduler admits a value-copied
`ActorMessage` into the shared bounded `ActorMailbox` and publishes readiness
only after admission succeeds. Unknown, full, and closed actors reject without
ready-queue publication; stop drains work, cancels abandoned reply reservations,
closes admission, and returns true only for the first terminal transition.
The scheduler captures its creating OS-thread identity and all registry,
admission, reply, lifecycle, and dispatch entrypoints fail closed when invoked
from another thread. This makes the intentionally single-threaded execution
domain enforced rather than merely documented; cross-thread producers require
a future synchronized command ingress.

This scalar-text compatibility path cannot transport dynamic heap values.
Native RuntimeValue actor transport remains restricted to validated fixed inline
transfer packets; typed heap/frozen/owned payloads require a future
`TransferEnvelopeV1`-bound endpoint. In the hosted Rust provider,
`rt_actor_try_send` exposes bounded admission and cooperative `rt_actor_stop`
closes the shared sender owners, removes scheduler mailbox admission, wakes a
blocked receive, and preserves joinability. The first stop succeeds, later
stops fail, and `rt_actor_is_alive` reports false afterward. Simple native
`ActorRef.stop()` routes through this checked boundary. This lifecycle contract
does not claim forceful interruption of an already-running handler, and no C
actor provider currently supplies parity.

### Landed parent ingress boundary

`ParentCommitOwnerV1` is the one mutable root authority currently available to
runtime applications. It serializes revision/token metadata together with the
canonical application payload-token root. Candidate publication validates and
orders the complete child batch, applies that payload order to an off-root copy,
verifies the copy against the candidate, then assigns both roots once under the
same mutex. Its mutation receipt records both before/after roots; malformed,
conflicting, or candidate-mismatched batches leave both unchanged.
`ParentCommitFrameInboxV1` is a separate bounded ingress owner:
it validates a Process-to-Parent frame plus its pointer-free `SPRS` result
payload before retaining an independent byte copy. Admission requires both a
frame slot and byte budget; the queue uses a cursor and releases exact retained
bytes on receive. The owner may drain a finite batch and submit it to one
common-engine transition.

`ParentCommitPipedProcessSessionV1` supplies the bounded OS-process adapter for
this ingress. It owns the child handle, polls only through its paired reader,
and has terminal close, cancellation, and natural-exit paths that attempt
native close at most once. The inbox consumes a drained frame and never
recreates a failed/stale child result, so cancellation or rejection cannot
resurrect child-owned work.

A production piped child is paired with a generation-bound inbox. The sole
long-lived `ParentCommitOwnerV1` issues positive generations under its existing
mutex; exhaustion fails closed instead of wrapping. The session constructor
accepts that owner-issued generation and refuses to spawn if it differs from
the inbox binding. Admission rejects a
different generation and rejects a repeated region ID for the lifetime of that
finite session. The inbox capacity is also the session's replay-table ceiling,
so replay defense cannot grow without bound after receives drain queue slots.
Legacy unbound inbox constructors retain reusable queue behavior but are not a
session/replay proof.

`ParentCommitPipedProcessSessionV1` owns one native piped-process handle and its
reader. Callers poll through that owner rather than passing the handle around.
Its close transition closes ingress and releases the native handle at most once;
later closes return the recorded result and expose the same terminal receipt.

## Tree encapsulation and visibility

| Raw layer | Common tree node | Public to parent | Public to next-layer sibling |
|---|---|---|---|
| HIR semantics | `structural/transfer` | transfer-class fact | frozen envelope descriptor only |
| MIR/borrow | `structural/storage_layout` | access/projection proof | plan request, never backend storage internals |
| Runtime | `structural/parallel_commit` | receipt and typed failure | commit port only |
| MDSOC adapters | all three common nodes | routed policy/receipt | selected port facade only |

Sibling layers remain tree-private. Any compiler/runtime shared identifier is extracted into one of these common nodes. No new grammar is required: `mut`, `iso`, `move`, attributes, library APIs, and typed policy are the semantic surface.

## Compiler-owned typed storage authority

Physical projection is admitted only from a compiler-private declaration that
binds a final MIR function/base local to one exact compiler-owned raw allocation,
source revision, fixed record schema/capacity, bounds proof, and the canonical
`StorageLayoutPlanV1`. The runtime region remains owned by its allocation
domain; the declaration is metadata evidence, not a second owner.

Ordinary RuntimeValue arrays, external or ABI-pinned storage, address-observed
data, unknown bounds, and unsupported field widths/layouts cannot enter this
route. MIR lowering will eventually consume an admitted declaration and emit
`mir.storage.project_field.v1` plus its site evidence atomically. The driver
module-qualifies and freezes that evidence before cache lookup and parallel
codegen; workers may only read module-local snapshots.

The v1 producer recognizes only one same-block SSA-shaped chain. A canonical
owned-raw marker must bind the base, allocation bytes, logical type, revision,
and element count. The producer independently verifies a constant index range
and exclusive intermediate uses, then emits an address projection followed by
the original typed value load. Allocation markers are consumed as compile-time
evidence and never reach a backend. Logical projections resolve against their
final LocalIds before generic optimization can renumber them.

The MIR builder is the allocation authority. Its internal owner operation emits
the exact allocation and returns an immutable fact in one call; MIR-opt may
derive a declaration only from that fact. A stable allocation identity is
present in both the instruction and fact/declaration, preventing metadata for
one plan or source revision from being attached to another allocation. The
producer consumes the private operation into `rt_alloc`; it is never a public
intrinsic or ordinary `T[]` representation.

CompileContext owns the module-qualified evidence lifecycle. It validates a
whole producer batch, commits aligned site/evidence rows and rewritten MIR as
one driver transaction, then transitions once from collecting to frozen before
native cache lookup. The frozen identity includes allocation identity,
provenance, source revision, producer contract/pattern, bounds proof, projection
count, plan, and field schema. Codegen may evict MIR payloads, but cannot mutate
the frozen receipt/cache authority.

Logical access evidence constrains which physical choices are legal; selecting
a layout cannot make an access safer. Constant region/range facts may establish
non-overlap for conflict analysis, while typed field paths are descriptive
locality evidence only. Address escape, unknown access, empty or incomplete
classification, and ABI-pinned storage force conservative handling. No access
advisory may authorize ownership transfer, scheduling, disjoint loans,
`noalias`, or alias scopes. A future planner adapter may rank only already-legal
physical choices; that dependency is strictly one-way.

## Migration order

Freeze contracts and diagnostic names; make boundary/borrow facts authoritative; replace unsafe transport and add bounded task lifecycle; add parent commit; then implement typed storage layouts and MDSOC/project pilots. Performance lowering cannot precede the raw-pointer and alias-soundness gates.
