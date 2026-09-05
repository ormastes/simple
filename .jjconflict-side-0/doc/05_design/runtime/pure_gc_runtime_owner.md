# Pure-Simple bounded GC owner

**Status:** host-independent implementation; executable deployment evidence
remains pending the current pure-Simple compiler.

`src/lib/gc_async_mut/pure/runtime.spl` provides a small, deterministic owner
for callers that need a pure-Simple runtime capsule. It is deliberately not a
replacement for the hosted GC in `src/app/gc/` and does not pretend to infer
roots from arbitrary Simple values.

## Ownership contract

`PureGcRuntime` is a reference owner (a `class`) with a fixed array of at most
64 slots. A caller receives only the copied, scalar-only
`GcHandle(owner_id, id, authorization)` bearer. The `id` packs a slot index and
a nonzero generation. The runtime accepts the bearer only when its owner,
slot, generation, and per-allocation authorization all equal the live slot
record. Equal `RuntimeValue` payloads are allocated in separate slots and
therefore receive separate bearers.

The explicit lifecycle is:

```text
Free --alloc--> Live --release--> Unreachable --collect--> Free(generation+1)
                         \--dealloc--> collect (eager reuse)
```

`get` rejects `Unreachable`, `Free`, retired, wrong-runtime, malformed,
wrong-authorization, and stale handles. An exact copied bearer intentionally
retains authority until `release`/`dealloc`; this deterministic pure owner is
not a cryptographic capability boundary. A generation at
`0x7ffffffffffff` retires its slot rather than wrapping. That value is the
largest generation whose 4096-stride encoding, including slot 63, remains a
positive signed `i64`. Exhaustion returns the all-invalid
`GcHandle(owner_id: 0, id: -1, authorization: 0)` and never fabricates a live
object.

`collect` only sweeps slots explicitly released by the owner. This is a sound
bounded policy: copied handles are treated as roots until the owner revokes
them, and no pointer scanning or guessed reachability is hidden in the pure
implementation. `PureGcStats` reports live, pending-reclamation, retired, and
available slot counts as well as allocation/free totals, collection count,
and capacity. Negative and zero requested capacity create a zero-slot owner;
requests above 64 clamp to 64.

## Compatibility and isolation

The existing free functions `alloc`, `dealloc`, `gc_collect`, and `gc_stats`
route through one lazily initialized module-owned default runtime for
compatibility. Lazy initialization avoids the freestanding backend's unsafe
module-global call-expression initializer. `RefCount` was removed: copied
bearers do not pretend to implement reference counting, and explicit owner
revocation is the lifecycle authority.

New code that needs an isolated owner should call
`pure_gc_runtime_new(capacity)`. Owner and authorization identities come from
process-local scalar counters. The counters, isolated owners, and compatibility
owner are deliberately **not thread-safe**. Keep each runtime in one execution
domain. Cross-task use requires an external owner actor/lease protocol that
serializes every operation; this module makes no concurrent-GC claim.

The focused contract is in
`test/01_unit/lib/gc_async_mut/pure_runtime_spec.spl`. It covers duplicate
allocation identity, cross-owner and malformed bearer rejection, bounded
exhaustion and generation reuse, stale/idempotent free, lifecycle statistics,
zero/negative/oversized capacities, signed-`i64` generation packing, and the
lazy compatibility owner. The mirrored manual is
`doc/06_spec/01_unit/lib/gc_async_mut/pure_runtime_spec.md`. The source check is
host-independent; running the executable spec requires a deployed pure-Simple
compiler.
