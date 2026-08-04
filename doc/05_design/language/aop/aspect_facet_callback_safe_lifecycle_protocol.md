<!-- codex-design -->
# Callback-safe aspect lifecycle ownership protocol

Status: implemented; static/source verification complete, threaded and
executable runtime evidence pending.

This addendum refines REQ-AF-008 for concurrent lazy activation, facet leases,
prepared advice, and unload. It does not replace the canonical
`LifecycleManager`, loader registries, or activation coordinator.

## Decision

Use two distinct coordinators with non-overlapping responsibilities:

1. `AspectLazySingleFlight` owns duplicate lazy-work identity, completion, and
   follower wakeup. The current implementation permits only one active flight
   per context, so different routes are conservatively serialized. Per-route
   parallelism is a performance follow-up, not a correctness claim.
2. `AspectLifecycleGate` serializes short reads or commits of the canonical
   application context: coordinator, lifecycle, publication registries,
   projection, loader, and provider cache.

No application I/O callback or advice callback runs while
`AspectLifecycleGate` is owned. Canonical generation pins are committed before
advice callbacks start, so unload may quiesce concurrently but cannot reclaim
the mapped owners until finalization releases those pins.

This is a serialized-state/leased-callback pattern. It is preferable to a
reentrant mutex: reentrancy would permit a callback to observe half-installed
state, while a non-reentrant mutex held across the callback deadlocks ordinary
facet or advice re-entry.

## Invariants

- `LifecycleManager` is the only generation/pin authority.
- Registry and lifecycle values returned from a loader operation are installed
  together while the lifecycle gate is owned.
- A callback permit contains immutable addresses and opaque canonical
  `GenerationToken` values; it is not a publication snapshot or second refcount.
- A permit is invoked at most once and finalized exactly once on every returned
  success/error path.
- Finalization releases tokens against the current canonical lifecycle, never
  against the prepare snapshot.
- Counter updates are deltas merged into the current registry. Finalization
  never replaces a registry with a stale pre-callback copy.
- Unload removes visibility and marks the generation quiescing under the gate.
  It reclaims owners/cache entries only when the canonical lifecycle reports
  drained.
- Lazy I/O failure reacquires the lifecycle gate, removes only its reservation,
  releases the gate, then publishes the shared single-flight failure.
- Panic/unwind cleanup is not claimed. Current Simple native callback execution
  has no catch/unwind boundary; a panic is fail-stop. Callback ports that return
  to the runtime must express failure as `Result`.

## Implemented owners and APIs

### Application lifecycle gate

Owner: `app.startup.aspect_lifecycle_gate`.

```simple
class AspectLifecycleGate

fn aspect_lifecycle_gate_create() -> AspectLifecycleGate
```

The gate is an identity/container only. `AspectExecutionContext` calls
`mutex_with_lock_keeping(context.lifecycle_gate.mutex, 0, body)` directly.
This single cross-module hop lets the mutex module invoke the application
closure without forwarding it through a gate-module trampoline; the latter is
a documented interpreter deadlock shape. Simple has no evidenced peer-only
field visibility, so the mutex field is owner-only by convention and the gate
is not re-exported by the startup facade. The body is restricted to
callback-free canonical-state work; application I/O and advice invocation
occur between separate scopes.

Simple currently has no catch/unwind boundary. A panic inside the body is
process fail-stop, not a recoverable cleanup path; the design does not claim
that execution can continue or that the mutex is reusable after panic.

`AspectExecutionContext` owns one gate independently of its lazy single-flight
table. Callback-free public operations enter/leave it:

- active facet lookup plus exact generation pin;
- facet descriptor validation/address lookup;
- generation/descriptor release;
- activation reservation and activation commit;
- visibility removal, quiesce, drain check, and unload reclamation;
- prepared-advice prepare and finalize.

Private `_under_lifecycle_gate` helpers make ownership explicit and prevent a
public gated method from recursively acquiring the gate.

### Prepared advice split

Owner: `compiler.loader.loader.advice_binding_registry`.

```simple
struct AdviceDispatchPermit:
    slot_id: text
    form: text
    entries: [AdviceDispatchProjectionEntry]
    tokens: [GenerationToken]

struct AdviceDispatchPrepareOutcome:
    registry: AdviceBindingRegistry
    lifecycle: LifecycleManager
    permit: AdviceDispatchPermit?
    status: text
    reason: text
    tokens_acquired: i64

struct AdviceDispatchInvocationReceipt:
    status: text
    reason: text
    return_values: [i64]
    invoked_count: i64

fn advice_dispatch_projection_prepare(
    projection: AdviceDispatchProjection,
    registry: AdviceBindingRegistry,
    lifecycle: LifecycleManager,
    loader: ModuleLoader,
    slot_id: text,
    form: text
) -> AdviceDispatchPrepareOutcome

fn advice_dispatch_permit_invoke(
    permit: AdviceDispatchPermit
) -> AdviceDispatchInvocationReceipt

fn advice_dispatch_projection_finalize(
    registry: AdviceBindingRegistry,
    lifecycle: LifecycleManager,
    permit: AdviceDispatchPermit,
    receipt: AdviceDispatchInvocationReceipt
) -> AdviceProjectionDispatchOutcome
```

`prepare` validates form/schema, derives the exact ordered chain, validates
registry/projection/loader identity, acquires every token, and returns the
updated registry/lifecycle. If prepare fails, it releases any partial token set
before returning and includes the failure counter delta.

`invoke` reads only the immutable permit. It does not receive the context,
registry, lifecycle, loader, cache, or gate. It calls each address once in
canonical order and returns a receipt.

`finalize` releases permit tokens in reverse order from the current lifecycle
and merges invocation/failure counter deltas into the current registry. Token
release failure is fail-closed and is reported without installing stale state.
The permit type remains loader-private; compiler-generated code calls only the
context ABI.

The current monolithic `advice_dispatch_projection[_with_invoker]` remains as a
compatibility composition of prepare/invoke/finalize only for callers that own
an isolated lifecycle value. `AspectExecutionContext` must use the split API.

## Exact application call graph

### Lazy facet acquisition

```text
acquire_or_activate_facet_descriptor
  -> lazy_singleflight.begin(route)
  -> mutex_with_lock_keeping(lifecycle_gate.mutex, 0, \: # lazy-preflight
       acquire_published_facet_descriptor_under_lifecycle_gate
       coordinator.reserve (owner only)
       install reserved coordinator)
  -> pack_io.load_exact_route                    [callback; no lifecycle owner]
  -> mutex_with_lock_keeping(lifecycle_gate.mutex, 0, \: # lazy-commit
       revalidate reservation + catalog generation + policy
       activate_pack_bytes_under_lifecycle_gate [decode/map/publish; no app callback]
       acquire descriptor lease)
  -> lazy_singleflight.complete_success/failure
```

Same-route followers receive the matching flight's shared typed completion.
The current context-wide flight owner also serializes different routes. Facet
release, unload, and advice prepare/finalize are not blocked during pack I/O.
Synchronous port-callback re-entry for the same lazy route is prohibited by the
port contract: no canonical thread/task activation identity exists yet, so the
runtime cannot reject it deterministically and such re-entry would wait on its
own flight. Embeddings must not perform it.

### Already-active facet acquire and release

```text
compiler context ABI
  -> mutex_with_lock_keeping(lifecycle_gate.mutex, 0, \: # facet acquire/release
       registry lookup + canonical token acquire/release)
```

Each caller receives its own lease. Single-flight success never shares a lease.

### Prepared advice

```text
prepared_advice_dispatch_context_invoke
  -> mutex_with_lock_keeping(lifecycle_gate.mutex, 0, \: # advice prepare
       advice_dispatch_projection_prepare(current state)
       install returned registry + lifecycle)        [pins are now canonical]
  -> advice_dispatch_permit_invoke               [callbacks; no lifecycle owner]
  -> mutex_with_lock_keeping(lifecycle_gate.mutex, 0, \: # advice finalize
       advice_dispatch_projection_finalize(current state, permit, receipt)
       install returned registry + lifecycle)
  -> return receipt values/error
```

A callback may acquire/release a facet, trigger a different lazy route, or
request unload. Unload sees the canonical advice pins and can only reach
`quiescing`; finalization releases the pins, after which a later unload call may
reclaim the generation.

### Unload

```text
unload_published_aspect
  -> mutex_with_lock_keeping(lifecycle_gate.mutex, 0, \: # unload
       authorize; remove facet/advice/projection visibility; quiesce
       if pinned: commit quiescing state and return "quiescing"
       else: validate cache pins; unmap owners; release/invalidate cache;
             complete lifecycle unload; remove publication)
```

No unload wait loop is added. Waiting while owning the lifecycle gate would
prevent advice finalization and facet release.

## State transitions and merge rules

| Phase | Gate | Canonical mutation | Callback allowed |
|---|---|---|---|
| lazy reserve | owned | coordinator reservation | no |
| pack I/O | free | none | Result-only port |
| activation commit | owned | loader/cache/registry/lifecycle | no |
| advice prepare | owned | tokens + lookup/attempt counters | no |
| advice invoke | free | none | yes |
| advice finalize | owned | token release + result counters | no |
| facet acquire/release | owned | token maps | no |
| unload | owned | visibility/lifecycle/cache/loader | no |

Counter merging uses explicit increments (`attempts`, `invocations`,
`failures`, `around_rejections`, lookup hit/miss) rather than assignment from a
permit snapshot. Registry records, active publications, and projection rows are
never copied back by finalization.

## Failure protocol

- Prepare failure: release partial pins inside prepare, commit returned current
  state under the gate, return the stable E-AF010 error; no callback occurs.
- Callback `Err`: finalize under the gate, release all pins, merge one failure
  plus completed-invocation evidence, return E-AF010.
- Finalize release failure: preserve the lifecycle returned by the reverse
  release sweep, record one failure, and return a diagnostic listing every
  failed token release. Never retry callbacks.
- Lazy I/O `Err`: cancel the exact reservation under the gate, then wake all
  matching followers with the same typed error.
- Activation commit failure: roll back only transaction-owned loader/cache
  material under the gate, clear the reservation, then complete the flight.
- Do not invoke callbacks or wait for external progress from a lifecycle-gate
  body.

## Required deterministic tests

1. Advice prepare commits a generation pin before invocation.
2. Unload between prepare and finalize returns `quiescing` and does not unmap.
3. Callback re-entry can acquire/release a facet without deadlock.
4. Finalize releases all exact tokens and a subsequent unload returns
   `unloaded`.
5. Callback `Err` releases all tokens and increments failure once.
6. Partial prepare failure releases earlier tokens and invokes no callback.
7. Replay/double finalize fails without changing counters or token maps.
8. Lazy I/O callback can use unrelated facet APIs because the lifecycle gate is
   free; the port contract prohibits synchronous same-route recursion.
9. Concurrent lazy callers perform one port read and one activation commit.
10. Facet acquire cannot observe visibility after unload quiesce commits.
11. Different contexts never share gates, permits, tokens, or counters.

Threaded integration evidence is still required after deterministic state tests:
barrier-controlled advice/unload and lazy/facet interleavings, with bounded
completion time and exact pin/cache/dispatch counters. Static state tests alone
must not be reported as proof of multithreaded safety.

## Implementation status

Implemented source slices are:

1. The independent `AspectLifecycleGate`, separate from lazy-flight state.
2. Advice prepare/invoke/finalize, with native invocation outside the lifecycle
   gate and canonical token/counter installation in the gated phases.
3. `AspectExecutionContext` composition for prepared advice and retryable
   unload/quiesce transitions.
4. Lazy preflight/reservation and commit/revalidation as separate gated phases
   around exact-route pack I/O.
5. Gated facet lease, descriptor, method-address, release, activation, and
   unload operations through private transition helpers.

Barrier-controlled native thread tests and performance evidence remain required
before claiming REQ-AF-008 complete.

Do not implement steps 3–5 by holding a mutex or logical owner across a callback.
Do not add a process-global context, a second generation refcount, busy polling,
or copied-registry replacement after callback return.

## Current gaps

The gate and split protocol are implemented, but static/source checks are not
proof of multithreaded behavior. REQ-AF-008 therefore remains unproven until
barrier-controlled advice/unload and lazy/facet interleavings pass with exact
pin, cache, and dispatch counters.

Construction, `enter_operational`, and configuration mutation (including loader
and pack-I/O installation) remain startup-only operations outside the lifecycle
gate. Policy/catalog reads likewise assume immutable post-construction state.
The lifecycle gate is not reentrant. Synchronous same-route port re-entry is a
prohibited embedding behavior and would self-wait because there is no canonical
task/thread identity detector. Different lazy routes are globally serialized
per context by the current single-flight owner, which is safe but may constrain
performance. Native callback panic has no recoverable unwind boundary and is
process fail-stop; only returned `Result` failures receive guaranteed finalize
cleanup.

The explicit MIR call-terminator contract is now implemented and preserved by
JSON, borrow/optimizer paths, interpreter, and backend consumers. Textual LLVM
can emit `invoke`; native/unsupported targets and the LLVM C-API path reject
unsupported `MayUnwind`. Typed HIR ownership is now present: `@no_unwind`
defaults every function, `@may_unwind` is explicit, async remains orthogonal,
and callable/import/method/function-type propagation feeds a fail-closed MIR
bridge. Ordinary MIR calls admit only `NoUnwind`; `MayUnwind` without a cleanup
successor and invalid metadata fail with E-MIR-UNWIND001, or E-AF007 first when
a facet lease is live.

This does not change the callback rule above. Cleanup-successor construction,
Throw/Resume, typed landing pads, and the production verifier gate now exist
statically. Async cancellation cleanup, LLVM C-API personality/invoke support,
runtime exception representation, and executable verification remain open.
