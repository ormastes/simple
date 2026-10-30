# Real TLDR caller migration: ownership and scheduler prerequisites

Source: release/1.0.0 at 0b10ef7c77838712d4fe4a24d96e88167097ce1e, fetched 2026-10-30. Compared the four relevant consumer/scheduler/AsyncRef files against previously inspected 0eb9fc4; no differences. Isolated worktree: /tmp/tldr-caller-prerequisites-20261030. Astra audit/design; no Luna coding assignment because the safe adapter contract is not yet implemented. No compiler/build/test launch. Runtime evidence UNRUN. Review/fix cycles used: one bounded audit, zero code retries.

## Finding changes the migration premise

Neither identified consumer currently waits on the detached TLDR Future. In `80.driver/driver_build/file_fiber_v1.spl`, the DEPS stage discards table.deref's return; it uses deref solely to enqueue an outside fill. Fibers park on existing scalar module/outside scheduler tokens. `module_filled`, `_fail`, and `parse_done` explicitly wake those tokens. Those wakes must remain functional; this audit does not diagnose a detached-future hang in that path.

`80.driver/cache/worker_surface_table_owner_v1.spl` never requests fills or creates handles. It performs ready-only lookup/set-once publication. Replacing it with AsyncRef would introduce ownership and capacity obligations without replacing an actual asynchronous wait.

## Blocking prerequisites for an actual canonical migration

1. **Carrier token adapter.** FiberSchedV1 stores one i64 park token per fiber; AsyncRef subscribes a canonical RingToken(ring,slot,generation), then requires owner-driven async_ref_deliver_wake_i64 and terminal ring completion acknowledgement. No bridge currently binds them. Never cast slot to scheduler token or drop generation. Extend the existing FileFiber carrier, not the scheduler or a new registry: retain one bounded wait record for each parked fiber, validate full ring identity on completion, then wake that fiber through the existing scheduler token. Release the mapping only after delivery/ACK or terminal cancellation.
2. **Cumulative resource bounds.** Scalar map descriptors/outcomes/waiters are insert-once until quiescent close. A ring slot may be reused but successive generation subscriptions still consume waiter storage. Bound total keys and total subscriptions per run, not just simultaneous parked fibers. imports_of is discovered per parsed source, so entry count alone does not prove a dependency-edge bound. Introduce an explicit run budget and typed admission failure; never silently fall back to detached Futures or unlimited allocation. No new global parse barrier is needed.
3. **Owned terminal shutdown.** file_fiber_end_v1 checks runnable/external work and closes the IO reactor; its caller then returns an inspectable FileFiberRunV1 with its table. It does not prove AsyncRef subscriber/cursor quiescence. Scheduler failure, stalled completion and host abandonment must terminalize outstanding producer outcomes, cancel/drain consumer reservations and confirm all callbacks are done before freeing the map. Existing copyable raw AsyncRef and exposed table fields can escape; a safe end method cannot assert nobody retained them. Minimum prerequisite is an explicit owner-scoped adapter/capability that forbids untracked reference escape, or an explicitly unsafe new API whose caller owns that obligation. Do not silently add unsafe destruction to existing safe APIs.
4. **Preserved inspection result.** Finished callers inspect run errors/order/text/table. A future adapter must separate live execution ownership from the returned immutable result, or keep a genuine owning lease alive with that result. Closing the raw arena and returning stale references is invalid; retaining every arena forever is not bounded cleanup. Changing the current return contract needs caller migration and tests, not a constructor swap.
5. **Worker transient retention.** worker_surface_table_promote_transient_owner_v1 promotes the whole graph once, then only entries on dirty leases because that is the only mutated graph. Async request/failure/waiter metadata would invalidate that premise. First prove retention of every changed graph across parser leases and a process-scope capacity/lifetime policy. Since this owner is ready-only, it should remain unchanged until an actual async caller requires those facilities.

## Smallest meaningful next implementation

Implement the FileFiber carrier wait/terminal-drain ownership adapter as a separate prerequisite, using the existing SimpleRing + AsyncRef subscription APIs and existing fiber scheduler. It must expose no untracked raw references to callers, and must retain exact ring generation until terminal completion. Freeze the run budget and finished-result lifetime/compatibility contract before coding. This is the minimum safe slice; merely changing create/deref/fill method names cannot provide it. Worker ready-cache migration is not a prerequisite and should not be bundled.

No concrete safe adapter API is claimed in this report. Current field opacity/raw-reference lifetime enforcement and terminal result contract are unresolved, so default caller replacement is blocked. Existing consumer source remains untouched.

## Author-first acceptance oracles for that adapter

- Two actual FileFiber consumers wait on one outside module; one producer publishes, both exact ring generations complete, then both original scheduler parks resume. Preserve unrelated progress and import-cycle behavior.
- Reuse the same ring slot with a new generation; delayed old completion cannot wake the new fiber. Use actual ring transitions, not manually incremented counters.
- Real SourceReader failure makes all original subscriptions terminal and wakes dependent fibers; no Pending remains after producer failure.
- Admission limits cover cumulative dependency subscriptions. Exhaustion returns explicit errors and cannot strand a parked fiber or overrun metadata.
- Cancellation of one interest leaves other interest/producer valid. Ring completion failure retains wake work until successfully delivered or terminally canceled.
- End on normal completion, scheduler failure, stall and host abort drains/cancels all records before release. The returned text/error result remains readable; attempted late external work is rejected before dereferencing released storage.
- Existing `test/01_unit/compiler/driver/file_fiber_v1_spec.spl` behavior remains compatible. Reuse `test/02_integration/lib/async/lockless_map_async_ref_spec.spl` and `test/02_integration/compiler/driver/cache/tldr_waiter_publication_contract_spec.spl` for canonical wake/failure semantics. If worker scope is later changed, extend `test/fixtures/compiler/worker_surface_table_lifetime.spl` across repeated parser leases.

These are unimplemented acceptance requirements, not executable PASS claims. No placeholder tests or fake completion were added.
