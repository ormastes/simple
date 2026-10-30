# async_host cancellation specs fail on the seed interpreter: class instances are copied, not aliased

## Status
Open. Skipped by the 2026-10-30 fix lane because the fix is larger than a spec or library change.

## Symptom
Seed `bin/simple` (`manual-release100-163d95b-20261030`), 2026-10-30:
- `test/01_unit/lib/nogc_async_mut/async_host_handle_cleanup_contract_spec.spl`: 1/8 pass.
  The failures include `expected 0 to equal 1` (cleanup action never ran),
  `expected 11 to equal 9`, `expected false to equal true`, and the
  `undefined field 'state' ... nil` error that
  `spec_it_method_receiver_stale_module_var_2026-10-30.md` fixes but that has not been redeployed yet.
  With that fix, the record says
  `cancellation_registry_live_count()` is 3 against a baseline of 0 after teardown.
- `test/01_unit/lib/nogc_async_mut/async_host_handle_cancellation_contract_spec.spl`: 0/2 pass
  (`expected 0 to equal 1`, `expected 2 to equal 1`).

Both specs are tagged `only-compiled`, but the runner still executes them on the seed interpreter.

## Root cause
`HostScheduler` (`src/lib/nogc_async_mut/async_host/scheduler.spl`) shares one
`HostTaskSignals` object between the scheduler and every `HostTaskContext`. It
stores `HostTask` values in `Dict<usize, HostTask>`. Cancellation works only if
those are aliased references:
`HostTaskContext.request_cancel()` pushes onto `self.signals.cancelled`, and
`HostScheduler._drain_task_signals()` later reads `self.signals.cancelled`
to run `cancel_task` -> `HostTaskContext.finish()` -> `lifetime.release()`.

The seed interpreter copies class instances when a value is stored in or read
from a collection, so the scheduler never sees the published cancel signal.
`finish()` therefore never runs, the cleanup actions never fire, and the
`CancellationToken` lifetimes are never released. That leaves the registry count at
3, one per scheduled task. `doc/07_guide/language/value_semantics_by_engine.md`
already shows that list and dict element semantics differ between engines.

Minimal reproduction (fails on the seed with `expected 0 to equal 1`):

```
class Sig:
    items: [i64]
class Ctx:
    sig: Sig
    me publish():
        self.sig.items = self.sig.items.push(7)
class Owner:
    sig: Sig
    tasks: Dict<i64, Ctx>

it "shares a class field through a dict-stored holder":
    var o = Owner(sig: Sig(items: []), tasks: {})
    o.tasks[1] = Ctx(sig: o.sig)
    val c = o.tasks[1]
    c.publish()
    expect(o.sig.items.len()).to_equal(1)
```

## Why it was skipped
Neither spec is wrong, and neither is the scheduler. A fix needs one of these:
1. reference semantics for class instances in the interpreter, which is an engine-wide value-model change; or
2. a scheduler redesign that keeps the signal queues in module-level storage keyed by
   scheduler id instead of a shared object field; or
3. the runner honoring `only-compiled`, so these specs run only on a compiled lane.
   No compiled lane exists on this host yet: `bin/simple` is the Rust seed.

Each is a design decision beyond a one-defect fix.

Note: `async_host_missing_async_core_module_breaks_task_handle_cancel_2026-07-29.md`
is stale. `src/lib/nogc_async_mut/async_core.spl` now exists, and the specs import it successfully.
