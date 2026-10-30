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

Pass counts and messages above are as reported by the seed runner. The spec
matcher's operand order in "expected X to equal Y" is not reliable, so read
them as "value mismatch", not as exact expected/actual pairs.

## Root cause (cleanup spec; cancellation spec only partly explained)
Owner ruling 2026-09-27: classes are value types. `val b = a`, argument passing,
and array or dict reads all copy. See
`interp_dict_class_value_copy_on_get_mutation_loss_2026-07-06.md` (RESOLVED section),
`doc/07_guide/language/capability_library_authoring.md`, and the gate
`test/01_unit/compiler/interpreter/dict_class_value_identity_spec.spl`.
The JIT's aliasing is itself a filed bug:
`jit_class_instances_alias_instead_of_copy_2026-09-27.md`.

`HostScheduler` (`src/lib/nogc_async_mut/async_host/scheduler.spl`) violates that
ruling. It passes `signals: self.signals` into every `HostTaskContext`, which already
copies the object, and stores `HostTask` values in `Dict<usize, HostTask>`. It then
expects `HostTaskContext.request_cancel()` (called through a handle's copy) to push
onto the same `signals.cancelled` queue that `_drain_task_signals()` reads. Under
value semantics that push lands on a copy, so these two things are lost:
- the cancel signal, so `has_runnable()` and the between-poll eager
  `cancel_task` path never fire for that task; and
- cleanup actions registered through the handle or context copy, which live on that copy.

`CancellationToken` state is module-level (`_registry_*` arrays in
`src/lib/nogc_async_mut/async/cancellation.spl`), so it is copy-safe.
`lifetime.cancel()` reaches the shared slot. A Pending or Running task that is
dispatched again is still finished and released by `run_one_worker`'s
`is_live()` and `is_cancelled()` checks. The leak therefore hits Suspended (parked)
tasks, which are never dispatched again. That is the case in the cleanup spec's
parked-waiter examples. The figure of 3 against a baseline of 0 is taken from
`spec_it_method_receiver_stale_module_var_2026-10-30.md`. This record does not
re-derive it.

`async_host_handle_cancellation_contract_spec` is NOT fully explained here.
Its first example cancels a task that is still Pending in the global queue, and
the pre-poll `is_live()` check should handle that. Its failures may belong to the
module-var visibility class fixed by #5394/#5444, which the deployed seed
(`163d95b`, the #5365 merge) predates. Rerun it after the seed is redeployed.

Minimal reproduction of the copy (fails on the seed):

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

## Fix direction (not done here)
Move the scheduler's shared signal queues and per-task cleanup actions into
module-level storage keyed by scheduler and task/lifetime id, which is the pattern
`CancellationToken` already uses. This is a scheduler redesign across `scheduler.spl`,
`handle.spl`, and `joinset.spl`, so it is larger than this lane's scope.
Interpreter reference semantics for classes are ruled out by the owner ruling.
Honoring `only-compiled` would not help either: it is a dead tag
(`scripts/check/check-bdd-tagged-block-drop.shs`), and a compiled lane that copies
classes correctly would break the same way.

Note: `async_host_missing_async_core_module_breaks_task_handle_cancel_2026-07-29.md`
is stale. `src/lib/nogc_async_mut/async_core.spl` now exists, and the specs import it successfully.
