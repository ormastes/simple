# `it` body method call on a module `var` uses the stale pre-helper value

## Status
Fixed in the Rust seed interpreter on 2026-10-30. The shared `bin/simple` picks up the fix only after the seed is redeployed.

## Symptom
`async_host_handle_cleanup_contract_spec.spl` (7 examples) and
`async_host/async_mutex_suspend_spec.spl` (12 examples) failed with
`undefined field 'state': cannot access field on value of type 'nil'`.
`cleanup_scheduler.tasks[id]` was empty right after a helper had filled it.

## Root cause
`interpreter_call/bdd.rs` runs every `it` body in a copy of the caller env. A
helper such as `cleanup_setup()` reassigns module vars (`cleanup_mutex =
AsyncMutex.hosted(2)`), and the write lands in `MODULE_GLOBALS`. Identifier
reads already prefer `MODULE_GLOBALS` for non-local bindings
(`spec_it_block_reads_stale_module_var_2026-08-04.md`). The method-call receiver
paths read `env` directly:
- `interpreter/expr/calls.rs` (MECALL-OWNED fast path and the self-update path)
- `interpreter_helpers/patterns.rs::handle_method_call_with_self_update`

So `g.f` returned the new value, but `g.m()` ran on the old object and its
write-back put the stale object over the live one. Minimal repro:

```
var gbox = Box(n: 0)
fn setup_it(): gbox = Box(n: 2)
it "...":
    setup_it()
    print "{gbox.n} {gbox.get()} {gbox.n}"   # printed 2 0 0
```

## Fix
`refresh_stale_module_global_receiver` (`interpreter/expr/calls.rs`) refreshes a
non-local binding that has no owner provenance from `MODULE_GLOBALS` before
both receiver paths use it.

## Specs
- Reproduction: `test/01_unit/compiler/spec_it_method_receiver_stale_module_var_spec.spl`
  (2 of 3 fail on the old seed; all 3 pass after the fix).
- Generalization: the same spec covers `fn` and `me` receivers and an array receiver.

## Remaining (not this defect)
With the fix, the two async_host specs no longer hit the nil error, but their
own assertions still fail. `async_host_handle_cleanup_contract_spec` example 1,
for instance, reports `cancellation_registry_live_count` = 3 against a baseline
of 0 after teardown. Those failures are left RED for separate triage.
