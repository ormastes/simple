# async_spec.spl: TaskState declared as `class` instead of `enum` — fixing the declaration hangs the run

**Status:** OPEN
**Filed:** 2026-09-01
**Found by:** triage of `test/01_unit/lib/std/` failures on Windows
  (`test/01_unit/lib/std/async_spec.spl`, 21/45 passing).

## The declaration bug (confirmed)

`test/01_unit/lib/std/async_spec.spl:97` declares:

```
class TaskState:
    Pending
    Running
    Suspended
    Completed
    Cancelled
```

This is the `enum` idiom (bare variant names, `impl TaskState: fn ... match
self: case Completed: ...`) written with the `class` keyword — compare
`enum PromiseState:` in the sibling spec
`test/01_unit/lib/std/concurrency/promise_spec.spl:15`, which uses the
identical shape correctly. Because `TaskState` is declared `class` and never
given fields, `TaskState.Pending` is not a valid variant constructor and
every use of it fails with `semantic: method 'Pending' not found on type
'TaskState'` — 20 of the file's 24 failures are this one error, repeated at
every call site that touches `Task`/`Executor`/`Scheduler`.

## Why it is NOT fixed here

Changing `class TaskState:` to `enum TaskState:` (the syntactically correct
fix, and the only change made to test this) does not turn the 20 failures
green. Instead the whole spec run hangs:

```
bin/simple test test/01_unit/lib/std/async_spec.spl
# times out (measured: no completion within 30s, rc=124)
# runner reports: TERMINATED: child died by signal with no crash sentinel
#   and no fault diagnostic (unverified -- an external killer such as
#   earlyoom cannot be ruled out)
```

i.e. fixing the declaration lets execution proceed far enough into the
`Task`/`Executor`/`Scheduler` logic in this file to hit a real infinite
loop or non-terminating match, somewhere downstream of `TaskState` actually
behaving like a proper enum for the first time. This is a second, deeper
bug this spec's own scheduling/executor code (not stdlib product code) —
diagnosing it needs isolating which specific `it` block hangs (bisection),
which was out of scope for this pass.

## Left as-is

The `class`/`enum` typo was reverted back to `class TaskState:` rather than
landed, because landing it turns a bounded 24-failure run into an unbounded
hang, which is worse for CI (blocks the whole file, and the runner cannot
even attribute the hang to a specific example). Both bugs are real; only
the first is precisely diagnosed. Do not "fix" this by changing `class` to
`enum` without also finding and fixing the hang, and do not silently drop
or `@tag:in-development` the spec to hide either problem.

## Repro

```bash
# current state (class, no hang, 21/45 pass):
bin/simple test test/01_unit/lib/std/async_spec.spl

# to reproduce the hang, change line 97 class -> enum and rerun with a timeout:
timeout 30 bin/simple test test/01_unit/lib/std/async_spec.spl; echo "rc=$?"
# rc=124
```
