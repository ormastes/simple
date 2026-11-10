# async_spec.spl: TaskState declared as `class` instead of `enum` — fixing the declaration hangs the run
## Closed 2026-11-05 — Resolved: hang was a spec-side value-semantics infinite loop, fixed by e8cfbc4d5e5

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** CLOSED 2026-11-05 (RESOLVED 2026-09-18 by e8cfbc4d5e5, re-verified by reproduction + full-mode runs)
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

## Resolution 2026-11-05 — hang located, root cause, and verification

**Where the hang was.** Runtime, in the spec's own `Executor.run()` loop —
not parse, not HIR, not an engine defect, and not Windows-specific. With
`class TaskState:` the file fails semantically before any executor code runs
(`method 'Pending' not found`); changing it to `enum` lets execution reach
the executor double, which then spins forever.

**Root cause (spec-side).** The pre-fix `Future`/`Promise` doubles embedded
an `AsyncState` class field, and Simple has value semantics: construction
and anon-tuple destructuring deep-copy. The old `Promise.new()` returned
`(Future(state: state), Promise(state: state))` — two *copies* of one
`AsyncState`, so `promise.complete(99)` mutated only the `Promise` copy and
the destructured `future` polled `Pending` forever. In the
`it "should wake suspended task"` example a task is spawned on that
never-ready future; `Executor.run()` loops `while self.running and
self.tasks.len() > 0`, and `run_iteration()` re-queues every suspended task
onto `ready_queue`, so `tasks` never drains and the loop never exits.

**Fix (already landed as e8cfbc4d5e5, "test(std): repair async_spec
Future/Promise state model (registry-based)").** Both halves of this bug
were fixed there, on 2026-09-18: `TaskState` is now declared `enum`, and
the doubles share mutable state through a module-level `_async_states`
registry keyed by `state_id` (the idiom from
`test/01_unit/lib/nogc_async_mut/promise_spec.spl`), so `Promise.new()`
handles poll consistently and the suspended task actually wakes. No engine
or stdlib change was needed. The existing `it "should wake suspended task"`
block is the regression test: under the old state model it hangs (rc=124).

**RED (hang reproduced, aarch64 Linux, phase-snapshot seed binary).**
Pre-fix spec (`git show e8cfbc4d5e5^:test/01_unit/lib/std/async_spec.spl`,
with `class TaskState:` -> `enum TaskState:` applied per this doc's repro):

```
timeout 120 <simple> test <pre-fix spec>   # rc=124, no verdict emitted
```

A minimal standalone probe using the old doubles (never-ready future +
`Executor.run()`) prints `before run` and never reaches `after run`,
confirming the infinite loop is in the executor double's re-queue logic.

**GREEN (current tree).** `test/01_unit/lib/std/async_spec.spl` with the
landed fix:

```
<simple> test test/01_unit/lib/std/async_spec.spl                 # 46/46 passed
<simple> test ... --mode interpreter                              # 46/46 passed
<simple> test ... --mode native                                   # 46/46 passed
```

**Regression (neighboring async specs, all with timeouts).**
`test/01_unit/lib/nogc_async_mut/promise_spec.spl` — 20/20 passed.
Sibling `test/01_unit/lib/std/concurrency/promise_spec.spl` — 12/19 passed,
7 failed with pre-existing, unrelated `semantic: unknown static method new
on class Promise` (production `std.async.Promise` API surface; separate
lane, not this bug).

**Remaining concerns.** None for this bug. The production
`std.async` promise shared-state registry remains a documented follow-up
lane per e8cfbc4d5e5's message; the sibling concurrency spec's 7 failures
are a distinct issue.


## 2026-11-10 triage (P3 runner lane, work/p3-runner-20261110): SUPERSEDED

Fix commit e8cfbc4d5e5 ("test(std): repair async_spec Future/Promise state
model (registry-based)") is an ancestor of this lane's base
(origin/release/1.0.0); the doc header already records CLOSED 2026-11-05.
No live reproduce attempted; the 46/46 full/interpreter/native evidence in
the resolution section stands.
