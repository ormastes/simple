# `green_task_error` is an exported API that can only ever return `""`

- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
- **Found:** 2026-08-08, adversarial review of `7168c6d1c2b2`
- **File:** `src/lib/nogc_async_mut/concurrent/green_thread.spl`

## Resolution

Wired a third option not enumerated below: a **self-report channel**. A
module-level `GREEN_CURRENT_ERROR: text` slot is reset by `green_run_one()`
immediately before invoking a thunk; the new export `green_fail(reason)` lets
the thunk body itself write to that slot. `green_run_one()` reads it back
after the thunk returns and records `has_error`/`error_reason` on the
`GreenTask` accordingly, so `green_task_error()` now returns a real value for
any task whose body called `green_fail(...)`. Tasks that don't call it are
`has_error: false` regardless of return value, preserving the existing
"bad result is value-level, not an error" test in
`green_spawn_deferred_spec.spl`. No thunk-signature change, so no blast radius
on the many existing `green_spawn(fn() -> i64)` call sites. Two new specs
added: "green_fail marks the task errored and green_task_error returns the
reason" and "green_task_error returns empty for a task that never called
green_fail".

`7168c6d1c2b2` itself is correct — reviewed and endorsed, see below. This is a
separate pre-existing defect found while reviewing it.

## The defect

`green_task_error(task_id)` is exported (line 106) and returns a per-task death
reason. `GreenTask` carries `has_error: bool` and `error_reason: text` to back
it. But `green_run_one()` is the only site that runs a thunk, and it does:

```
var ran_ok: bool = true
ran_result = t.thunk()
var updated = GreenTask(
    ...
    has_result: ran_ok,
    has_error: false,        # hardcoded
    error_reason: ""         # hardcoded
)
```

`ran_ok` is initialised `true` and never assigned again; `has_error` is a
literal `false`. No other site constructs a `GreenTask` with `has_error: true`
(`green_spawn` sets it `false` too). Therefore `has_error` is `false` for every
task that has ever existed, and `green_task_error` returns `""`
unconditionally — as does the `t.has_error` branch of
`GreenThreadHandle.is_done()`.

Three fields and one exported function are dead weight that read as a working
error-reporting API. A caller checking `green_task_error(id) != ""` to detect a
failed task gets a silent false negative.

## Why it cannot be fixed locally

The thunk type is `fn() -> i64`. Simple has no try/catch by design
(`.claude/rules/language.md`: "Error handling: use `Result<T, E>` + `?`"), so
there is nothing for `green_run_one` to catch. Fixing it requires either:

1. widening the thunk to `fn() -> Result<i64, text>` (breaking change to
   `green_spawn` / `green_spawn_eager`), or
2. a runtime-level task-abort hook the scheduler can poll.

Per `.claude/rules/code-style.md` ("NEVER convert TODO/FIXME to NOTE — implement
or delete entirely") the alternative is to delete `green_task_error`,
`has_error` and `error_reason` until one of those lands, rather than keep an
export that cannot work. Deleting is the smaller change and is recommended
unless option 1 is scheduled.

## The reviewed fix itself: endorsed

`7168c6d1c2b2` split `value_ready`/`value_done` out of the aggregate
`ready_count`/`done_count` so a value handle's `is_done()` compares against
`value_done`. Verified complete:

- `green_run_one()` has exactly two completion paths. The deferred-task path
  bumps `done_count` only. The value path (guarded by "no pending deferred task
  remains") bumps both `done_count` and `value_done`, and is the only writer of
  `value_done`.
- Because the deferred path has priority, the value branch can only run once
  every deferred task is finished, at which point
  `ready_count - done_count == value_ready - value_done`. So the value branch
  fires exactly `value_ready - value_done` times and `value_done` can never
  overtake `value_ready`.
- `green_ready_count()` is unchanged (`ready_count - done_count`) and still
  reports the aggregate outstanding total, which is what its callers expect.

The module header was updated in the same change as this report: it described
three counters where the struct has five, and asserted that task errors are
recorded as per-task death reasons, which §"The defect" above shows is not the
case.
