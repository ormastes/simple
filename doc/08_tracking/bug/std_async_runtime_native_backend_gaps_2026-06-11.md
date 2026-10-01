# std.async Runtime Native Backend Gaps - 2026-06-11

## Not closed 2026-09-13 — partly stale, partly unverified; left OPEN with the stale half recorded

- **measured** Gap 1 is STALE as written: `src/lib/nogc_async_mut/async/sffi.spl` no longer
  exists (the directory now holds future/poll/promise/executor/scheduler/sleep/timer/sync/
  cancellation/combinators/task/io/runtime `.spl`), and `grep -rl future_alloc_pending src/`
  returns nothing — the 14 named externs are not declared anywhere any more.
- **inferred** Gaps 2-5 (no real cooperative yield; `Poll.unwrap()` unknown `panic`; chained
  `self.poll().is_ready()`; poll-once `gather`/`race`/`timeout`) are behavioural and need the
  acceptance specs under `test/01_unit/lib/async/` this entry itself demands; none exist, so
  nothing here can be closed on evidence.
- Left OPEN: rewrite gap 1 against the current module layout before working the rest.


Status: open (triaged 2026-06-11)

## Summary

The pure-Simple `std.async` layer was repaired on 2026-06-11 (waker drain,
import/arity fixes, honest pending `yield_now`/`sleep`, poll-once
`gather`/`race`/`timeout`, cancellation/sync/timer primitives). The remaining
gaps need native runtime work or interpreter fixes and are tracked here.

## Gaps

1. **14 async SFFI externs unimplemented** — declared in
   `src/lib/nogc_async_mut/async/sffi.spl` but absent from the Rust runtime:
   `future_alloc_pending`, `future_poll`, `promise_*`, `async_sleep`,
   `async_yield`, `async_read_file`, `async_write_file`, `async_join`,
   `async_select`. Adding them requires seed runtime work plus
   `scripts/bootstrap/bootstrap-from-scratch.sh --deploy`.
2. **`yield_now()` / `AsyncIO.sleep()` cannot suspend-once-then-resume** —
   they now return honest `Pending`; a real cooperative yield needs a
   scheduler tick that calls `waker_signal` (native timer or runtime hook).
   Until then, only executor-driven re-poll completes them.
3. **`Poll.unwrap()` → "Unknown variable: panic"** — HIR lowering cannot
   resolve `panic` in `src/lib/nogc_async_mut/async/poll.spl`; JIT falls back
   to the interpreter.
4. **Chained `self.poll().is_ready()` fails in interpreter nested-call
   context** (`Future.is_ready()`); workaround is an intermediate local.
5. **`gather`/`race`/`timeout` are poll-once** — completing mixed
   ready/pending sets needs the waker-driven re-poll loop from gap 2.

## Acceptance

Each gap closes with a behavioral spec in `test/01_unit/lib/async/` proving
suspension/resumption (no literal-vs-literal assertions), run in interpreter
mode.
