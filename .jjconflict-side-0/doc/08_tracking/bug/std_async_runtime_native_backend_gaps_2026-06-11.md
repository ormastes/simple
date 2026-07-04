# std.async Runtime Native Backend Gaps - 2026-06-11

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
