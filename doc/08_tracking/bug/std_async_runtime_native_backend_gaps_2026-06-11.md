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

## Triage 2026-11-25 (P2 fleet, release/1.0.0 @ d1b74b3fa1d)

Per-gap state at HEAD, by code inspection (spec execution is environment-
blocked: the tracked release/1.0.0 binary rejects the `@representation_boundary`
decorator now present in release/1.0.0 source, so `bin/simple.exe test` aborts
loading `src/app/test_runner_new/test_runner_client.spl:9` before any spec
runs — no new execution evidence is claimed):

1. **Gap 1 (14 async SFFI externs) — STALE, confirmed.** `sffi.spl` is gone
   and `grep -rn future_alloc_pending src/` returns nothing; the named externs
   are declared nowhere.
2. **Gap 2 (no real cooperative yield/sleep) — largely superseded.**
   `src/lib/nogc_async_mut/async/sleep.spl` now implements a Go-style
   cooperative scheduler (`run_sleepers` drives N sleepers concurrently,
   parking the OS thread only until the nearest deadline), and
   `runtime.spl:113-231` has a waker-drain + timer + re-poll executor loop
   (`_drain_wakers`, `waker_check`/`waker_clear`). Remaining integration
   (Runtime-driven timer wakeup for `sleep`) is explicitly tracked in
   `doc/08_tracking/todo/async_runtime_timer_wakeup_for_sleep_2026-08-17.md`.
3. **Gap 3 (`Poll.unwrap()` → unknown `panic`) — mooted by API redesign.**
   `Poll::unwrap` is deliberately absent; the supported extractor is the free
   fn `poll_unwrap` (`poll.spl:19-22`), and the header note pins the remaining
   `.unwrap()` rebinding defect to
   `poll_unwrap_second_bind_site_lower_and_check_impl_2026-08-25`.
4. **Gap 4 (chained `self.poll().is_ready()`) — worked around in source.**
   `future.spl:59-65` reads the intermediate `self.poll_result`; whether the
   interpreter nested-call defect itself is fixed is unverified (blocked as
   above).
5. **Gap 5 (poll-once combinators) — partially live.**
   `combinators.spl` `join`/`select` are still single-pass (first `Pending`
   returns `Future.pending` with no re-poll registration), but the runtime
   executor now re-polls via wakers, and the acceptance specs this entry
   demanded now exist under `test/01_unit/lib/async/` (async_basics,
   async_primitives, runtime_timer_sleep, sleep_go_style).

Left OPEN, re-scoped: what remains is (a) running the acceptance specs on a
qualified self-hosted binary and (b) the tracked runtime-timer integration
todo — not the original backend-extern gaps. Not a bounded single-lane fix.
