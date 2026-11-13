# async_spec: `Poll.pending()` example calls a constructor the Poll double no longer has (2026-11-13)

- **Severity:** P3 (test-only; no product code affected)
- **Status:** fixed
- **Spec:** `test/01_unit/lib/std/async_spec.spl`, example `Poll<T>` / "should reject unwrap of pending value" (renamed by the fix to "rejects unwrap of a pending poll obtained from a pending future")
- **Branch:** `release/1.0.0` at `c63348a42db`

## Symptom

Reproduced with the seed `seed-whileval` (`<seed> test test/01_unit/lib/std/async_spec.spl`,
capped `systemd-run --user --scope -p MemoryMax=16G timeout 900`):

```
Poll<T>
  ✗ should reject unwrap of pending value
    semantic: unknown variant or method 'pending' on enum Poll
SPEC FILE VERDICT: test/01_unit/lib/std/async_spec.spl outcome=ERROR declared>=48 executed=48 passed=47 failed=1
```

## Root cause

The example is stale, not the library.

- Consolidation commit `b214ccc5a02` ("consolidate test/unit/lib -> test/01_unit/lib")
  copied this example from the legacy `test/unit/lib/std/async_spec.spl`. There the
  `Poll` double was a `class` with `static fn pending() -> Poll`.
- In `test/01_unit/lib/std/async_spec.spl` the double had already been modernized to
  `enum Poll: Ready(i64) / Pending`. That mirrors production `std.async.poll.Poll<T>`
  (`src/lib/nogc_async_mut/async/poll.spl`), which also has no lowercase `pending()`
  constructor. Neither the stdlib docs nor `doc/04_architecture/language/concurrency/`
  specify one.
- The only `fn pending` in the async stdlib belongs to the unrelated noalloc
  `PollResult` type (`src/lib/nogc_async_mut_noalloc/async/poll.spl`).

Unwrapping a pending poll already fails loudly. Both the spec double's `unwrap()` and
production `poll_unwrap` call `panic("Poll is pending")`. Nothing returns nil, so no
library change is needed.

## Fix

The example's construction is repaired, and its assertion and message are unchanged.
It now gets the pending poll from `Future.pending().poll()`, which is where the legacy
`Poll.pending()` value came from. The legacy double's `Future.poll()` returned
`Poll.pending()` when the future was not ready. This keeps the example distinct from
REQ-ASYNC-POLL-004, which builds `Poll.Pending` directly. Adding a `pending()`
constructor to the double was rejected, because it would invent API that production
`Poll<T>` does not have.

## Limitation

The direct panic path of `unwrap()` on `Pending` is not asserted in-process. The spec
framework has no panic or raise matcher (no `fn expect_raises` under `src/lib`), and a
panic would abort the spec file. The checked helper `unwrap_checked` is the asserted
contract.
