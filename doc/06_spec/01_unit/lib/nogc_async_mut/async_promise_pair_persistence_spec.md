# Production promise pair persistence

Source: `test/01_unit/lib/nogc_async_mut/async_promise_pair_persistence_spec.spl`.

Authored manual; doc generation and execution are pending a qualified
self-hosted runtime. **TEST_BLOCKED**, not generated verification evidence.

1. Complete a production Promise returned in an anonymous tuple; require the
   associated Future to retain readiness and value 33 over repeated polls.
2. Complete independent pairs with 17 and 29; require one completion not to
   make the other ready or replace its payload.
3. Reject a second completion of 99; require the original payload 41 to persist.

Run: `<qualified-selfhosted-runtime> test test/01_unit/lib/nogc_async_mut/async_promise_pair_persistence_spec.spl --mode=interpreter`.

Expected inventory: three scenarios, zero failures. No current result claimed.
