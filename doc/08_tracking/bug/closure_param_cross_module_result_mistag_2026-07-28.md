# Cross-module closure-param invocation mis-tags results (seed run lane)

- **Date:** 2026-07-28
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- **Area:** interpreter/JIT closure calls; observed via `bin/simple run` (seed-backed lane — banner "Build and use the pure-Simple bin/simple instead." was printed)

## Symptom

Calling a `fn(Any) -> Any` parameter from a stdlib module function corrupts or
misdispatches the result when the argument flows from an extern (`rt_mutex_lock`)
result:

- `mutex_with_lock(m, \v: v + 3)` on `mutex_new(7)` returns `<special:7>`;
  probe inside showed `current=7` (clean) but `f(current)` = `<special:7>`.
- Wrong-closure dispatch observed: `rwlock_with_write(rw, \v: v + 8)` on 42
  returned 43 — the `\v: v + 1` lambda from an earlier call site was applied.
- `hof_any(7, \v: v + 3)` returns 10 in a clean file but `<special:7>` in the
  same file once module-level `extern fn` declarations are present.
- Same-file `extern fn rt_mutex_lock` declarations return raw mis-tagged
  values (`<value:0x7>` for 7); the stdlib-module extern path returns clean 7.
- `\v: v * 2` applied to a locked 10 produced `<value:0x14>` — the arithmetic
  happened (0x14 = 20) but the int tag was lost.
- Identical behavior with and without `SIMPLE_NO_JIT=1`.

Counter-case that works: `rwlock_with_read(rw, \v: v * 2)` (closure call is the
final expression, receiver value from `rt_rwlock_read`) returned 84 correctly
and repeatedly. A trampoline that mimics that shape for the mutex path did NOT
fix it.

## Repro

Fixtures preserved in the SF4 lane report; minimal:

```
use std.nogc_sync_mut.concurrent.mutex.{mutex_new, mutex_with_lock}
fn main():
    print "{mutex_with_lock(mutex_new(7), \v: v + 3)}"   # expect 10, got <special:7>
main()
```

## Impact

Blocks reliable higher-order guard APIs (`with_lock`) in the stdlib on the
seed-backed run lane. Spec-harness behavior tracked separately in
`test/01_unit/lib/nogc_sync_mut/concurrent/with_lock_guard_spec.spl`.
