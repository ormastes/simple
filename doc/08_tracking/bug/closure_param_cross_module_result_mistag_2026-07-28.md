# Cross-module closure-param invocation mis-tags results (seed run lane)

- **Date:** 2026-07-28
- **Status:** open
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

## Triage 2026-11-25 (fleet lane p2w1-ac, Windows worktree @ origin/release/1.0.0)

PARTIALLY STALE — the originally filed symptoms are mostly fixed on the
current tracked seed (`bin/simple.exe`, Rust seed v1.0.0-rc.1), but a residual
`rwlock_with_write` mistag remains and is seed-side. Probes run with
`SIMPLE_LIB=src bin/simple.exe run` (the `bin/simple.exe test` path is blocked
repo-wide at HEAD by the known `unknown decorator '@representation_boundary'`
source/binary inconsistency):

FIXED since filing (each printed the expected value, exit 0):

- `mutex_with_lock(mutex_new(7), \v: v + 3)` → `10` (was `<special:7>`)
- `hof_any(7, \v: v + 3)` → `10` in a file that also declares a module-level
  `extern fn rt_mutex_lock` (was `<special:7>`)
- `rwlock_with_read(rwlock_new(42), \v: v * 2)` → `84` (the counter-case,
  still correct)

STILL BROKEN (residual):

- `rwlock_with_write(rwlock_new(42), \v: v + 8)` and the method form
  `rw.with_write(\v: v + 8)` return the correct value 50 with its tag lost —
  printed as the denormal float `0.000...237` (i.e. the i64 bits of 50
  reinterpreted as f64). Bisection: `mutex_with_lock_keeping(m, 0, \: 50)`
  through the same gate helper prints `50` correctly, and a stdlib-free
  minimal nested-closure shape (`apply_gate(\: f(x))` with a captured closure
  param) also prints `50` — so the trigger is the specific combination in
  `rwlock_with_write`'s inner closure (captured `f` + `unsafe` extern calls
  `rt_rwlock_read`/`rt_rwlock_set` inside the zero-arg closure) flowing back
  through the generic `fn() -> T` boundary. A related JIT demotion observed on
  a sibling probe states the cause plainly: "the call boundary types
  [TypeId(5)] -> TypeId(14) are not carryable across the closure ABI (ANY
  means no encoding is correct for both an integer and a float); JIT would
  return wrong values". The defect lives in the Rust seed JIT closure ABI;
  fixing it requires a seed rebuild, which this lane prohibits, and dodging it
  by restructuring the stdlib would silently normalize a compiler workaround.
  The interpreter engine cannot arbitrate at HEAD because the interpreter's
  strict parser rejects the `@representation_boundary` decorators now present
  in `mutex.spl`/`rwlock.spl` (same source/binary inconsistency as above).

Status stays OPEN for the `with_write` residual only; everything else filed
here is fixed. Next step belongs to the seed JIT owner: make the closure ABI
carry (or honestly demote) the `T?`/extern-tagged results of closures that
capture a closure parameter and call externs. No code change made.
