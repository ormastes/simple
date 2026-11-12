# `rt_mutex_lock -> i64` makes the seed JIT double-box the protected value (2026-11-12)

Status: FIXED in source (`src/lib/nogc_sync_mut/concurrent/mutex.spl`:
`rt_mutex_lock` / `rt_mutex_try_lock` now return `i64?`).

Not observable before the JIT admitted declared `ANY` closure boundaries:
every module co-compiling `mutex_with_lock` fell back to the interpreter,
which is dynamically typed.

## Repro (seed JIT with the boundary admitted)

```simple
use std.nogc_sync_mut.concurrent.mutex.{mutex_new, mutex_with_lock}

fn main():
    val m = mutex_new(41)
    print "{mutex_with_lock(m, \c: c + 1)},{mutex_with_lock(m, \c: c * 2)}"   # expect 42,84
```

`-> i64`: `329,5264`; a text mutex answered `nil`; a float mutex a garbage
float. `-> i64?`: `42,84`, `ab`, `2.5` (JIT, no fallback) and the same under
the interpreter.

## Cause

The runtime answers the PROTECTED VALUE as an already-tagged word (nil for a
stale handle). Declared `-> i64`, the Rust seed treats the result as a raw
integer and boxes it on the way into the `val current: T? = ...` binding,
tagging it a second time. This is the contract mismatch
`rti007_any_return_rows_2026-11-01.md` describes for `rt_tuple_get`.

## Why `i64?` and not `<T> -> T?`

The frozen stage2 (Phase 3, revision ef0681fc0e1) cannot build an interface
row for a declared return that lowers to `Any`, which is what a generic extern
return does there (E-RTI-007); that is why the `-> i64` workaround existed and
why restoring `<T>(mutex: i64) -> T?` was held. `i64?` satisfies both sides:

- seed: an optional of a raw scalar is a tagged slot
  (`slot_holds_tagged_value`), so the word is carried verbatim into `T?`;
- frozen stage2: the return is concrete and non-generic. At ef0681fc0e1
  `rti_term_of_hir_type` maps `HirTypeKind.Optional(inner)` to
  `RtType.OptionalT(...)` and only rejects `Any` / inference / error types.
  The same shape is already compiled by Phase 3:
  `extern fn rt_mutex_new<T>(initial: T) -> i64?`
  (`src/lib/nogc_sync_mut/sffi/concurrent.spl`).

It also matches the documented contract ("nil means stale or foreign handle")
and `mutex_lock_gate`, which already returns `i64?` from it.

## Verified / not verified

- Verified: the repro above on the seed JIT and the interpreter;
  `mutex_free_function_spec` (1/1), `mutex_struct_value_spec` (4/4),
  `mutex_unit_spec` (41/41) before and after.
- NOT verified: compiling `mutex.spl` with the frozen Windows stage2 binary.
  No stage2 binary is available on this host; the argument above is from the
  ef0681fc0e1 source and the existing `-> i64?` precedent.
- No automated regression test: the mutex specs run interpreted and pass with
  either declaration.
