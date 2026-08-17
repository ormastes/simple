# `Any`-typed closure parameters silently destroy the value

- **Filed:** 2026-07-28
- **Severity:** high — silent data loss, no error, no warning
- Status: OPEN (P1)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- **Found via:** SF4 mutex-guard lane (its `with_lock` signature is built on this)

## Symptom

A closure passed through a parameter typed `fn(Any) -> Any` returns `nil`
instead of its value. The identical closure typed with a concrete type, or with
a generic type parameter, is correct.

Probe (`bin/simple run`, verified 2026-07-28):

```simple
fn apply_any(f: fn(Any) -> Any) -> Any:
    f(1)

fn apply_i64(f: fn(i64) -> i64) -> i64:
    f(1)

val g = fn(x: Any) -> Any: x
print(g(7))            # -> <value:0x7>   undecoded tagged box, not 7
print(apply_any(g))    # -> nil           value destroyed
val h = fn(x: i64) -> i64: x
print(apply_i64(h))    # -> 1             correct
```

Two distinct failures, both silent:

1. **Calling an `Any` closure directly leaks a raw tagged box** — `<value:0x7>`
   rather than `7`. `0x7` is the tagged encoding, undecoded on the way out. This
   is the same family as the known `BoxInt <<3` seed landmine.
2. **Passing an `Any` closure through an `Any`-typed parameter yields `nil`** —
   the value is not merely mis-decoded, it is gone.

Generic type parameters are unaffected:

```simple
fn apply_gen<T>(f: fn(T) -> T, v: T) -> T:
    f(v)

apply_gen(fn(x: i64) -> i64: x, 42)        # -> 42   correct
apply_gen(fn(s: text) -> text: s, "ok")    # -> ok   correct
```

## Impact

Any API that takes a callback typed through `Any` silently loses data. This is
especially dangerous for guard/wrapper patterns, where the callback's return
value is stored back somewhere: the store succeeds and writes `nil`.

Concretely, the SF4 `with_lock` guard is written as:

```simple
fn with_lock(f: fn(Any) -> Any) -> Any:
    val current = rt_mutex_lock(self._handle)
    val updated = f(current)
    rt_mutex_unlock(self._handle, updated)   # stores nil
    updated
```

Every `with_lock` call writes `nil` back into the mutex's stored value. A guard
intended to make locking safer instead destroys the protected data on every
use, with no diagnostic. This is a more serious defect than the spec hang
originally attributed to that lane, and plausibly its cause: a mutex whose
stored gate value has been replaced by `nil` can leave a subsequent acquirer
spinning.

## Fix direction

Use a generic type parameter instead of `Any` for callback signatures:

```simple
fn with_lock<T>(f: fn(T) -> T) -> T
```

Verified working above. This is also what `.claude/rules/language.md` implies by
preferring `<>` generics; `Any` should be reserved for genuinely heterogeneous
storage, not for callback plumbing.

Separately, the two underlying defects should be fixed rather than only routed
around: an `Any` round-trip that cannot preserve a value is a hole in the type,
and `<value:0x7>` escaping to output means the box decoder is not being reached
on that path.

## Related

- `reference_neither_engine_trustworthy_2026-07-27` — silent wrong values on
  both engines, different in each.
- `doc/07_guide/language/dict_native_pitfalls.md` — same family: `Dict.get()` on
  struct values returns corrupt payloads under native codegen.
