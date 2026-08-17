# Static method that mentions the class type parameter is unresolvable

- **Date:** 2026-07-25
- **Area:** semantic analysis / static-method resolution on generic classes
- **Severity:** medium-high — breaks a documented, in-use production API and
  forces every generic class to ship free-function factory duplicates.
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 01).

## Symptom

`src/lib/gc_async_mut/pure/tensor.spl`:

```
class PureTensor<T>:
    static fn zeros(shape: [i64]) -> PureTensor<f64>:      # resolves fine
    static fn ones(shape: [i64]) -> PureTensor<f64>:       # resolves fine
    static fn randn(shape: [i64]) -> PureTensor<f64>:      # resolves fine
    static fn from_data(data: [T], shape: [i64]) -> PureTensor<T>:   # NOT FOUND
```

probe:

```
use std.pure.tensor.{PureTensor}
val t = PureTensor.zeros([2, 3])                       # ok
val u = PureTensor.from_data([1.0, 2.0, 3.0, 4.0], [2, 2])
```

```
✓ static zeros on generic type
✗ static from_data
    semantic: unknown static method from_data on class PureTensor
```

The distinguishing factor is the class type parameter `T`: the three statics
whose signatures mention no `T` resolve, the one that does mention `T` is
reported as if the method did not exist.

## Impact

- Production call sites that are currently broken:
  `src/lib/gc_async_mut/pure/demo.spl:25`, `:32`, `:33`.
- `src/lib/gc_async_mut/pure/tensor.spl:100-158` carries a whole block of
  `tensor_from_data` / `tensor_zeros` / `tensor_ones` / `tensor_randn` free
  functions explicitly commented as "Workaround for: PureTensor.X()". Note the
  comment there blames a *generic static methods in the interpreter* limitation
  wholesale — that is now stale, since `zeros`/`ones`/`randn` do work; only the
  `T`-mentioning form is affected.
- `src/lib/gc_async_mut/pure/test/tensor_spec.spl` keeps one explicitly pending
  example for this.

## Deliberately not worked around

Narrowing `from_data(data: [T], ...)` to `data: [f64]` would make it resolve,
but that silently normalises the workaround and drops i64 tensor construction
from the static API. Per `CLAUDE.md` ("fix it or record a concrete bug/feature
request instead of silently normalizing the workaround") the signature is left
correct and the defect recorded here.

## Blocked on

`bin/simple` currently resolves to the Rust bootstrap **seed**
(`bin/simple test` prints "this Rust-built Simple binary is a bootstrap seed
only"), so a fix in the pure-Simple semantic analyser cannot be verified
without a full bootstrap redeploy.
