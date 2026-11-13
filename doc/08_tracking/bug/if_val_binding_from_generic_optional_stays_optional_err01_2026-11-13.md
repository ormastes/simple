# `if val` binding from a generic `T?` return stays optional under ERR-01

Date: 2026-11-13
Status: OPEN
Severity: P3
Found by: lane p3-asyncreg-20261113 (async_handler_registry_removed_apis_2026-09-16)

## Observed

The ERR-01 diagnostic (seed fix `349cd121b82`, `hir/lower/expr/operators.rs`
`lower_cast`) says to narrow with `?? <default>`, `if val x = ...`, or
`match`. `if val` does not work when the optional comes from a generic return:

```simple
use std.concurrent.channel.{channel_new}
fn drain() -> i64:
    val ch = channel_new()
    ch.send(41)
    if val m = ch.try_recv():      # Channel.try_recv<T>() -> T?
        return (m as i64) + 1      # still: cannot cast an optional `T?` to `i64` (ERR-01)
    return 0
```

Measured with seed-fix 2026-11-13: the spec fails with `err01=2`, 0 examples
executed. These all pass (1/1) on the same seed: `?? 0`, `match Some(v)`,
`if val` over a concrete `Dict<i64,i64>.get`, and a typed binding first
(`val m: i64? = ch.try_recv()` then `if val n = m`).

## Expectation

`if val x = <expr of type T?>` binds `x: T` whether `T` is concrete or an
uninferred generic. Either that, or the diagnostic stops recommending
`if val` for this case.

## Workaround in tree

`src/lib/nogc_async_mut/http_server/worker_owner.spl` run loop uses the
typed-binding form.
