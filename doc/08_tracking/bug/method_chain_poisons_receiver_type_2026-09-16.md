# Method chain poisons the receiver variable's inferred type

Date: 2026-09-16
Status: OPEN

## Observed

When a method call chain or a method call nested inside `expect(...)`.to_equal(...)
uses a `var` receiver, subsequent method calls on that receiver fail or return
wrong values, as if the receiver's inferred type had been replaced by the
chained result's type.

Repro (fails; binding intermediates passes):

```simple
var replies = ReplyStore.with_capacity(1)
val reply_id = replies.allocate_id()
expect(replies.allocate_id()).to_equal(-1)      # ok
replies.remove(reply_id)
expect(replies.allocate_id() > reply_id).to_equal(true)   # FAILS: false
```

With `val full_id = replies.allocate_id(); expect(full_id).to_equal(-1)` the
final expect passes. Same shape seen on `StaticCompressionCache.get(...)` and
`HttpRequestParser` chains, and earlier on `ndarray.sum_axis(...).len()` (spec
`ndarray_empty_public_reductions_spec.spl` now binds intermediate vals with a
comment pointing here).

## Impact

Correct specs fail with `expected false to equal true` even though every
individual operation behaves correctly when probed with bound intermediates.
Affected worklist specs worked around: `actor_reply_store_capacity_spec.spl`,
`static_compression_cache_spec.spl`, `worker_wire_shutdown_spec.spl`,
`ndarray_empty_public_reductions_spec.spl`.

## Expectation

A method call on a variable must not change the variable's inferred type;
`x.m1().m2()` and `expect(x.m1()).to_equal(v)` must behave identically to
binding each intermediate to a `val`.

## Unblock condition

Fix the seed/self-hosted type inference so chained-call receivers keep their
declared/inferred type (suspect: inference of the chain result leaking into the
receiver slot). Then remove the binding workarounds from the four specs above.
