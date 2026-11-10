# Method chain poisons the receiver variable's inferred type

Date: 2026-09-16
Status: OPEN (re-verified LIVE 2026-11-11, lane ne15 — see addendum)

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


## Addendum 2026-11-11 (lane ne15) — LIVE; receiver poison reproduces verbatim on the fresh seed

**Verification actually run** (worktree simple-p3-ne15-20261111, tip
f7640d20a458, fresh seed 46fe8f6b6def, seed-smoke). Faithful self-contained
repro of the doc's snippet (capacity-1 ReplyStore; the chained
`expect(replies.allocate_id()).to_equal(-1)`, then `replies.remove(reply_id)`,
then `expect(replies.allocate_id() > reply_id).to_equal(true)`):

```simple
struct ReplyStore:
    next_id: i64
    cap: i64
    live: [i64]
impl ReplyStore:
    static fn with_capacity(capacity: i64) -> ReplyStore:
        ReplyStore(next_id: 0, cap: capacity, live: [])
    me allocate_id() -> i64:
        if self.live.len() >= self.cap: return -1
        val id = self.next_id
        self.next_id = self.next_id + 1
        self.live.push(id)
        id
    me remove(id: i64):
        var out: [i64] = []
        for x in self.live:
            if x != id: out.push(x)
        self.live = out
# chained form:  ✗ expected false to equal true   (Results: 1 total, 0 passed, 1 failed)
# bound-intermediate control: ✓                   (Results: 1 total, 1 passed, 0 failed)
```

Control with `val full_id = replies.allocate_id()` passes; the chained form
fails exactly as filed. The poison — a method call nested inside
`expect(...)` corrupting subsequent calls on the same `var` receiver — is
still live. Status stays OPEN; the four workaround specs (e.g.
`test/01_unit/lib/nogc_async_mut/actor_reply_store_capacity_spec.spl`, still
carrying its "Bind intermediates" comment pointing here) must keep their
workarounds.

**Fix path / grant needed:** the doc's unblock condition points at seed /
self-hosted type inference (chain-result type leaking into the receiver
slot). This lane cannot rebuild the seed (no cargo/rustc) and has no
self-hosted binary, so no code change was attempted. Grant for the fixing
lane: seed rebuild after the inference fix (`cd src/compiler_rust && cargo
build --release`, or the repo's seed-rebuild script), then re-run the two
shapes above (chained must pass, control must stay green), then remove the
four spec workarounds as this doc's unblock condition requires.
