# Method chain poisons the receiver variable's inferred type

Date: 2026-09-16
Status: FIXED 2026-11-14 (lane p3-batch-c) — root cause was the seed `expect` handler re-evaluating ordered comparisons; see the 2026-11-14 addendum

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

## 2026-11-13 triage (P3 misc-a lane, work/p3-misc-a-20261113)

**LIVE (confirmed)** — ne15 re-verified: chained form still fails, bound-intermediate control still passes. Chain-result type leaks into the receiver slot in seed/self-hosted inference; seed-rebuild grant recorded. The four workaround specs must keep their binds.


## Addendum 2026-11-13 (lane work/live-p3-l3-20261113 (worktree lp3-wt, base f790f7f266e = origin/release/1.0.0 tip, seed binary build-commit 46fe8f6b6def))

Re-verified LIVE verbatim on this base with the 2026-11-11 addendum's
self-contained ReplyStore repro: the chained form
(`expect(replies.allocate_id()).to_equal(-1)` nested in `expect`, then
`replies.remove(...)`, then `expect(replies.allocate_id() > reply_id).to_equal(true)`)
fails 1/1, while the bound-intermediate control (each `allocate_id()` result
bound to a `val` first) passes on the same binary in the same session. The
receiver-poison mechanism is unchanged. Fix path remains the record's: seed /
self-hosted type-inference (chain-result type leaking into the receiver slot)
plus seed rebuild; not attempted in this lane.

## Addendum 2026-11-14 (lane p3-batch-c) — FIXED; the receiver was never poisoned

Seeds: Rust seed built from `release/1.0.0` @ `c541817df822` (base) and the
same tree plus this fix, Linux aarch64.

**Real cause.** The receiver's type was not the problem. The seed's BDD
`expect` handler (`src/compiler_rust/compiler/src/interpreter_call/bdd.rs`,
`"expect"` arm) evaluated both operands of an ORDERED comparison (`<`, `<=`,
`>`, `>=`) for its failure message, then evaluated the whole comparison
**again** for its value. Any side-effecting operand ran twice and the assertion
saw the second run. In the ReplyStore repro, `expect(replies.allocate_id() >
reply_id)` allocated id 1 (true), then allocated again on a full store (-1,
false). Probes on the base seed:

- `expect(bump() > 0).to_equal(true)`: global counter ends at **2** (now 1);
- `val b = replies.allocate_id() > reply_id`: true, and `simple run` agrees;
- `expect(replies.allocate_id()).to_equal(-1)` followed by plain calls on the
  same `var`: correct. This is the "V1 passes, V3 fails" split that contradicts
  the receiver-poison diagnosis.

`==`/`!=` were already single-evaluation.

**Fix.** Each operand is evaluated once. The ordered arm runs the standard
binary evaluator on those values, bound to NUL-prefixed temporaries (the same
pattern as the compound field-setter path in `interpreter/node_exec.rs`), so
ordering semantics (unsigned, float, text, `__lt__`) are unchanged. The dead
`eval_assertion_operand` wrapper is replaced by
`collapse_assertion_operand`, which works on an already-evaluated value.

**Evidence.** `test/01_unit/bugs/expect_ordered_compare_single_eval_spec.spl`:
base seed 5/10, with every single-evaluation and ReplyStore example red; fixed
seed 10/10. Negative examples that are green on both seeds: `==`/`!=` run
once, `expect(5 < 3).to_equal(false)`, u64 high-bit, int/float and text
ordering. A bare `expect 1 > 2` still fails with `expected 1 > 2 to hold` on
both seeds. Timing for 100k `expect(i >= 0).to_equal(true)`: base 2.43/2.29 s,
fixed 2.36/1.74 s, RSS 228–281 MB on both (noise).

**Workarounds removed.** All four specs were re-run with the chained form on
both seeds, at their real paths:

| spec | base | fixed |
|---|---|---|
| `actor_reply_store_capacity_spec` | red | green |
| `static_compression_cache_spec` | green | green |
| `worker_wire_shutdown_spec` | green | green |
| `ndarray_empty_public_reductions_spec` | green | green |

So only the ReplyStore shape was this bug. The other three had already
stopped reproducing. All four now use the chained form.
