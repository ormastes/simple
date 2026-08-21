# Spec runner: a falsy `expect(x)` subject overwrites an earlier real matcher failure message

- Date: 2026-08-21
- Status: RESOLVED 2026-08-21
- Where: `src/compiler_rust/compiler/src/interpreter_call/bdd.rs:1103` (`"expect"` builtin)

## Symptom

`browser_session_async_spec.spl` (`rejects a late old-page response ...`)
reported `expected subject to be truthy, got 0`, and
`browser_session_dom_generation_runtime_spec.spl` reported
`expected subject to be truthy, got ` (empty). In both, **no** `to_be(true)`
was failing. The real failures were `expected fetch-3 to equal fetch-2`,
`expected leak to equal https://example.test/atomic` and
`expected 0 to equal 1` — only visible by truncating the spec file just past
each step (bisection took 8 runs).

## Mechanism

`expect(value)` on a non-truthy subject sets `BDD_EXPECT_PROVISIONAL = true`
and writes `"expected subject to be truthy, got {}"` into `BDD_FAILURE_MSG`
**unconditionally**. A following `.to_*()` matcher clears the provisional
flag, but the message slot has already replaced whatever an earlier, genuine
matcher failure put there. So any example that, after its real failure, runs
`expect(0).to_equal(0)`, `expect("").to_equal("")`,
`expect(list.len()).to_equal(0)` or `expect(false).to_be(false)` reports the
wrong message. Both browser_session specs do exactly that (cookie counts,
empty cookie headers, empty pending-write lists).

## Fix sketch

Write the provisional text into its own slot (or only when `BDD_FAILURE_MSG`
is still `None`), and promote it to the real slot only at example end if no
matcher consumed it. Ship with a reproduce spec: an example whose first
matcher fails with `to_equal`, followed by `expect(0).to_equal(0)`, must
report the `to_equal` text.

## Resolution (2026-08-21)

Root cause: `src/compiler_rust/compiler/src/interpreter_call/bdd.rs` wrote the
provisional text straight into `BDD_FAILURE_MSG` at three sites — the ordered
comparison arm, the `==`/`!=` arm, and the general truthiness arm (the last is
the `bdd.rs:1103` in the report) — so it overwrote whatever a real matcher
failure had already recorded.

Fix: a new thread-local `BDD_PROVISIONAL_MSG` slot. All three provisional sites
write there; at example end the reported message is `BDD_FAILURE_MSG`, falling
back to `BDD_PROVISIONAL_MSG` only when no real failure was recorded. Both slots
are reset at example start and in `clear_bdd_state`. A provisional message is
now a fallback, never a replacement.

Files:
- `src/compiler_rust/compiler/src/interpreter_call/bdd.rs`
- `src/compiler_rust/driver/tests/bdd_provisional_message_test.rs` (new)

Evidence — fixture spec (first matcher fails for real, then `expect(0).to_equal(0)`,
`expect("").to_equal("")`, `expect(false).to_be(false)`):

    PRE-FIX  (deployed bin/simple):  expected subject to be truthy, got false
    POST-FIX (rebuilt seed):         expected fetch-3 to equal fetch-2

The complementary direction still holds: a bare `expect(false)` with no matcher
still reports `expected subject to be truthy, got false`.

Test: `cargo test --release --test bdd_provisional_message_test` -> 2 passed,
0 failed. It is fixture-driven — each deliberately-failing spec is written to a
temp dir and run in a child process, and the test asserts on the CAPTURED runner
output, so no spec in the tree is left red.
