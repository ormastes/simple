# Spec runner: a falsy `expect(x)` subject overwrites an earlier real matcher failure message

- Date: 2026-08-21
- Status: OPEN (seed change; `src/compiler_rust` is owned by a live lane — filed, not fixed)
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
