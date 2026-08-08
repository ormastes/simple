# `array.remove(index)` returns the mutated array, not the removed element

**Status:** OPEN — 2026-07-20 behaviour reconfirmed 2026-08-08. The interpreter
still returns the mutated array. The seed JIT is WORSE and was not previously
recorded: it returns `nil` **and does not mutate the array at all**. See
"Re-triage 2026-08-08" below.
**Date:** 2026-07-20
**Component:** Array `.remove(index)` builtin method (interpreter),
exercised via `test/feature/usage/mutable_by_default_spec.spl`.
**Severity:** Medium — 3 of 24 examples fail; every other mutable-array
operation in the same file (`insert`, `clear`, index-assignment) is
correct.

## Symptom

```
✗ allows remove on default arrays
  expected [1, 3] to equal 2
✗ allows remove first element
  expected [2, 3] to equal 1
✗ allows remove last element
  expected [1, 2] to equal 3
```

```simple
it "allows remove on default arrays":
    var arr = [1, 2, 3]
    val removed = arr.remove(1)
    expect removed == 2
    expect arr.len() == 2
```

`arr.remove(1)` is expected to return the removed element (`2`, the value
at index 1), matching common `Vec::remove`/`list.pop(index)`-style
conventions and the spec's own naming (`val removed = ...`). Instead it
returns the array itself, post-removal (`[1, 3]`) — the mutation itself is
correct (dropping index 1 from `[1, 2, 3]` does yield `[1, 3]`), only the
*return value* is wrong: the method returns the mutated collection instead
of the removed element.

This is NOT a stale-test issue: the spec's expectation (`removed == 2`) is
the conventional, documented-sounding semantics for a `.remove(index)`
method, and no other array method in this same file has this problem —
`.insert(index, value)` (tested without capturing its return value, only
checking the mutated array afterward) and `.clear()` both pass fine. Per
this triage pass's fix guide, a prior pass explicitly declined to touch
this spec because "fixing" it would require weakening/redirecting the
`.remove()` return-value assertion — left correctly RED here as well.

## Minimal repro

```simple
fn main():
    var arr = [1, 2, 3]
    val removed = arr.remove(1)
    print(removed)
    print(arr)

main()
```

Expected: `2` then `[1, 3]`. Actual: `[1, 3]` printed for `removed` too
(i.e. `.remove()`'s return value equals the post-mutation array, not the
removed element).

## Root-cause hypothesis

Not traced into interpreter source (out of scope for a spec-triage pass;
needs a rebuild to verify any fix). Candidate: the `.remove(index)` builtin
method arm returns `self` (or the receiver's post-mutation `Value`) instead
of the element it spliced out — a likely copy-paste/API-shape mismatch
against `.insert()`'s (correctly void/self-returning) arm, or against
`Dict.remove(key)`'s convention if that method returns something
different.

## Notes

- Do NOT attempt a Rust seed source fix here (out of scope for a
  spec-triage pass; needs a rebuild to verify).
- Per the fix guide's explicit hard rule, the spec's assertions
  (`expect removed == 2` etc.) were NOT weakened, narrowed, or redirected
  to match the actual (wrong) return value — all 3 examples are left
  correctly RED.

## Affected specs

- test/feature/usage/mutable_by_default_spec.spl (3 of 24 examples: `allows
  remove on default arrays`, `allows remove first element`, `allows remove
  last element`)

Verified with:
`SIMPLE_RUST_SEED_WARNING=0 timeout 90 bin/release/x86_64-unknown-linux-gnu/simple test test/feature/usage/mutable_by_default_spec.spl --no-session-daemon 2>&1 | sed 's/\x1b\[[0-9;]*m//g'`
→ `Passed: 21, Failed: 3`

## Re-triage 2026-08-08 — still OPEN, and the JIT lane is worse than filed

Binary: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`, which
prints the Rust bootstrap-seed banner. No pure-Simple self-hosted binary is
deployed on this host, so both lanes below are seed lanes.

This report's own minimal repro, run unchanged:

```simple
fn main():
    var arr = [1, 2, 3]
    val removed = arr.remove(1)
    print "removed={removed}"
    print "arr={arr}"
main()
```

| lane | `removed` | `arr` after |
|------|-----------|-------------|
| interpreter (`SIMPLE_EXECUTION_MODE=interpreter bin/simple run`) | `[1, 3]` | `[1, 3]` |
| seed JIT (`bin/simple run`, the default) | `nil` | `[1, 2, 3]` |

**Interpreter:** exactly as filed — the return value is the mutated array
instead of the removed element `2`, while the mutation itself is correct. No
change since 2026-07-20.

**Seed JIT — new, not in the original report:** `.remove(index)` returns `nil`
*and the array is not mutated at all*. So on the engine ordinary programs run
on, `arr.remove(1)` is a complete no-op that also discards the element it was
supposed to return. That is strictly worse than the interpreter behaviour and
is a second, independent defect in the same builtin.

Note the discovery asymmetry: `bin/simple test` runs the interpreter, so the
three RED examples in `mutable_by_default_spec.spl` document only the return
value bug. Nothing in the spec corpus can observe the JIT no-op, because the
suite cannot reach that engine — the structural gap catalogued in
`run_vs_test_harness_divergence_2026-07-28.md`.

**Still not fixed here, and the spec stays RED.** Per this repo's testing rule
a correct spec that fails is a legitimate artifact; `expect removed == 2` is the
right assertion and must not be weakened. Closing this needs a decision on the
contract (return the removed element, as the spec and the `Vec::remove` /
`list.pop(index)` convention say) applied to BOTH lanes, plus the JIT mutation
fix which is a separate, larger problem.
