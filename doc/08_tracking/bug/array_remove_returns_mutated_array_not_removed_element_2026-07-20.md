# `array.remove(index)` returns the mutated array, not the removed element

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
