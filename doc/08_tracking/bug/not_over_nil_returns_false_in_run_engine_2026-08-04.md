# `not nil` yields `false` in the `run` engine but `true` under the test runner

**Status:** OPEN (engine divergence — unary `not` over `nil` / `T?`).
**Found:** 2026-08-04, while fixing the `Some(nil)` spec assertions.
**Impact:** silent wrong answer. `not` is correct on real bools, so the defect
only surfaces on nil/optional operands — and it disagrees between engines, so a
spec can be green under one runner and red under the other.

## Symptom

Via `bin/simple run` (JIT / seed interpreter path):

```
not nil          -> false      # WRONG — nil is absent, so `not nil` should be true
not true         -> false      # correct
not false        -> true       # correct
e.?              -> nil        # e: i64? = nil
not e.?          -> false      # WRONG — follows from `not nil`
```

Under the **Rust test runner** (`SIMPLE_TEST_RUNNER_RUST=1 … test`), the same
expressions behave correctly. A spec with a deliberate failing control:

```
Passed: 3   Failed: 1     # the 1 is the control `verify(false)`
```

where the 3 passing examples are `not opt.?` for `opt: i64? = nil`, `not opt.?`
for `opt = Some(nil)`, and `not (not Some(42).?)`.

So: **`not <nil>` is `true` under the test runner and `false` under `run`.**

## Repro

```simple
fn main():
    val n = nil
    print "not nil  -> {not n}"      # prints false; should print true
    print "not true -> {not true}"   # false  (correct)
    print "not false -> {not false}" # true   (correct)
```

`./bin/simple run probe.spl`

## Why it matters

`not X.?` is a load-bearing idiom in the spec corpus — it is how "this optional
is absent" is asserted, and it appears throughout `test/03_system/core/edge_case`
(4 sites per file across 50 files). Every one of those is correct only because
the test runner evaluates it correctly. Anything that evaluates the same source
through `run` gets the opposite answer with no diagnostic.

This also nearly produced a bad fix: correcting the 202 `Some(nil)` specs to
`verify(not opt.?)` was first checked with `bin/simple run`, which reported
`false` and made the corrected assertion look wrong. Only running it under the
engine that actually executes the specs showed the fix was right. **Probe with
the engine that runs the code, not with whichever one is convenient.**

## Fix direction

Make `not` agree across engines on non-bool operands. Decide the rule once —
either `not` coerces its operand to a truthiness value (`nil` ⇒ absent ⇒ `not`
is `true`), which is what the test runner does and what the corpus assumes, or
`not` on a non-bool is a type error. Do **not** leave it engine-dependent.

Note that a related coercion is already known to be inconsistent: `1 == true`
holds in the pure-Simple matcher but not under the Rust runner
(`int_payload_compares_equal_to_bool_true_2026-08-04.md`). These are the same
class of defect — unspecified truthiness coercion resolved differently per
engine — and are probably worth one ruling rather than two fixes.

Related: `optional_passed_to_bool_param_is_neither_coerced_nor_rejected_2026-08-04.md`.
