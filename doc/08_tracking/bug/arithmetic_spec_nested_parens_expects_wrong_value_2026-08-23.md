# SPEC BUG (not a compiler bug): nested-parenthesis expectation is arithmetically wrong

**Date:** 2026-08-23
**Verdict:** the compiler is CORRECT. `test/feature/usage/arithmetic_spec.spl`
is wrong and should be corrected. No source change was made.

## The claim

The sweep report listed `handles deeply nested parentheses` — `expected 8 to
equal 6` — as a **wrong arithmetic result**, and called it "the most serious
defect in this list". It is not a defect at all.

## The spec

`test/feature/usage/arithmetic_spec.spl:298`

```
expect (((10 + 5) * 2) - 5) / 3 == 6
```

## The arithmetic

```
10 + 5        = 15
15 * 2        = 30
30 - 5        = 25
25 / 3        = 8     (integer division; 8 remainder 1)
```

**8 is the correct answer.** The spec asserts `== 6`, which no evaluation
order produces: the parentheses are fully explicit, so there is no precedence
or associativity freedom left to exploit. `6` would require `25 / 3` to be
something other than 8, or a different numerator — most likely the expectation
was written against `((10 + 5) * 2 - 6) / 4` or similar and never re-checked
after the expression was edited.

Confirmed independently of the spec harness (`bin/simple run`):

```
print("parens: {(((10 + 5) * 2) - 5) / 3}")
-> parens: 8
```

## Action

Fix the expectation to `== 8`, or change the expression to one that genuinely
yields 6. Leave the compiler alone. This row should be struck from the sweep
report's defect table so it stops drawing effort away from the real
silent-wrong-answer defects beside it.
