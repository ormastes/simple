# Decorators are parsed but never applied (silent wrong answer)

**Date:** 2026-08-23
**Engine:** Rust seed tree-walk interpreter (spec/test-runner engine).
**Class:** silent wrong answer — the decorated function runs, undecorated.

## Symptom

`test/feature/usage/decorators_spec.spl`, 5 of 10 examples RED. Measured on
the seed carrying this lane's range/SIMD/named-arg fixes, so this is a
distinct root cause from all three:

```
✗ applies basic decorator            expected 6 to equal 12
✗ applies decorator with arguments   expected 11 to equal 33
✗ stacks multiple decorators         expected 5 to equal 20
✗ uses decorator without parentheses expected 16 to equal 21
✗ binds value with as clause
Results: 10 total, 5 passed, 5 failed
```

## The pattern across all four numeric cases

Every failing value is the **undecorated** result:

| case | got | expected | relationship |
|---|---|---|---|
| basic | 6 | 12 | expected = got x 2 (the decorator doubles) |
| with arguments | 11 | 33 | expected = got x 3 |
| stacked | 5 | 20 | expected = got x 4 (two decorators) |
| no parentheses | 16 | 21 | decorator's contribution absent |

The bodies compute correctly; the wrapper is simply never installed. This is
not a wrong-argument or wrong-slot defect — it is the decorator application
step being skipped entirely, so the raw function is what the name resolves to.

## Why it is dangerous

Decorators are used for memoisation, validation, access control, retry, and
logging. A decorator that silently does not apply removes an invariant the
call site believes is enforced, while the program keeps returning a
plausible value. Nothing errors.

## Why this record and not a fix

Filed rather than fixed to stay inside the minimal-semantics-preserving
mandate: the four cases span decorator *parsing* (bare vs. parenthesised vs.
argument-carrying vs. stacked), so the defect is likely at the point where a
decorator list is attached to a function definition and then consulted at
call time — a larger change than the three landed in this range. The five
failing examples above are the reproduce tests and are RED today.

## Next step

Find where decorator attributes are stored on `FunctionDef` in the seed and
whether any call path consults them. If they are stored but never read, that
absence is the whole bug.
