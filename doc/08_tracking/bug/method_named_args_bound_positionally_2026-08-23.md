# Named arguments are ignored for METHOD calls (silent sign flip)

**Date:** 2026-08-23
**Engine:** Rust seed tree-walk interpreter (spec/test-runner engine).
**Class:** silent wrong answer.

## Symptom

`test/feature/usage/named_arguments_spec.spl` — `reorders method arguments`
reports `expected -35 to equal 35`.

```
class Math:
    fn subtract(self, minuend, subtrahend):
        return minuend - subtrahend
val m = Math {}
m.subtract(subtrahend=15, minuend=50)   # -> -35, should be 35
```

The operands are bound positionally in WRITTEN order, so the subtraction runs
backwards: `15 - 50` instead of `50 - 15`.

## Discriminator: free functions are fine, methods are not

In the same spec file, on the same engine, in the same run:

```
Named Arguments Reordering
  ✓ reorders three arguments
  ✓ reorders with different calculation
...
  ✗ reorders method arguments
    expected -35 to equal 35
```

Free-function named-argument reordering **works**. Only the method path fails.
This narrows the defect to the receiver-call binding path, and makes the `self`
parameter (which shifts every parameter index by one) the prime suspect.

## Why it is dangerous

A sign flip is a plausible-looking number. Named arguments exist precisely so
that call sites can be written in a readable order; a caller who reorders for
clarity silently changes the computed result. Commutative operations hide it
entirely, so the defect surfaces only intermittently.

## Notes for the fix

A survey of the pure-Simple self-hosted compiler found reordering implemented
for functions (`_EvalOps/call_method_eval.spl:260-300`) and a `self`-offset
variant for methods (`:716-770`), plus fallback method paths that lose
reordering entirely (callable-field fallback at `:704` routes to the
function path, whose parameter list has no `self`; builtin dispatch at
`:631-643` never receives `arg_names`). The HIR interpreter and MIR lowering
bind purely positionally and have no reordering for calls at all. The failing
engine here is the Rust seed, so its own method-call binding is what must be
read first — do not assume the pure-Simple findings transfer.
