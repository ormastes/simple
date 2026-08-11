# A method call on a parenthesised float literal returns the receiver, not the result

- **Date:** 2026-08-10
- **Status:** OPEN
- **Lanes:** interpreter and JIT (`SIMPLE_JIT_STRICT=1`) — both, identically.
- **Class:** silent wrong-value. The method is not applied at all.

## Symptom

```
fn main():
    print (16.0).sqrt()      # => 16.0     WRONG, expected 4.0
```

Compare the same method through a local, which is correct once
`float_returning_method_in_argument_position_prints_tagged_bits_2026-08-10.md`
is fixed:

```
fn main():
    val b: f64 = 16.0
    print b.sqrt()           # => 4.0      correct
```

## Why this is a *different* defect from the tagged-bits one

The tagged-bits defect printed `577023702256844800`, which is exactly
`bits(4.0) / 8` — the computation was right and only the boxing was lost. Here
the printed value is `16.0`: a well-formed float, correctly boxed, that is the
**receiver**. `sqrt` was never applied. That is a resolution/lowering failure on
the literal-receiver form, not a type-stamp or boxing failure, and fixing the
type stamp does not touch it.

Found while enumerating the method family for the tagged-bits defect. It is
excluded from `scripts/check/check-float-method-argument-position.shs` on
purpose: that check must go green on the tagged-bits fix, and this row would
keep it red for an unrelated reason.

## Reproduction

```
fn main():
    print (16.0).sqrt()
```
```
simple run repro.spl              # 16.0
SIMPLE_JIT_STRICT=1 simple repro.spl   # 16.0
```

## Related

- `doc/08_tracking/bug/float_returning_method_in_argument_position_prints_tagged_bits_2026-08-10.md`
- `doc/08_tracking/bug/float_and_int_math_methods_missing_on_numeric_receivers_2026-08-10.md`
