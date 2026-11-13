# Interpreter `while val` binds the whole `Option::Some(x)`, not the payload

Date: 2026-11-13
Status: OPEN
Severity: P3
Found by: lane p3-ifval-20261113 (if_val_binding_from_generic_optional_stays_optional_err01_2026-11-13)

## Observed

On the seed interpreter lane (`SIMPLE_EXECUTION_MODE=interpret`), `while val`
binds the optional itself instead of its payload, for a concrete `i64?` as
well as a generic `T?`:

```simple
fn pk(v: i64, ok: bool) -> i64?:
    if ok:
        v
    else:
        nil
fn wconc() -> i64:
    var i = 0
    var total = 0
    while val m = pk(i, i < 3):
        total = total + m * 10      # interpret: "type mismatch: cannot convert enum to int"
        i = i + 1
    total
```

`print "m={m}"` inside the loop prints `m=Option::Some(0)`. Same failure on
seed-fix 2026-11-13 (before) and on the seed carrying the if-val fix (after);
`if val` and `elif val` over the same subjects bind the payload correctly on
the interpreter, and the JIT lane computes `30`.

## Expectation

`while val x = <T?>` binds `x: T` on the interpreter exactly as `if val` does.

## Pinned by

`test/01_unit/language/if_val_generic_optional_cast_spec.spl` leaves `while val`
out of its interpreter leg for this reason (its JIT leg covers `while val`).
