# Pure-Simple ERR-01 misses `as` on an untyped local holding an optional call result

Date: 2026-11-13
Status: OPEN
Severity: P3
Found by: lane p3-ifval-20261113 (if_val_binding_from_generic_optional_stays_optional_err01_2026-11-13)

## Observed

The self-hosted HIR lowerer's `[E-OPT-CAST-001]` check
(`src/compiler/20.hir/hir_lowering/_Expressions/expression_core.spl`, Cast arm)
reads the operand's HIR type or the DECLARED symbol type of a named local /
called function. A local declared without an annotation from an optional
call result has no declared type, so the cast is not rejected:

```simple
fn pick<T>(v: T, ok: bool) -> T?:
    if ok:
        v
    else:
        nil

fn f() -> i64:
    val m = pick(41, true)
    m as i64        # pure-Simple: 0 errors; seed: ERR-01 (correct)
```

Measured 2026-11-13 through `optional_as_cast_rejected_spec.spl`'s
`lowering_errors` helper: `pick(41, true) as i64` -> 1 error (correct),
`val m = pick(41, true); m as i64` -> 0 errors (should be 1).

## Expectation

Parity with the seed: an unannotated `val` initialised from a call whose
declared return type is `T?` carries that optional type into the cast check.
