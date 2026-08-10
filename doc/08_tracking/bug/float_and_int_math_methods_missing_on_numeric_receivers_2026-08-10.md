# Most math methods do not exist on numeric receivers (`f64.sin`, `i64.abs`, ...)

- **Date:** 2026-08-10
- **Status:** OPEN
- **Lanes:** interpreter and JIT (`SIMPLE_JIT_STRICT=1`) — both, identically.
- **Class:** missing dispatch. Loud, not silent — the runtime refuses rather
  than substituting a placeholder, which is the correct behaviour.

## Symptom

Only five math methods resolve on an `f64` receiver. Measured on a binary built
from `bb43fac0cf5` (2026-08-10), one expression per row, both lanes agreeing:

| expression | result |
|---|---|
| `b.sqrt()` | resolves |
| `b.abs()` | resolves |
| `b.floor()` | resolves |
| `b.ceil()` | resolves |
| `b.round()` | resolves |
| `b.trunc()` | `Runtime error: Function 'f64.trunc' not found` |
| `b.sin()` | `Runtime error: Function 'f64.sin' not found` |
| `b.pow(2.0)` | `Runtime error: Function 'f64.pow' not found` |
| `b.max(7.0)` | `Runtime error: Function 'f64.max' not found` |
| `i.abs()` (i64) | `Runtime error: Function 'i64.abs' not found` |

The five that resolve are exactly the inline set in
`src/compiler_rust/compiler/src/codegen/instr/methods.rs:199`
(`matches!(method, "sqrt" | "abs" | "floor" | "ceil" | "round")` ->
`builder.ins().sqrt / fabs / floor / ceil / nearest`). Everything else in
`src/compiler_rust/compiler/src/method_registry/builtins.rs` — `sin`, `cos`,
`tan`, `exp`, `ln`, `pow`, `trunc`, `is_nan`, `is_infinite` — is declared in
the registry but has no reachable lowering, so the registry over-promises.

The free-function forms of several of these DO work (`sqrt(16.0)`,
`pow(2.0, 3.0)`, `min`/`max`/`abs`, all fenced by
`scripts/check/check-numeric-builtin-result-type.shs`), so this is specifically
the method-receiver spelling.

## Why filed separately

Found while enumerating the method family for
`float_returning_method_in_argument_position_prints_tagged_bits_2026-08-10.md`.
That defect is a *wrong value* on methods that DO resolve; this is *no
dispatch* for methods that do not. Fixing the type stamp cannot fix a method
that has no lowering, and stamping a result type on one of these would be
actively wrong — it would tell MIR to unbox a value the callee never produced.
That is why the type-stamp fix is restricted to the five-method inline set.

## Reproduction

```
fn main():
    val b: f64 = 16.0
    print b.sin()
```
```
simple run repro.spl                    # Runtime error: Function 'f64.sin' not found
SIMPLE_JIT_STRICT=1 simple repro.spl    # same
```

## Related

- `doc/08_tracking/bug/float_returning_method_in_argument_position_prints_tagged_bits_2026-08-10.md`
- `doc/08_tracking/bug/float_literal_receiver_method_call_returns_receiver_2026-08-10.md`
- `doc/08_tracking/bug/numeric_builtins_hardcode_i64_result_type_2026-08-10.md` (free-function forms)
