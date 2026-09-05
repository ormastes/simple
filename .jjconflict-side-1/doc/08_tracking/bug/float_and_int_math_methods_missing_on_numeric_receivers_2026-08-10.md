# Most math methods do not exist on numeric receivers (`f64.sin`, `i64.abs`, ...)

- **Date:** 2026-08-10
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
- **Lanes:** interpreter and JIT (`SIMPLE_JIT_STRICT=1`) — both, identically.
- **Class:** missing dispatch. Loud, not silent — the runtime refuses rather
  than substituting a placeholder, which is the correct behaviour.

## Fix (2026-08-11)

Two independent points, both required (fixing only the first changes nothing
observable):

1. **`hir/lower/expr/mod.rs::builtin_numeric_method_result_type`** — extended
   the result-type whitelist (previously `sqrt`/`abs`/`floor`/`ceil`/`round`
   only) to also stamp `trunc`/`sin`/`cos`/`tan`/`asin`/`acos`/`atan`/`sinh`/
   `cosh`/`tanh`/`exp`/`ln`/`log2`/`log10`/`cbrt`/`pow`/`powf`/`max`/`min` on a
   float receiver, and `abs` on all integer receiver widths.
2. **`codegen/instr/closures_structs.rs::try_compile_builtin_method_call`** —
   this, not `codegen/instr/methods.rs::compile_builtin_method`, is the actual
   dispatch site for method calls lowered as `MirInst::MethodCallStatic` (both
   `DispatchMode::Dynamic` and `DispatchMode::Static` funnel into
   `MethodCallStatic`; `MirInst::BuiltinMethod` — what `methods.rs` handles —
   is never emitted for a real method-call HIR node). Added: `trunc` and
   integer `abs` as native Cranelift instructions (`trunc`, `iabs`), and the
   remaining methods routed to the pre-existing `rt_math_*` runtime symbols
   (already used by the free-function forms via
   `lower_libm_math`) through `call_runtime_1`/`call_runtime_2`.
   `codegen/common_backend.rs::referenced_call_names` also needed a
   `MirInst::MethodCallStatic` arm to pre-declare the `rt_math_*` family
   (mirroring the pre-existing `BuiltinMethod` arm) — without it codegen
   panicked with `missing runtime fn 'rt_math_sin'` the first time an uncommon
   method was hit, because the runtime-import pre-pass never saw the name (it
   is chosen inside codegen, not named in the MIR).

Verified red-then-green on a from-source seed build
(`/mnt/data/cargo-target/release/simple`, `simple-driver` package) — all ten
symptom rows plus the five already-working controls, both the default
(JIT-first) and `SIMPLE_JIT_STRICT=1` lanes. Fenced by
`scripts/check/check-numeric-method-family-dispatch.shs` (28 assertions, both
lanes green).

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
