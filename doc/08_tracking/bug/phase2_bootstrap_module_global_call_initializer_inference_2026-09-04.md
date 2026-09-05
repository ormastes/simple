# Phase 2 bootstrap cannot infer a module-global call initializer

## Status

Open compiler inference defect; the focused bootstrap admission probe uses an
explicit type annotation so cross-module global identity remains testable.

## Reproduction

With `SIMPLE_NO_STUB_FALLBACK=1`, the admitted-candidate Phase 2 macOS arm64
compiler rejects this otherwise typed initializer before MIR linking:

```simple
fn initialize_value() -> i64:
    42

val initialized_value = initialize_value()
```

The failure is `bootstrap MIR lowering: cannot derive module static type from
unresolved initializer; add an explicit annotation`. The function return type
is already explicit, so bootstrap lowering is failing to propagate it into the
module-global declaration.

## Required fix

Bootstrap MIR type resolution must use the resolved callee return type for a
module-global call initializer. Admission requires the unannotated form to
build under strict no-stub mode and retain the existing cross-module exit-42
identity behavior. Until then, the canonical module-global identity probe uses
`val initialized_value: i64 = initialize_value()`; this does not change its
runtime identity assertion.
