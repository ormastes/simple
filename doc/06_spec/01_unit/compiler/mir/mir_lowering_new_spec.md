# MIR Lowering New Spec

Source: `test/01_unit/compiler/mir/mir_lowering_new_spec.spl`

## MIR/HIR bootstrap lowering contracts

Checks that the split MIR lowering shape remains wired, that named bootstrap
calls stay name-based and keep bootstrap return types instead of becoming
unknown/numeric `i64` calls, and that the
bootstrap HIR unresolved-name path keeps `get_args`, `eprint`, and bootstrap
entry helper names as named builtins with minimal function signatures only
under bootstrap mode.

It also checks the current frontend/flat-bridge trace strings used while
diagnosing Stage 2 bootstrap lowering.

Latest focused evidence:

```text
PASS test/01_unit/compiler/mir/mir_lowering_new_spec.spl
5 examples, 0 failures
```
