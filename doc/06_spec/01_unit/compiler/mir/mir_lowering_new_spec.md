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
diagnosing Stage 2 bootstrap lowering. The latest scenario pins contextual
bootstrap diagnostics: missing HIR modules are reported at the MIR driver
boundary, HIR/MIR probes include module/path/count context, and Rust field
access diagnostics share an opt-in cached debug gate.

Latest focused evidence:

```text
BLOCKED test/01_unit/compiler/mir/mir_lowering_new_spec.spl
Current deployed pure-Simple runtime exits 139 while checking specs in this
worktree. Source assertions for the added diagnostic scenario pass, and
`cargo check -p simple-compiler` passes for the Rust seed changes.
```
